#!/usr/bin/env python3
"""Aggregate run/check metadata into manifests, verify the result is all-green, and
(optionally) build a self-contained publication tree.

Two uses:
  * Verify gate (default): join each instance's run.json + check.json, and write per-dimension manifests
    Does not modify the working tree.
  * Packager (--build-publish-dir DIR): prepare everything for publication.

Dimensions come in two tiers. A *verified* dimension has check.json records and can
reach status "verified_unsat". A *pending* dimension has run.json but no check.json at
all (proofs produced, drat-trim not yet run): its instances are "solved_unverified",
its manifest carries verification: "pending", and it never counts as verified-green.
"""

from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import sys
import tempfile

SCHEMA_VERSION = "1.0"


def parse_args():
    p = argparse.ArgumentParser(description="Build manifests, verify all-green, optionally package.")
    p.add_argument("--instance-root", type=Path, default=Path("instances"))
    p.add_argument("--result-root", type=Path, default=Path("results"))
    p.add_argument("--out-dir", type=Path, default=Path("manifests"),
                   help="where manifests are written in verify mode (default: manifests/)")
    p.add_argument("--max-d", type=int, default=None,
                   help="include only dimensions with d <= MAX_D (e.g. 9 to exclude d10up)")
    p.add_argument("--check-files", action="store_true",
                   help="also re-hash the CNF/DRAT on disk against the recorded hashes (slow)")
    p.add_argument("--build-publish-dir", type=Path, default=None,
                   help="build the publication tree here (implies a green requirement)")
    p.add_argument("--code-dir", type=Path, default=Path("."),
                   help="where to find scripts/README/LICENSE to copy into the publish tree")
    p.add_argument("--release-version", default=None,
                   help="version string recorded in the manifests (e.g. '1')")
    p.add_argument("--allow-pending", action="append", default=[], metavar="FOLDER",
                   help="folder permitted to be solver-only (no check.json), e.g. d10up; "
                        "repeatable. A folder with no check.json that is not listed aborts.")
    p.add_argument("--allow-empty-verified", action="store_true",
                   help="permit a release with zero verified dimensions (proofs-only). "
                        "Off by default: such a release would attest nothing.")
    return p.parse_args()


def sha256_file(path):
    with path.open("rb") as f:
        if sys.version_info >= (3, 11):
            return hashlib.file_digest(f, "sha256").hexdigest()
        h = hashlib.sha256()
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
        return h.hexdigest()


def parse_folder(name):
    """'d9' -> (9, 'general'); 'd10up' -> (10, 'up'). Returns None if not a d-folder."""
    if not name.startswith("d"):
        return None
    body = name[1:]
    family = "general"
    if body.endswith("up"):
        family, body = "up", body[:-2]
    if not body.isdigit():
        return None
    return int(body), family


def load_json(path):
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError as e:
        raise Abort(f"corrupted JSON in {path}: {e}")


class Abort(Exception):
    """Fatal configuration/uniformity problem; stop before producing anything."""


def build_instance_record(stem, d, family, run, check, args, pending):
    """Join one instance into a manifest record. In a pending dimension there is no
    check side: the record is solver-only with status 'solved_unverified'."""
    rec = {
        "instance": f"{stem}.cnf",
        "d": d,
        "cnf_path": f"cnfs/d{d}{'up' if family == 'up' else ''}/{stem}.cnf",
        "drat_path": f"proofs/d{d}{'up' if family == 'up' else ''}/{stem}.drat",
    }
    folder = f"d{d}{'up' if family == 'up' else ''}"
    rec["run_json_path"] = f"metadata/{folder}/{stem}.run.json"
    if pending:
        if run is None:
            rec["status"] = "incomplete"
            rec["missing"] = ["run"]
            return rec
        for k in ("tau", "w", "tight", "up_monotone"):
            rec[k] = run.get(k)
        rec["cnf_sha256"] = run.get("cnf_sha256")
        rec["drat_sha256"] = run.get("drat_sha256")
        # both the CNF and the proof are published artifacts here: require them on disk
        cnf_disk = args.instance_root / folder / f"{stem}.cnf"
        drat_disk = args.result_root / folder / f"{stem}.drat"
        cnf_recorded = bool(run.get("cnf_sha256"))
        proof_recorded = bool(run.get("drat_sha256")) and (run.get("drat_size_bytes") or 0) > 0
        cnf_ok = cnf_disk.exists()
        proof_ok = (drat_disk.exists() and drat_disk.stat().st_size > 0
                    and drat_disk.stat().st_size == run.get("drat_size_bytes"))
        if args.check_files:
            cnf_ok = cnf_ok and sha256_file(cnf_disk) == run.get("cnf_sha256")
            proof_ok = proof_ok and sha256_file(drat_disk) == run.get("drat_sha256")
        solver_clean = (run.get("result") == "unsat" and run.get("result_consistent") is True
                        and cnf_recorded and proof_recorded and cnf_ok and proof_ok)
        rec["solver"] = {
            "result": run.get("result"), "result_consistent": run.get("result_consistent"),
            "returncode": run.get("returncode"), "wall_seconds": run.get("wall_seconds"),
            "cnf_file_ok": cnf_ok, "proof_file_ok": proof_ok,
        }
        rec["status"] = "solved_unverified" if solver_clean else "bad"
        return rec

    rec["check_json_path"] = f"metadata/{folder}/{stem}.check.json"

    if run is None or check is None:
        rec["status"] = "incomplete"
        rec["missing"] = [s for s, v in (("run", run), ("check", check)) if v is None]
        return rec

    # identity comes from the run record (single source)
    for k in ("tau", "w", "tight", "up_monotone"):
        rec[k] = run.get(k)
    rec["cnf_sha256"] = run.get("cnf_sha256")
    rec["drat_sha256"] = run.get("drat_sha256")

    solver_clean = run.get("result") == "unsat" and run.get("result_consistent") is True
    checker_clean = check.get("verified") is True and check.get("verified_consistent") is True
    drat_match = check.get("drat_sha256") == run.get("drat_sha256")
    cnf_match = check.get("cnf_sha256") == run.get("cnf_sha256")

    cross = {"drat_sha256_match": drat_match, "cnf_sha256_match": cnf_match}
    green = solver_clean and checker_clean and drat_match and cnf_match

    if args.check_files:
        cnf_disk = args.instance_root / folder / f"{stem}.cnf"
        drat_disk = args.result_root / folder / f"{stem}.drat"
        file_cnf = cnf_disk.exists() and sha256_file(cnf_disk) == run.get("cnf_sha256")
        file_drat = drat_disk.exists() and sha256_file(drat_disk) == run.get("drat_sha256")
        cross["cnf_file_matches_recorded"] = file_cnf
        cross["drat_file_matches_recorded"] = file_drat
        green = green and file_cnf and file_drat

    rec["solver"] = {
        "result": run.get("result"), "result_consistent": run.get("result_consistent"),
        "returncode": run.get("returncode"), "wall_seconds": run.get("wall_seconds"),
    }
    rec["checker"] = {
        "verified": check.get("verified"), "verified_consistent": check.get("verified_consistent"),
        "returncode": check.get("returncode"), "wall_seconds": check.get("wall_seconds"),
    }
    rec["cross_check"] = cross
    rec["status"] = "verified_unsat" if green else "bad"
    return rec


def build_folder_manifest(folder, d, family, args):
    idir = args.instance_root / folder
    rdir = args.result_root / folder
    cnfs = sorted(idir.glob("*.cnf"))
    if not cnfs:
        return None  # empty folder (e.g. no admissible weight function): not part of the release
    # A folder with no check.json at all is a pending (solver-only) dimension; this must be
    # declared with --allow-pending so a forgotten verifier run can't masquerade as "pending".
    pending = not any(rdir.glob("*.check.json"))
    if pending and folder not in set(args.allow_pending):
        raise Abort(f"{folder}: no check.json files found. If this dimension is intentionally "
                    f"solver-only, pass --allow-pending {folder}; otherwise run the verifier.")
    instances = []
    for cnf in cnfs:
        stem = cnf.stem
        run_p = rdir / f"{stem}.run.json"
        check_p = rdir / f"{stem}.check.json"
        run = load_json(run_p) if run_p.exists() else None
        check = load_json(check_p) if check_p.exists() else None

        # uniformity guard: every record must carry a single cnf_sha256 matching the published CNF
        for label, rec in (("run", run), ("check", check)):
            if rec is not None and "cnf_sha256_published" in rec:
                raise Abort(f"{folder}/{stem}: {label} record carries an unexpected "
                            f"cnf_sha256_published field; this release expects a single cnf_sha256.")
        # instance-name sanity: the record's own instance field must match its filename stem
        expected = f"{stem}.cnf"
        for label, rec in (("run", run), ("check", check)):
            if rec is not None and rec.get("instance") not in (None, expected):
                raise Abort(f"{folder}/{stem}: {label} instance field is "
                            f"{rec.get('instance')!r}, expected {expected!r} (stale/cross-copied?)")
        # identity/family sanity
        if run is not None and run.get("up_monotone") is not None:
            if bool(run.get("up_monotone")) != (family == "up"):
                raise Abort(f"{folder}/{stem}: up_monotone={run.get('up_monotone')} "
                            f"disagrees with folder family '{family}'")
        instances.append(build_instance_record(stem, d, family, run, check, args, pending))

    n = len(instances)
    bad = sum(1 for r in instances if r["status"] == "bad")
    inc = sum(1 for r in instances if r["status"] == "incomplete")
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "version": args.release_version,
        "folder": folder,
        "family": family,
        "d": d,
        "instances": instances,
    }
    if pending:
        su = sum(1 for r in instances if r["status"] == "solved_unverified")
        manifest["verification"] = "pending"
        manifest["counts"] = {"instances": n, "solved_unverified": su, "bad": bad,
                              "incomplete": inc, "all_solved": n > 0 and su == n}
    else:
        vu = sum(1 for r in instances if r["status"] == "verified_unsat")
        manifest["verification"] = "verified"
        manifest["counts"] = {"instances": n, "verified_unsat": vu, "bad": bad,
                              "incomplete": inc, "all_green": n > 0 and vu == n}
    return manifest


def write_manifests(folders, args, out_dir):
    out_dir.mkdir(parents=True, exist_ok=True)
    verified, pending = {}, {}
    for folder, d, family in folders:
        m = build_folder_manifest(folder, d, family, args)
        if m is None:
            print(f"  {folder}: (empty, skipped)")
            continue
        (out_dir / f"manifest_{folder}.json").write_text(json.dumps(m, indent=2) + "\n")
        c = m["counts"]
        if m["verification"] == "pending":
            pending[folder] = c
            ok = c["all_solved"]
            print(f"  {folder}: {c['solved_unverified']}/{c['instances']} solved "
                  f"(bad {c['bad']}, incomplete {c['incomplete']}) -- PENDING VERIFICATION"
                  f"{'' if ok else ' [NOT CLEAN]'}")
        else:
            verified[folder] = c
            flag = "OK" if c["all_green"] else "NOT GREEN"
            print(f"  {folder}: {c['verified_unsat']}/{c['instances']} verified-unsat "
                  f"(bad {c['bad']}, incomplete {c['incomplete']}) -- {flag}")

    all_verified_green = all(v["all_green"] for v in verified.values())  # vacuously True if empty
    all_pending_solved = all(v["all_solved"] for v in pending.values())  # True if no pending
    if not verified and not args.allow_empty_verified:
        raise Abort("no verified dimensions in scope: this release would attest nothing. "
                    "Pass --allow-empty-verified for a deliberate proofs-only release.")
    top = {
        "schema_version": SCHEMA_VERSION,
        "version": args.release_version,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "verified_dimensions": {
            "dimensions": [f for f in verified],
            "counts_by_folder": verified,
            "all_verified_green": all_verified_green,
        },
        "pending_dimensions": {
            "dimensions": [f for f in pending],
            "counts_by_folder": pending,
            "all_solved": all_pending_solved,
            "note": "proofs produced but not yet independently checked with drat-trim",
        },
    }
    (out_dir / "manifest_all.json").write_text(json.dumps(top, indent=2) + "\n")
    # The release is OK when the verified tier is fully green and any pending tier is cleanly solved.
    ok = all_verified_green and all_pending_solved
    summary = {"verified": verified, "pending": pending,
               "all_verified_green": all_verified_green, "all_pending_solved": all_pending_solved}
    return ok, summary


def discover_folders(args):
    if not args.instance_root.is_dir():
        raise Abort(f"missing instance root: {args.instance_root}")
    folders = []
    for p in sorted(args.instance_root.iterdir()):
        if not p.is_dir():
            continue
        parsed = parse_folder(p.name)
        if parsed is None:
            continue
        d, family = parsed
        if args.max_d is not None and d > args.max_d:
            print(f"  (excluding {p.name}: d={d} > max-d {args.max_d})")
            continue
        folders.append((p.name, d, family))
    folders.sort(key=lambda x: (x[1], x[2]))  # numeric by d, then family (d5 before d10up)
    return folders


CODE_FILES = ["README.md", "LICENSE", "requirements.txt", "mfmc.py", "mfmc_runner.py",
              "mfmc_verifier.py", "publish_artifacts.py"]


def build_publish_tree(folders, args, pub):
    if pub.exists() and any(pub.iterdir()):
        raise Abort(f"{pub} exists and is not empty; remove it or choose a fresh directory.")
    pub.mkdir(parents=True, exist_ok=True)
    suffix = lambda fam: "up" if fam == "up" else ""

    def _dst(path):
        path.parent.mkdir(parents=True, exist_ok=True)
        return path

    # copy raw data under published names, driven by the current CNF stems so the
    # published tree mirrors the manifest exactly (no stale leftovers get published)
    for folder, d, family in folders:
        s = suffix(family)
        cnf_list = sorted((args.instance_root / folder).glob("*.cnf"))
        if not cnf_list:
            continue
        rdir = args.result_root / folder
        for cnf in cnf_list:
            stem = cnf.stem
            shutil.copy2(cnf, _dst(pub / "cnfs" / f"d{d}{s}" / cnf.name))
            drat = rdir / f"{stem}.drat"
            if drat.exists():
                shutil.copy2(drat, _dst(pub / "proofs" / f"d{d}{s}" / drat.name))
            for ext in (".run.json", ".check.json"):
                meta = rdir / f"{stem}{ext}"
                if meta.exists():
                    shutil.copy2(meta, _dst(pub / "metadata" / f"d{d}{s}" / meta.name))

    # manifests with published paths
    write_manifests(folders, args, pub / "manifests")

    # code / docs, if present
    for name in CODE_FILES:
        src = args.code_dir / name
        if src.exists():
            shutil.copy2(src, pub / name)

    # SHA256SUMS over every raw file in the tree (pre-compression)
    lines = []
    for f in sorted(pub.rglob("*")):
        if f.is_file() and f.name not in ("SHA256SUMS", "SHA256SUMS.archives", "COMPRESS.sh"):
            lines.append(f"{sha256_file(f)}  {f.relative_to(pub).as_posix()}")
    (pub / "SHA256SUMS").write_text("\n".join(lines) + "\n")

    # COMPRESS.sh: per-dimension proof archives + cnfs + metadata, then append archive hashes
    present = [(d, suffix(family)) for folder, d, family in folders
               if sorted((args.instance_root / folder).glob("*.cnf"))]
    archives = [f"proofs_d{d}{s}.tar.zst" for d, s in present] + ["cnfs.tar.zst", "metadata-jsons.tar.zst"]
    # Deterministic tar so re-runs reproduce byte-identical archives. NOTE: the trust chain is the
    # raw-file hashes in SHA256SUMS; archive hashes are only a download-integrity convenience.
    tar = ("tar --sort=name --mtime='UTC 2026-01-01' --owner=0 --group=0 --numeric-owner "
           "-I 'zstd -19 -T0' -cf")
    cmds = ["#!/usr/bin/env bash",
            "# Build compressed archives for Zenodo, then (idempotently) record their hashes.",
            "set -euo pipefail", 'cd "$(dirname "$0")"', "",
            "rm -f " + " ".join(archives) + " SHA256SUMS.archives", ""]
    for d, s in present:
        cmds.append(f"{tar} proofs_d{d}{s}.tar.zst proofs/d{d}{s}")
    cmds.append(f"{tar} cnfs.tar.zst cnfs")
    cmds.append(f"{tar} metadata-jsons.tar.zst metadata")
    cmds.append("")
    cmds.append(f"sha256sum {' '.join(archives)} > SHA256SUMS.archives")
    cmds.append('echo "archives built; raw-file hashes in SHA256SUMS, archive hashes in SHA256SUMS.archives"')
    (pub / "COMPRESS.sh").write_text("\n".join(cmds) + "\n")
    (pub / "COMPRESS.sh").chmod(0o755)


def main():
    args = parse_args()
    try:
        folders = discover_folders(args)
        if not folders:
            print("ERROR: no dimension folders in scope.", file=sys.stderr)
            sys.exit(2)

        building = args.build_publish_dir is not None
        if building:
            args.check_files = True  # never package without confirming files match recorded hashes
        print(f"{'BUILD' if building else 'VERIFY'}: dimensions "
              f"{', '.join(f for f, _, _ in folders)}\n")

        if building:
            # Preflight verify into a throwaway temp dir, so packaging never mutates the
            # working-tree manifests/. build_publish_tree writes the real manifests into publish/.
            with tempfile.TemporaryDirectory() as tmp:
                ok, summary = write_manifests(folders, args, Path(tmp))
            if not ok:
                print("\nNot publishable (verified tier not green, or a pending solve is not "
                      "clean) -- refusing to build publish tree.", file=sys.stderr)
                sys.exit(1)
            build_publish_tree(folders, args, args.build_publish_dir)
            nv = sum(c["verified_unsat"] for c in summary["verified"].values())
            ns = sum(c["solved_unverified"] for c in summary["pending"].values())
            print(f"\nBuilt publication tree at {args.build_publish_dir}: "
                  f"{nv} verified-unsat" + (f", {ns} solved-but-pending-verification" if ns else "") + ".")
            if summary["pending"]:
                print("Pending dimensions are published as proofs-only (verification: pending); "
                      "the README must say so.")
            print(f"Next: run {args.build_publish_dir}/COMPRESS.sh to make the Zenodo archives.")
        else:
            ok, summary = write_manifests(folders, args, args.out_dir)
            print(f"\nManifests in {args.out_dir}/. "
                  f"verified tier green: {summary['all_verified_green']}; "
                  f"pending tier clean: {summary['all_pending_solved']}.")
            if not ok:
                print("NOT OK.", file=sys.stderr)
                sys.exit(1)
            if summary["pending"]:
                print("OK (verified tier green; pending dimensions solved but NOT yet verified).")
            else:
                print("ALL GREEN.")
    except Abort as e:
        print(f"ABORT: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
