#!/usr/bin/env python3
"""Verify each DRAT proof with drat-trim; save checker logs and per-instance metadata.

Check-side mirror of the cadical runner. For each instances/<d>/<stem>.cnf paired
with results/<d>/<stem>.drat, it runs drat-trim and writes results/<d>/<stem>.check.json
next to the raw .check.out/.check.err. It never overwrites results: an instance is
skipped only if its .check.json records a verified-clean result for the same CNF and DRAT
(re-hashed on disk); existing-but-not-clean outputs are flagged ("blocked"). A run
that checks zero proofs exits with an error rather than reporting success.
"""

from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time

SCHEMA_VERSION = "1.0"


def positive_int(s):
    x = int(s)
    if x < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return x


def parse_args():
    p = argparse.ArgumentParser(
        description="Verify DRAT proofs with drat-trim; save logs and metadata.")
    p.add_argument("--kind", choices=["general", "up", "all"], required=True,
                   help="which instance family to check (general = non-up-monotone)")
    p.add_argument("--drat-trim", default="drat-trim", help="path to the drat-trim binary")
    p.add_argument("--time-limit", type=positive_int, default=1000000000,
                   help="drat-trim -t value in seconds (default effectively unlimited)")
    p.add_argument("--jobs", type=positive_int, default=4, help="number of parallel checks")
    p.add_argument("--instance-root", type=Path, default=Path("instances"))
    p.add_argument("--result-root", type=Path, default=Path("results"))
    return p.parse_args()


def sha256_file(path):
    with path.open("rb") as f:
        if sys.version_info >= (3, 11):
            return hashlib.file_digest(f, "sha256").hexdigest()
        h = hashlib.sha256()
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
        return h.hexdigest()


def selected_dir(d_dir, kind):
    if kind == "all":
        return True
    if kind == "up":
        return d_dir.name.endswith("up")
    if kind == "general":
        return not d_dir.name.endswith("up")
    raise ValueError(f"Unknown kind: {kind}")


def drat_available(drat_trim):
    """Confirm the checker is executable; drat-trim has no --version, so just probe."""
    try:
        subprocess.run([drat_trim], stdin=subprocess.DEVNULL,
                       capture_output=True, text=True, errors="replace",
                       check=False, timeout=10)
    except (OSError, subprocess.TimeoutExpired) as e:
        print(f"FATAL: Could not execute '{drat_trim}': {e}", file=sys.stderr)
        sys.exit(1)


def previous_check_verified(meta_file, cnf, drat, cnf_hash, drat_hash):
    """True iff a prior .check.json records a verified-clean check for this exact
    CNF and DRAT (both re-hashed on disk to catch any change since it was written)."""
    try:
        data = json.loads(meta_file.read_text())
    except Exception:
        return False
    if not (data.get("verified") is True and data.get("verified_consistent") is True
            and data.get("cnf_sha256") == cnf_hash
            and data.get("drat_sha256") == drat_hash):
        return False
    return (cnf.exists() and drat.exists()
            and sha256_file(cnf) == data["cnf_sha256"]
            and sha256_file(drat) == data["drat_sha256"])


def check_one(cnf, drat, outdir, args):
    """Verify one proof, writing .check.out/.check.err/.check.json. Returns the
    metadata dict, or a marker dict with outcome 'skipped' / 'blocked'."""
    stem = cnf.stem
    out = outdir / f"{stem}.check.out"
    err = outdir / f"{stem}.check.err"
    meta_file = outdir / f"{stem}.check.json"
    command = [args.drat_trim, str(cnf), str(drat), "-t", str(args.time_limit)]

    cnf_hash = sha256_file(cnf)
    drat_hash = sha256_file(drat)
    existing = [p.name for p in (out, err, meta_file) if p.exists()]
    if existing:
        if previous_check_verified(meta_file, cnf, drat, cnf_hash, drat_hash):
            return {"instance": cnf.name, "outcome": "skipped"}
        return {"instance": cnf.name, "outcome": "blocked",
                "detail": f"existing outputs are not a verified-clean check; "
                          f"not overwriting ({', '.join(sorted(existing))})"}

    data = {
        "schema_version": SCHEMA_VERSION,
        "instance": cnf.name,
        "cnf_path": str(cnf),
        "drat_path": str(drat),
        "cnf_sha256": cnf_hash,
        "drat_sha256": drat_hash,
        "drat_size_bytes": drat.stat().st_size,
        "jobs": args.jobs,
        "command": command,
        "time_limit": args.time_limit,
        "returncode": None,
        "verified": None,
        "verified_consistent": None,
        "saw_verified": False,
        "saw_not_verified": False,
        "stdout_path": str(out),
        "stderr_path": str(err),
        "wall_seconds": 0.0,
        "error": None,
    }

    t0 = time.perf_counter()
    try:
        r = subprocess.run(command, stdin=subprocess.DEVNULL, capture_output=True,
                           text=True, errors="replace", check=False)
        data["wall_seconds"] = time.perf_counter() - t0
        data["returncode"] = r.returncode
        out.write_text(r.stdout)
        err.write_text(r.stderr)

        text = r.stdout + "\n" + r.stderr
        saw_v = "s VERIFIED" in text
        saw_nv = "s NOT VERIFIED" in text
        data["saw_verified"] = saw_v
        data["saw_not_verified"] = saw_nv
        rc = r.returncode
        data["verified"] = (rc == 0 and saw_v and not saw_nv)
        # consistent iff exactly one verdict line is present and it agrees with the code
        data["verified_consistent"] = (
            (rc == 0 and saw_v and not saw_nv) or (rc != 0 and saw_nv and not saw_v))
    except Exception as e:
        data["wall_seconds"] = time.perf_counter() - t0
        data["error"] = str(e)

    meta_file.write_text(json.dumps(data, indent=2) + "\n")
    return data


def classify(data):
    """Maps a real check record to: ok (verified) or bad (anything else)."""
    if data["error"]:
        return "bad"
    if data["verified"] and data["verified_consistent"]:
        return "ok"
    return "bad"


def status_label(status, data):
    if status == "ok":
        return "VERIFIED"
    if data["error"]:
        return f"BAD ({data['error']})"
    return (f"!!! NOT VERIFIED -- returncode {data['returncode']}, "
            f"saw_verified={data['saw_verified']}, saw_not_verified={data['saw_not_verified']} !!!")


def check_dir(d_dir, args):
    """Checks every proof in one folder; writes a timestamped batch record.
    Returns the per-folder counts."""
    outdir = args.result_root / d_dir.name
    counts = {"found": 0, "ran": 0, "skipped": 0, "blocked": 0, "ok": 0, "bad": 0}

    cnfs = sorted(d_dir.glob("*.cnf"))
    counts["found"] = len(cnfs)
    if not cnfs:
        return counts

    if not outdir.exists():
        print(f"{d_dir.name}: BLOCKED ({len(cnfs)} proofs missing; no result dir {outdir})")
        for cnf in cnfs:
            print(f"  {cnf.name}: BLOCKED (missing result directory)")
        counts["blocked"] = len(cnfs)
        return counts

    # Pair each CNF with its proof; a missing/empty DRAT is flagged per-instance.
    pairs, premissing = [], []
    for cnf in cnfs:
        drat = outdir / f"{cnf.stem}.drat"
        if drat.exists() and drat.stat().st_size > 0:
            pairs.append((cnf, drat))
        else:
            premissing.append(cnf.name)

    print(f"{d_dir.name}: checking {len(pairs)} proofs"
          + (f" ({len(premissing)} missing DRAT)" if premissing else ""))
    for name in premissing:
        print(f"  {name}: BLOCKED (missing or empty DRAT)")
        counts["blocked"] += 1

    started_at = datetime.now(timezone.utc)
    t0 = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(check_one, cnf, drat, outdir, args): cnf for cnf, drat in pairs}
        for fut in as_completed(futures):
            cnf = futures[fut]
            try:
                rec = fut.result()
            except Exception as e:
                counts["ran"] += 1
                counts["bad"] += 1
                print(f"  {cnf.name}: BAD (worker error: {e})")
                continue
            outcome = rec.get("outcome")
            if outcome == "skipped":
                counts["skipped"] += 1
                print(f"  {rec['instance']}: SKIP (verified-clean check exists)")
            elif outcome == "blocked":
                counts["blocked"] += 1
                print(f"  {rec['instance']}: BLOCKED ({rec['detail']})")
            else:
                counts["ran"] += 1
                status = classify(rec)
                counts[status] += 1
                print(f"  {rec['instance']}: {status_label(status, rec)}, {rec['wall_seconds']:.2f}s")

    wall_seconds = time.perf_counter() - t0
    batch = {
        "schema_version": SCHEMA_VERSION,
        "d": d_dir.name,
        "config": {"kind": args.kind, "jobs": args.jobs,
                   "drat_trim": args.drat_trim, "time_limit": args.time_limit},
        "started_at": started_at.isoformat(),
        "wall_seconds": wall_seconds,
        "counts": counts,
        "machine": platform.node(),
        "platform": platform.platform(),
    }
    ts = started_at.strftime("%Y%m%dT%H%M%SZ")
    (outdir / f"batch.{ts}.check.json").write_text(json.dumps(batch, indent=2) + "\n")
    return counts


def main():
    args = parse_args()
    drat_available(args.drat_trim)

    total = {"found": 0, "ran": 0, "skipped": 0, "blocked": 0, "ok": 0, "bad": 0}
    dirs = (sorted(p for p in args.instance_root.iterdir() if p.is_dir())
            if args.instance_root.is_dir() else [])
    for d_dir in dirs:
        if not selected_dir(d_dir, args.kind):
            print(f"Skipping {d_dir.name}")
            continue
        counts = check_dir(d_dir, args)
        for k in total:
            total[k] += counts[k]

    assert total["found"] == total["ran"] + total["skipped"] + total["blocked"]
    assert total["ran"] == total["ok"] + total["bad"]

    if total["found"] == 0:
        print(f"ERROR: no instances found under {args.instance_root} for kind={args.kind}.",
              file=sys.stderr)
        sys.exit(2)

    print(f"\nFound {total['found']}: ran {total['ran']} "
          f"(verified {total['ok']}, bad {total['bad']}), "
          f"skipped {total['skipped']}, blocked {total['blocked']}.")

    if total["bad"] or total["blocked"]:
        print("Some proofs did not cleanly verify (see flagged lines above).", file=sys.stderr)
        sys.exit(1)

    print("All selected proofs are verified (newly or from verified-clean prior checks).")


if __name__ == "__main__":
    main()
