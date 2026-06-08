#!/usr/bin/env python3
"""Run CaDiCaL on each CNF instance; save proofs, logs, and per-instance metadata.
   See the README.
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
EXIT_SAT, EXIT_UNSAT = 10, 20


def positive_int(s):
    x = int(s)
    if x < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return x


def parse_args():
    p = argparse.ArgumentParser(
        description="Run CaDiCaL on each CNF instance; save proofs, logs, and metadata.")
    p.add_argument("--kind", choices=["general", "up", "all"], required=True,
                   help="which instance family to run (general = non-up-monotone)")
    p.add_argument("--cadical", default="cadical", help="path to the cadical binary")
    p.add_argument("--jobs", type=positive_int, default=1, help="number of parallel solves")
    p.add_argument("--instance-root", type=Path, default=Path("instances"))
    p.add_argument("--result-root", type=Path, default=Path("results"))
    return p.parse_args()


def sha256_file(path):
    """Returns the SHA256 hex digest of a file."""
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


def cadical_version(cadical):
    try:
        r = subprocess.run([cadical, "--version"], stdin=subprocess.DEVNULL,
                           capture_output=True, text=True, check=True)
        return r.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        print(f"FATAL: Could not execute '{cadical}'. Is it in your PATH?", file=sys.stderr)
        sys.exit(1)


def parse_cnf_header(cnf):
    """Reads (d, tau, w, tight, up_monotone) from the 'c ...' line and
    (num_vars, num_clauses) from the 'p cnf ...' line. On a malformed header the
    affected fields stay None and a note is returned; the instance is still run."""
    info = {"d": None, "tau": None, "w": None, "tight": None,
            "up_monotone": None, "num_vars": None, "num_clauses": None}
    note = None
    try:
        with cnf.open() as f:
            for line in f:
                line = line.strip()
                if line.startswith("c ") and "=" in line:
                    fields = dict(tok.split("=", 1) for tok in line[2:].split() if "=" in tok)
                    if "d" in fields:
                        info["d"] = int(fields["d"])
                    if "tau" in fields:
                        info["tau"] = int(fields["tau"])
                    if "w" in fields:
                        info["w"] = [int(x) for x in fields["w"].split(",")]
                    if "tight" in fields:
                        info["tight"] = fields["tight"] == "True"
                    if "up_monotone" in fields:
                        info["up_monotone"] = fields["up_monotone"] == "True"
                elif line.startswith("p cnf"):
                    parts = line.split()
                    info["num_vars"] = int(parts[2])
                    info["num_clauses"] = int(parts[3])
                    break
    except Exception as e:
        note = f"header parse failed: {e}"
    return info, note


def previous_run_verified(meta_file, drat, cnf_hash):
    """True iff a prior .run.json records a clean UNSAT for this exact CNF and the
    DRAT proof on disk still matches its recorded hash (re-hashed to catch
    truncation/corruption since the JSON was written)."""
    try:
        data = json.loads(meta_file.read_text())
    except Exception:
        return False
    if not (data.get("cnf_sha256") == cnf_hash
            and data.get("result") == "unsat"
            and data.get("result_consistent") is True
            and data.get("drat_size_bytes", 0) > 0
            and data.get("drat_sha256")):
        return False
    if not drat.exists():
        return False
    return sha256_file(drat) == data["drat_sha256"]


def run_one(cnf, outdir, args):
    """Solves one instance, writing its .out/.err/.drat/.run.json. Returns either
    the full metadata dict (a real run), or a marker dict with
    outcome 'skipped' / 'blocked' (no files touched)."""
    stem = cnf.stem
    out = outdir / f"{stem}.out"
    err = outdir / f"{stem}.err"
    drat = outdir / f"{stem}.drat"
    meta_file = outdir / f"{stem}.run.json"
    command = [args.cadical, str(cnf), str(drat)]

    cnf_hash = sha256_file(cnf)
    existing = [p.name for p in (out, err, drat, meta_file) if p.exists()]
    if existing:
        if previous_run_verified(meta_file, drat, cnf_hash):
            return {"instance": cnf.name, "outcome": "skipped"}
        return {"instance": cnf.name, "outcome": "blocked",
                "detail": f"existing outputs are not a verified-clean run; "
                          f"not overwriting ({', '.join(sorted(existing))})"}

    header, header_note = parse_cnf_header(cnf)
    data = {
        "schema_version": SCHEMA_VERSION,
        "instance": cnf.name,
        "cnf_path": str(cnf),
        "cnf_sha256": cnf_hash,
        **header,
        "header_note": header_note,
        "jobs": args.jobs,
        "command": command,
        "returncode": None,
        "result": None,
        "result_consistent": None,
        "saw_unsat_line": False,
        "saw_sat_line": False,
        "stdout_path": str(out),
        "stderr_path": str(err),
        "drat_path": str(drat),
        "drat_size_bytes": 0,
        "drat_sha256": None,
        "wall_seconds": 0.0,
        "error": None,
    }

    t0 = time.perf_counter()
    try:
        # errors='replace' guards against malformed solver output; no timeout (blocks).
        r = subprocess.run(command, stdin=subprocess.DEVNULL, capture_output=True,
                           text=True, errors="replace", check=False)
        data["wall_seconds"] = time.perf_counter() - t0
        data["returncode"] = r.returncode
        out.write_text(r.stdout)
        err.write_text(r.stderr)

        solver_text = r.stdout + "\n" + r.stderr
        data["saw_unsat_line"] = "s UNSATISFIABLE" in solver_text
        data["saw_sat_line"] = "s SATISFIABLE" in solver_text

        rc = r.returncode
        data["result"] = {EXIT_UNSAT: "unsat", EXIT_SAT: "sat"}.get(rc, "unknown")
        data["result_consistent"] = (
            (rc == EXIT_UNSAT and data["saw_unsat_line"] and not data["saw_sat_line"])
            or (rc == EXIT_SAT and data["saw_sat_line"] and not data["saw_unsat_line"]))
    except Exception as e:
        data["wall_seconds"] = time.perf_counter() - t0
        data["error"] = str(e)

    if drat.exists():
        data["drat_size_bytes"] = drat.stat().st_size
        if data["drat_size_bytes"] > 0:
            data["drat_sha256"] = sha256_file(drat)

    meta_file.write_text(json.dumps(data, indent=2) + "\n")
    return data


def classify(data):
    """Maps a real-run record to one of: ok, sat, bad."""
    if data["error"]:
        return "bad"
    if data["result"] == "unsat" and data["result_consistent"] and data["drat_size_bytes"] > 0:
        return "ok"
    if data["result"] == "sat" or data["saw_sat_line"]:
        return "sat"
    return "bad"


def status_label(status, data):
    if status == "ok":
        return "OK"
    if status == "sat":
        return "!!! SATISFIABLE -- COUNTEREXAMPLE OR ENCODING BUG !!!"
    if data["error"]:
        return f"BAD ({data['error']})"
    return f"BAD (returncode {data['returncode']}, consistent={data['result_consistent']})"


def run_dir(d_dir, args, version):
    """Runs every instance in one folder; writes a timestamped batch record.
    Returns the per-folder counts."""
    outdir = args.result_root / d_dir.name
    outdir.mkdir(parents=True, exist_ok=True)
    cnfs = sorted(d_dir.glob("*.cnf"))
    counts = {"found": len(cnfs), "ran": 0, "skipped": 0, "blocked": 0,
              "ok": 0, "sat": 0, "bad": 0}
    if not cnfs:
        return counts

    print(f"{d_dir.name}: {len(cnfs)} instances")
    started_at = datetime.now(timezone.utc)
    t0 = time.perf_counter()

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {pool.submit(run_one, cnf, outdir, args): cnf for cnf in cnfs}
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
                print(f"  {rec['instance']}: SKIP (verified-clean result exists)")
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
                   "cadical": args.cadical, "cadical_version": version},
        "started_at": started_at.isoformat(),
        "wall_seconds": wall_seconds,
        "counts": counts,
        "machine": platform.node(),
        "platform": platform.platform(),
    }
    ts = started_at.strftime("%Y%m%dT%H%M%SZ")
    (outdir / f"batch.{ts}.run.json").write_text(json.dumps(batch, indent=2) + "\n")
    return counts


def main():
    args = parse_args()
    version = cadical_version(args.cadical)
    args.result_root.mkdir(parents=True, exist_ok=True)

    total = {"found": 0, "ran": 0, "skipped": 0, "blocked": 0,
             "ok": 0, "sat": 0, "bad": 0}
    dirs = (sorted(p for p in args.instance_root.iterdir() if p.is_dir())
            if args.instance_root.is_dir() else [])
    for d_dir in dirs:
        if not selected_dir(d_dir, args.kind):
            print(f"Skipping {d_dir.name}")
            continue
        counts = run_dir(d_dir, args, version)
        for k in total:
            total[k] += counts[k]

    assert total["found"] == total["ran"] + total["skipped"] + total["blocked"]
    assert total["ran"] == total["ok"] + total["sat"] + total["bad"]

    if total["found"] == 0:
        print(f"ERROR: no instances found under {args.instance_root} for kind={args.kind}.",
              file=sys.stderr)
        sys.exit(2)

    print(f"\nFound {total['found']}: ran {total['ran']} "
          f"(ok {total['ok']}, SAT {total['sat']}, bad {total['bad']}), "
          f"skipped {total['skipped']}, blocked {total['blocked']}.")

    if total["sat"] or total["bad"] or total["blocked"]:
        print("Some instances were NOT a clean UNSAT (see flagged lines above).", file=sys.stderr)
        sys.exit(1)

    print("All instances that ran are a clean UNSAT.")


if __name__ == "__main__":
    main()
