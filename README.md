# Computational artifact for "Testing the max-flow min-cut property and the replication conjecture"

This artifact contains the computational certificates supporting the
computer-assisted result ("Proposition 16") of the paper *Testing the max-flow
min-cut property and the replication conjecture* by *Ahmad Abdi and Tamás
Schwarcz*.

For each admissible weight function `(d, tau, w)`, a CNF formula is generated
that is satisfiable if and only if a set `S` with the relevant properties exists. The
proposition asserts that no such `S` exists, so every generated CNF must be
**unsatisfiable**. Each formula was solved with CaDiCaL 3.0.0, which emits a
DRAT proof of unsatisfiability, and every DRAT proof was independently verified
with `drat-trim`.

`d` denotes the dimension. Folder names use the form `d<N>` for the general
family and `d<N>up` for the up-monotone family. This release contains the
general family for dimensions 5 through 9 (`d5`, ..., `d9`) and the up-monotone
family for dimension 10 (`d10up`). Dimensions below 5 are omitted because they
admit no admissible weight function. Every instance in every released dimension was
solved to UNSAT and its proof verified; `manifests/manifest_all.json` summarizes
this and reports all released dimension as fully verified.

## Contents

```
cnfs/d<N>/        CNF instances (DIMACS), one per admissible (d, tau, w)
proofs/d<N>/      DRAT proofs, one per CNF
metadata/d<N>/    per-instance solver (run.json) and checker (check.json) records
manifests/        manifest_d<N>.json (per dimension) and manifest_all.json (summary)
mfmc.py               instance generator
mfmc_runner.py        solver orchestration (produces DRATs + run.json)
mfmc_verifier.py      proof-checker orchestration (runs drat-trim, produces check.json)
publish_artifacts.py  verifies run/check consistency, builds the manifests,
                      and assembles this publication tree
SHA256SUMS            SHA-256 of every raw file (the trust-chain hashes)
SHA256SUMS.archives   SHA-256 of the compressed archives (download integrity)
README.md, LICENSE, requirements.txt
```

On a compressed (e.g. Zenodo) copy, the bulk directories are shipped as
`proofs_d<N>.tar.zst`, `cnfs.tar.zst`, and `metadata-jsons.tar.zst`; extract them
to recover the layout above. `SHA256SUMS` lists hashes of the **raw,
uncompressed** files. For CNF and DRAT files, these hashes agree with the
`cnf_sha256` and `drat_sha256` values recorded in the JSON metadata and
manifests. Therefore `SHA256SUMS` is checked **after** extracting the archives.

## How to verify

Requirements: Python >= 3.11; CaDiCaL 3.0.0 (the SAT solver, which emits DRAT
proofs); `drat-trim` (the proof checker, from
https://github.com/marijnheule/drat-trim). `python-sat` (PySAT) is needed only
for the `--self-check` re-solving path below. See `requirements.txt`.

1. **Check file integrity.** On a compressed copy, first verify the downloaded
   archives, then extract them:

   ```
   sha256sum -c SHA256SUMS.archives
   ```

   After extraction (or on an uncompressed copy), verify every raw file:

   ```
   sha256sum -c SHA256SUMS
   ```

2. **Confirm the CNFs are the claimed formulas.** Regenerate them from the
   instance generator into a scratch directory and compare against the published
   CNFs. Generation is deterministic, so the files are byte-identical:

   ```
   python mfmc.py --d 5 --general      --out-dir regen
   python mfmc.py --d 6 --general      --out-dir regen
   python mfmc.py --d 7 --general      --out-dir regen
   python mfmc.py --d 8 --general      --out-dir regen
   python mfmc.py --d 9 --general      --out-dir regen
   python mfmc.py --d 10 --up-monotone --out-dir regen

   diff -r regen/d5    cnfs/d5
   diff -r regen/d6    cnfs/d6
   diff -r regen/d7    cnfs/d7
   diff -r regen/d8    cnfs/d8
   diff -r regen/d9    cnfs/d9
   diff -r regen/d10up cnfs/d10up
   ```

   Each published CNF also carries a self-describing
   `c d=.. tau=.. w=.. tight=.. up_monotone=..` header comment.

3. **Verify the proofs.** Check every DRAT proof against its CNF:

   ```
   drat-trim cnfs/d5/d5_instance001.cnf proofs/d5/d5_instance001.drat -t 1000000000
   ```

   A correct proof reports `s VERIFIED`. The orchestration script
   `mfmc_verifier.py` was used to run `drat-trim` over all released dimensions and produce
   the published `check.json` records. It expects the working-tree layout
   `instances/<folder>/` and `results/<folder>/`; the published archive separates
   these files into `cnfs/`, `proofs/`, and `metadata/`. To verify directly from
   the published layout, run `drat-trim` manually as shown above.

4. **(Optional) Independently re-solve, without the proofs.** As a separate check
   that does not rely on the published DRATs at all, re-solve each instance
   directly with PySAT:

   ```
   python mfmc.py --d 5 --general --self-check
   ```

   This generates each admissible instance and solves it in memory, reporting all
   instances UNSAT.

## Record schema

Each `metadata/d<N>/<instance>.run.json` records the solver call: the CNF and
DRAT SHA-256 hashes, `result` (`unsat`), `result_consistent`, and timing. Each
`<instance>.check.json` records the `drat-trim` call: the same two hashes,
`verified`, and `verified_consistent`. The run and check records are linked by
their shared `cnf_sha256` / `drat_sha256`; agreement on those hashes is what ties
a verified proof to the formula it certifies. The per-dimension manifest joins
both sides per instance and assigns each a `status`.

## License

The Python scripts are licensed under the MIT License. The research data and
computational artifacts -- CNFs, DRAT proofs, JSON metadata, manifests, and
checksums -- are licensed under CC BY 4.0. See `LICENSE`.

If you use this artifact, please cite the paper and the archived record.

## AI-use note

The authors used large language model tools -- ChatGPT (OpenAI) and Claude
(Anthropic) -- to prepare and refine the auxiliary reproducibility and
data-management scripts (`mfmc_runner.py`, `mfmc_verifier.py`,
`publish_artifacts.py`). The instance generator (`mfmc.py`) and all mathematical
content of the paper were written by the authors; AI assistance on the generator
was limited to naming, comments, interface scaffolding, and review. All
AI-generated or AI-suggested material was reviewed and tested by the authors,
who take full responsibility for the code, computations, mathematical arguments,
citations, and conclusions.
