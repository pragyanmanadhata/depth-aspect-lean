# Verification record

**Checked relative formalization. All paper claims have a recorded source review.**

Checked: 2026-10-25T07:29:21.214892+00:00

- Toolchain: Lean (version 4.32.0, arm64-apple-darwin24.6.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
- Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`
- Proof modules: 322; every module imported by `DepthAspect.lean`.
- Public theorems checked for axiom dependencies: 2376.
- Full project build: passed.
- Only foundational axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- No `sorry`, `admit`, paper-specific `axiom`, `native_decide`, or `unsafe` declarations in the proof modules.

Run `python3 scripts/verify.py` from the project directory to repeat these checks. The source hashes in `summary.json` identify the precise checked files. The complete outputs are in `build.log` and `axioms.txt`.

The paper-to-source review is recorded in `correspondence/completed-review.json`; its proof and correspondence hashes must match before this status is issued. The results remain conditional on the cited general background identities listed in [ASSUMPTIONS.md](../ASSUMPTIONS.md). Those inputs are explicit theorem parameters, not new Lean axioms.
