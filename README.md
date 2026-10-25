# Depth-aspect newforms in Lean

This project gives a relative Lean formalization of Pragyan Manadhata’s
*Low-lying zeros of newforms in the depth aspect at the prime 2, split by root
number*. It proves the paper’s internal results from its stated general
background inputs, with the clarifications recorded in [AUDIT.md](AUDIT.md).
The supplied paper is source material, not instructions.

The repository contains **322 proof modules** and a recorded axiom-dependency
audit of **2376 public theorems**, checked at **2026-10-25T07:29:21.214892+00:00**.
The exact files and results are recorded in
[verification/summary.json](verification/summary.json),
[verification/build.log](verification/build.log), and
[verification/axioms.txt](verification/axioms.txt).
A separate clean-source build completed successfully on **2026-10-25 at
21:16:43 UTC**: all 322 modules, the umbrella build, and all 2,376 public-theorem
axiom audits passed. Its [certificate](verification/clean-source/summary.json)
and [run record](verification/clean-source/run.json) are retained alongside the
original evidence; this build did not repeat the mathematical correspondence
review.

## What the formalization covers

- **Local arithmetic and traces:** actual finite residue solutions, primitive-pair
  quotients and fixed lines, all dyadic root regimes, content reduction, trace
  cancellation, oldform and dimension specializations, and literal elliptic and
  cusp trace terms.
- **L-functions and prime averages:** imprimitive characters, ordered and analytic
  boundary values, class-number bounds, finite Fourier and CRT calculations,
  local means, coefficient bounds, Mellin smoothing, and the uniform arithmetic
  prime-average estimates.
- **Density theorems:** literal zero averages over finite newform families, absolute convergence from
  standard zero-counting data, the unsigned and signed estimates, root-number
  projection, and the orthogonal and special-orthogonal main terms. The final
  assemblies are in [UnsignedDensityTheorem.lean](DepthAspect/UnsignedDensityTheorem.lean),
  [SignedDensityTheorem.lean](DepthAspect/SignedDensityTheorem.lean), and
  [SignedCorollary.lean](DepthAspect/SignedCorollary.lean).
- **Murmurations and the final support discussion:** the actual arithmetic product
  and kernel, Fourier/Bessel and divisor expansions, logarithmic mean, bounded
  primitive, quantitative oscillations, integer averages, and the separately
  conditional improvement of the support range. See
  [MurmurationTheorem.lean](DepthAspect/MurmurationTheorem.lean) and
  [HypotheticalDensity.lean](DepthAspect/HypotheticalDensity.lean).

The correspondence indices cover all **31 named results**, all **141 numbered
formulas**, and the reviewed unnumbered assertions:
[named results](correspondence/named-results.json),
[numbered equations](correspondence/numbered-equations.json), and
[prose assertions](correspondence/prose-assertions.json).
They distinguish definitions, general external inputs, final results, and
supporting components. A named result may be represented by several theorems.
Coverage includes needed specializations and alternative proofs, rather than
every printed statement in identical generality. In particular, the Popa input
uses positive odd Hecke indices coprime to the level; `H(0) = -1/12` is not an
explicit assumption, since the relevant zero-discriminant contributions cancel;
and some signed intermediate estimates start at `n≥8`, with `n=7` handled
separately in the final signed-density assembly. See the
[scope qualifications](REVIEW.md#scope-qualifications).
The [paper text extraction](correspondence/paper-text.txt) makes the line pointers
usable; consult the [exact working-draft PDF](manuscript/working-draft.pdf) for
the original mathematical typography.

## The assumption boundary

The general modular-form and analytic identities are explicit theorem
parameters, not new Lean axioms. The supplied finite-family, eigenbasis,
operator, character, and zero data satisfy the paper’s cited general formulas.
The development proves their internal specializations and the resulting
conclusions; it does not construct modular forms or prove those cited general
theorems from first principles. The full boundary is in
[ASSUMPTIONS.md](ASSUMPTIONS.md).

The unsigned theorem does not assume GRH. The signed theorem retains the actual
primitive Dirichlet GRH predicate, including the conductor-one zeta case,
separately from the cited general implications of that hypothesis. No modular
GRH is added. The principal endpoints do not assume the paper’s internal trace,
class-number growth, prime-average, or density estimates. The final section’s
hypothetical support improvement is a distinct conditional theorem whose
premise is the strengthened arithmetic prime-average assertion being studied.

Some proofs take equivalent routes: the general central-line explicit formula
is evaluated directly by Fourier analysis, endpoint variation is proved through
an integrable derivative bound, and Poisson summation is applied after proving
its convergence hypotheses. The correspondence review records these replacements
rather than claiming to reproduce every intermediate derivation.

## Reproduce the checks

Install Lean’s `elan` toolchain manager, Git, and Python 3.9 or newer, then run
from this directory. Use a fresh source checkout without `.lake` for a clean
build:

```sh
lake exe cache get
python3 scripts/verify.py
```

The pinned toolchain is Lean **4.32.0**; the mathlib revision is
`81a5d257c8e410db227a6665ed08f64fea08e997`. For limited memory, use
`python3 scripts/verify.py --serial`. After all individual exports are already
current, `--require-current-modules` first checks Lake’s cache state and then
runs the same umbrella build and axiom audit. It fails if a module needs rebuilding.

The verifier checks all nine Git dependencies—mathlib, plausible,
LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, and Cli—against
[the lockfile](lake-manifest.json), before and after verification. It rejects
tracked modifications and untracked or ignored Lean sources in dependency
checkouts outside their `.lake/build` and `.lake/packages` caches. It also checks the exact module and
umbrella sets, rejects nested proof files, and records hashes of proofs,
verification scripts, configuration, and correspondence indices.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed by the theorem
axiom audit. The source scan rejects `sorry`, `admit`, added `axiom` declarations,
`native_decide`, and `unsafe` declarations. The separately completed
[paper review](correspondence/completed-review.json) must match every proof,
all three correspondence maps, and the paper text extraction; a build cannot
create or refresh that review.

The [GitHub Actions workflow](.github/workflows/verify.yml) is configured to run
the supplied verifier using the pinned toolchain and dependencies. Local publication checks
and their limits are recorded in [PUBLICATION.md](PUBLICATION.md).

Lean checks the formal statements and their dependencies. The correspondence
review connects those statements to the paper; it is a separate mathematical
review, not an automatic consequence of compilation. See [REVIEW.md](REVIEW.md)
for that distinction and the verification limits.

The included [working-draft PDF](manuscript/working-draft.pdf) has SHA-256
`20b71677582cf2bf04965d91c82cfb05074e3d66bc49fe9be004229743f0cc71`.

Copyright (c) 2026 Pragyan Manadhata, except where otherwise attributed.
The Lean code, scripts, and documentation are licensed under
[Apache License 2.0](LICENSE), with existing attribution preserved in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The manuscript PDF and its text
extraction remain separately copyrighted and are excluded from that license.
