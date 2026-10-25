# Formalization and verification review

The recorded review of this relative formalization concerns **322 proof modules** and
**2376 public-theorem axiom audits**, checked at **2026-10-25T07:29:21.214892+00:00**.
It separates two obligations: Lean must accept the formal proofs, and the
formal definitions, hypotheses, and conclusions must represent the paper’s
mathematical claims.

## Mathematical correspondence

The review covers the supplied working draft’s 31 named results, 141 numbered
formulas, and recorded prose assertions. The three indices in
[correspondence/](correspondence/) identify exact declarations and source hashes.
They distinguish a complete result from a component lemma, a definition, or a
cited general input. The completed review binds those indices to the exact
proof sources; changes require renewed review before a completed status can
be issued.

The main fidelity checks are:

- The local arithmetic uses actual finite residue sets and the actual quotient
  of primitive pairs by unit scaling. Projective charts and the matrix
  fixed-line condition are proved equivalent to these objects. The level-zero
  chart convention is not asserted to be a projective quotient; the quotient
  cancellation theorem uses positive depths.
- Trace and dimension results are derived from general identities and actual
  eigenbasis equations. The integer representatives, local factors, primitive
  class weights, cusp terms, normalized eigenvalue averages, and signed trace
  formulas are connected explicitly. Bounds are not substituted for the
  quantities they are meant to estimate.
- The prime-average chain uses literal characters, residue averages, coefficient
  series, and analytically continued L-values. Internal Euler-factor,
  class-number growth, Fourier, smoothing, and prime-average estimates are
  proved before they are applied to the spectral family.
- The density statements use the same finite family, root-number filters,
  normalized Hecke eigenvalues, zero ordinates, and entire test functions.
  Zero-sum absolute convergence follows from general counting and strip data;
  summability is a conclusion. Tests remain complex-valued and even where the
  paper requires evenness.
- Both signed depth parities use the same strict active-index condition. Their
  trace parameters satisfy divisibility by **8**, as required by the arithmetic
  mean calculation. The four-twist coefficients, the factor `2/L`, and the
  dimension coefficient are retained through the literal prime-to-integral
  assembly. Negative and zero trace indices are included.
- The murmuration statements concern the actual arithmetic Euler product and
  weighted kernel. Their series, integrals, logarithmic mean, bounded primitive,
  and oscillation sequences are proved for those definitions. The final support
  discussion retains its explicit hypothetical arithmetic premise.

The top-level results accept the paper’s cited general modular and analytic
inputs as theorem parameters. They do not assume internal prime estimates,
trace bounds, the specialized explicit formula, sign balance, or density
conclusions. Intermediate reusable lemmas may take such estimates as hypotheses;
the final endpoints supply them from their proofs. The precise external boundary,
including primitive Dirichlet GRH and its separate general consequences, is in
[ASSUMPTIONS.md](ASSUMPTIONS.md).

The unsigned result adds no GRH hypothesis. No modular GRH is used in either
family. General zero-counting and critical-strip inputs suffice for the
zero-convergence companions. The general gamma and Bessel identities are kept
visible rather than relabeled as proved here.

## Scope qualifications

The correspondence counts identify coverage, not identical generality for every
printed formula. The Popa trace-formula input is restricted to positive odd
Hecke indices coprime to the level, the specialization needed for the dyadic
argument. The convention `H(0) = -1/12` is not explicitly asserted; the relevant
zero-discriminant terms cancel without using its value. Some signed intermediate
estimates require `n≥8`, while the final signed-density theorem includes `n=7`
through the separate finite-prefix argument. These qualifications do not change
the principal density statements. They supplement the unchanged correspondence
records and their original review timestamps.

## Corrections and equivalent proof routes

[AUDIT.md](AUDIT.md) records the corrections and statement clarifications. These
include using exact dimension formulas for nonemptiness at the smallest signed
level; retaining the contextual interval ordering in standalone prime-average
statements; respecting the paper’s odd-prime convention; separating the excluded
prime in Lemma 6.2; and covering truncated blocks below 3 and finite initial
depths with very small support. The finite-prefix envelope is uniform in the
auxiliary spectral data.

The formalization need not repeat every intermediate argument to establish the
same conclusion. In particular, the cited general central-line explicit formula
is evaluated directly by an absolutely convergent Fourier expansion. This
replaces the optional line-shift route in the prose. The endpoint variation
estimate is proved by derivative integrability and monotonicity, without a
separate asymptotic characterization at the endpoint. The general Poisson theorem
is applied after deriving compact support and Fourier decay, replacing the
printed Fejer-kernel passage. Exact sieving, a conjugate-root/Chebyshev argument,
and an endpoint-safe primitive also replace corresponding prose derivations;
the precise substitutions are listed in the prose index. The source maps identify
these as alternative proofs, not missing premises or assumed conclusions.

## Verification records

The integrated verifier requires the umbrella to import exactly the proof
modules. It regenerates the public-theorem audit, completes the build, requires
an axiom report for exactly the requested theorem names, and permits only
`propext`, `Classical.choice`, and `Quot.sound`. A comment-aware scan rejects
placeholders, added axioms, native-evaluation proof shortcuts, and unsafe proof
sources. Nested proof files are rejected rather than silently omitted.

The theorem collector is a lightweight source parser, not a general Lean
environment enumerator. Its supported namespace and declaration forms must be
checked against the release sources. Private proofs, definitions, and instances
are checked by the build, and their axiom dependencies are included transitively
when public theorems use them. A theorem’s explicit hypotheses remain hypotheses;
the axiom report does not prove that an external identity holds for modular forms.

All nine Git dependencies in `lake-manifest.json` are checked at their exact
revisions: mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop,
Qq, batteries, and Cli. Before and after verification, tracked modifications and
untracked or ignored Lean sources in those dependency checkouts outside their
`.lake/build` and `.lake/packages` caches are rejected. Source-file and source-set changes are detected by hashes and
fresh inventories, including the verification scripts, toolchain and dependency
configuration, and correspondence files.

A completed-paper label additionally requires
[completed-review.json](correspondence/completed-review.json) to match the exact
proof-source set, all three correspondence maps, and the paper text extraction. Compilation cannot create
that mathematical review. The integrated results and raw output are preserved
in [verification/summary.json](verification/summary.json),
[build.log](verification/build.log), and [axioms.txt](verification/axioms.txt).
A later [clean-source certificate](verification/clean-source/summary.json)
records the successful complete verifier run at **2026-10-25 21:16:43 UTC**.
It repeats the builds and axiom checks, and verifies the existing correspondence
record's source bindings; it does not constitute a new mathematical review.

Publication preparation is documented in [PUBLICATION.md](PUBLICATION.md).
Documentation, ignore rules, the manuscript copy, and CI configuration are
outside the integrated certificate’s recorded source set. The publication work
does not create, refresh, or independently repeat the mathematical correspondence
review.

## Limits and reproduction

These checks establish the encoded implications under the stated general
assumptions, together with a recorded paper-to-source review. They do not prove
GRH, reconstruct the general modular-form theory from first principles, or turn
a natural-language paper into a kernel-checked object. The trust boundary also
includes Lean’s kernel, the pinned libraries and toolchain, and the correctness
of the correspondence review. Changing a recorded file invalidates its recorded
hash; changing reviewed proofs or correspondence files also requires renewed
mathematical review under the workflow above.

Run `python3 scripts/verify.py` from the project directory to repeat the full
verification. Use `--serial` for dependency-ordered module builds on limited
memory, or `--require-current-modules` only when all individual exports are
already current. `lake env lean CheckAxioms.lean` repeats the axiom report alone
and is not a substitute for the complete verifier or the separate paper review.
