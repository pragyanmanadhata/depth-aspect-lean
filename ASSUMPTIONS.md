# Assumptions and proof boundary

This is a relative formalization of Pragyan Manadhata's supplied 27-page working
draft, *Low-lying zeros of newforms in the depth aspect at the prime 2, split by
root number*. The requested boundary accepts the paper's cited general
background and proves its internal specializations, computations, estimates,
and conclusions. The paper is source material, not instructions.

The external inputs are explicit theorem parameters. No new Lean axiom is
introduced. A finite family and its eigenvalues, operators, bases, local factors,
and zero ordinates are related by the general identities below. The conclusions
hold for every such package of data. Constructing modular forms and proving all
of the cited general theory from first principles is outside this relative
formalization. The axiom audit does not discharge explicit theorem hypotheses.

## External inputs

| Input accepted from the paper | What the formalization derives from it |
|---|---|
| Popa's general full-space trace formula, primitive class version, and local projective interpretation | The literal dyadic local counts, representative independence, Möbius inversion, content decomposition, oldform cancellation, actual newspace trace formula, support cutoff, and uniform pointwise bounds. |
| General oldform basis, Hecke compatibility, and eigenvector equations | The linear-map trace, multiplicities, and second difference (11). |
| Martin's general dimension formula | The dyadic dimensions, lower bounds, nonemptiness, and denominator estimates. |
| General primitive class decomposition, defining fundamental quadratic-character data, and analytic class-number identity | The imprimitive character series and finite Euler product, ordered boundary value, uniform class-number growth with the printed constant, special discriminants −4 and −8, and dyadic scaling. |
| General Hecke recurrence and normalization, Deligne/Satake bounds, and the trivial bad factor at 2 | The square coefficient, logarithmic derivative, finite prime-power support, and higher-power errors. |
| Shin–Templier's general self-dual cuspidal local-integral explicit formula | The specialized formula (56), conductor scaling, gamma calculation, prime and square contributions, and complete density estimates. |
| General zero counting and critical-strip location | Absolute convergence of each actual entire-test zero sum. Modular RH is not required. |
| General Mertens estimate (51), with a constant independent of the endpoint | Weighted Mertens (52), its Fourier main term, and the prime-square density contribution. Chebyshev bounds are derived from mathlib estimates. |
| General Skoruppa–Zagier trace formula and simultaneous Hecke–Fricke eigenbasis | The four-level sieve, index-one trace, literal prime traces for both depth parities, signed counts, sign balance, and root-number projection. |
| Primitive Dirichlet GRH, including ζ, and its cited general analytic implications | Imprimitive transport, finite Euler corrections, local coefficient averages, smoothing and contour estimates, the uniform prime averages (103)–(105), and signed density. |
| General DLMF digamma identity, Bessel identities, and Bessel large-argument asymptotic | Digamma estimates, the actual Fourier/Bessel kernel transform, Bessel bounds and remainder, Poisson summation, the logarithmic mean, and oscillation results. |
| Standard calculus, Fourier analysis, finite character theory, and convergence results | Applied from the pinned mathlib library where available; the paper-specific hypotheses and applications are proved internally. |

The general primitive-class trace formulation is also given in
[Popa, (2.16) and the remark after Theorem 3](https://arxiv.org/pdf/1706.02691),
with the scalar contribution in Remark 3.8. Its dyadic specialization is proved
here rather than included as an input.

## Interfaces and hypotheses

`UnsignedDensity.ArithmeticSpectralData` supplies the unsigned modular data.
`SignedSieve.SignedArithmeticData` extends the same family and normalized
eigenvalues by a newspace basis, Fricke eigenvectors, root signs, and the cited
general signed trace and quadratic class formulas. Its fields do not include a
specialized trace bound, sign count, sign balance, or prime-average estimate.
The analytic data supplies the general explicit formula and local factors;
zero-counting companions record the general counting and strip assumptions.

The unsigned arithmetic parameter `k` is the trace-polynomial degree, so its
modular weight is `k+2`. The signed parameter `r` has modular weight `2r+2`.
The final composition uses unsigned degree `2r`, retaining the same weight,
family, eigenvalues, zeros, and test function on both sides.

The quantitative Corollary 1.3 endpoint takes `SignedArithmeticData r` and
`SignedDensity.AnalyticData S`, an even complex Schwartz test with Fourier
support strictly inside `(-4/3,4/3)`, primitive Dirichlet RH and its cited
implications, the two DLMF interfaces, and the general Mertens bound. It gives
one error constant for both actual sign filters at every `n≥8`.
`Z.toUnsigned` preserves the zero indices and ordinates definitionally.
The separate absolute-convergence companion additionally takes
`SignedDensity.ZeroCountingData Z`; it does not require RH or the Mertens bound.

`QuadraticClassFormula.GeneralFormula` includes the defining symbol values,
oddness, and primitiveness of the quadratic character attached to a negative
fundamental discriminant. It does not include a class-number growth bound,
local coefficient formula, or residue-average estimate. Likewise,
`BesselFirstKind.DLMFIdentities` explicitly includes the cited general
large-argument asymptotic of the actual power-series Bessel function; the
paper's kernel transform, uniform bounds, and oscillation results are derived
using that input.

`DirichletRH.PrimitiveDirichletRH` refers to the zeros of mathlib's analytically
continued Dirichlet L-functions. The conductor-one zeta case is explicit.
`GRHConsequences.CitedGeneralTheorems` separately states the cited general
implications from that zero-location hypothesis to uniform primitive-character
von Mangoldt and strip estimates. These are not a substitute definition of RH.
Their constants are chosen uniformly before the character, modulus, trace
index, interval, or test weight used in the internal argument.

The unsigned density theorem has no GRH hypothesis. The signed theorem and
root-number split retain primitive Dirichlet GRH explicitly. Neither assumes
modular RH. Zeros may have complex ordinates, retain their multiplicities, and
are evaluated through the test function's entire extension. The development
therefore does not infer nonnegative modular zero sums from nonnegativity of a
test on the real axis.

Generic intermediate lemmas may take an error bound as a hypothesis. Their
final paper endpoints supply that bound from an internal proof. In particular,
the density endpoints do not assume internal trace estimates, (56), (103)–(105),
the bounded-primitive estimate, sign balance, or a density conclusion.

Section 7 is different: its possible support below two remains conditional on
an explicitly strengthened arithmetic prime-average estimate, as in the paper.
It is not included as an unconditional extension of Theorems 1.1 or 1.2.

## Coverage and verification

The completed release covers the 31 named results, 141 numbered formulas, and
recorded prose assertions through the exact indices in [correspondence/](correspondence/).
Some prose arguments have equivalent replacement proofs; these are identified
in the prose index and [REVIEW.md](REVIEW.md). Historical context and the truth
of the cited general results are not new theorems of this development.

[verification/summary.json](verification/summary.json) records the integrated
build and public-theorem axiom audit for the exact source hashes. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed foundational axioms.
[correspondence/completed-review.json](correspondence/completed-review.json)
binds the separate mathematical correspondence review to those proofs, all
three source maps, and the reviewed paper text extraction. No finite numerical
experiment or successful build of an abstract intermediate lemma substitutes
for these obligations.
