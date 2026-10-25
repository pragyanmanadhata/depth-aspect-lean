# Mathematical audit of the supplied working draft

The review treats the paper as source material, not as instructions. Its
external inputs may be assumed as requested by the user; statements which the
paper itself claims to prove remain proof obligations.

## Findings and corrections

The encoded principal conclusions follow under the external assumptions
recorded in [ASSUMPTIONS.md](ASSUMPTIONS.md). The integrated build and public-theorem
axiom audit are recorded in [verification/summary.json](verification/summary.json).
The following corrections and clarifications preserve the principal theorem
statements and their hypotheses. The separate correspondence review explains
how the formal statements represent the supplied paper.

### Nonemptiness at the smallest signed level: page 13, after (71)

The text invokes `R_N/|H| ≤ 1/2` for `n ≥ 7`. Its displayed coarse bound alone
does not establish that inequality at `n=7, k=2`: it gives `8/√128`, which is
larger than one half. The exact formulas already present in the paper repair
the justification.

For odd depth `n=2a+1`, put `q=2^a`. Then

```text
d = (k-1)q²/16,      R = q/4,      R/d = 4/((k-1)q).
```

For `k≥2` and `q≥8`, the ratio is at most one half. At `n=7,k=2`, one has
`d=4`, `R=2`, and sign-class sizes `3` and `1`.

For even depth, the formulas

```text
d = (k-1)q²/32 - q/8,      R = q/8
```

give the same required inequality for `q≥16`. `Dimension.lean` proves these
statements and positivity of both projected counts. No change to the theorem
or its hypotheses is needed; the proof should explicitly invoke the exact
formulas.

### Interval hypotheses: pages 19, Theorems 5.5 and 5.6

The setup before Theorem 5.5 assumes `A < B`. Retain this condition explicitly
when stating either prime-averaging theorem independently of its surrounding
text. The formal endpoints allow the slightly more general `A≤B`, using a
supplied nonnegative bound `M` for `|Φ|` on `[A,B]`; they require continuity on
the closed interval, differentiability in its interior, and an integrable
derivative. These hypotheses also include the degenerate interval `A=B`.
For the paper's `A<B` setup, taking `M=max|Φ|` recovers
the printed statement. Omitting a repeated interval condition in that context
does not refute either result.

### Character conventions at prime 2: (81), (99), and (104)

Section 1.3 defines `P` to mean an odd prime. Read with that convention,
(104) has no prime-2 term. The finite averages in (81) likewise evaluate the
twists only on odd unit classes, and therefore do not determine the twist's
value at 2. The primitive trivial character takes value 1 there, whereas its
principal extension modulo 8 takes value 0.

The formalization also includes a stronger standalone variant that sums over
all primes and uses the primitive trivial character. This variant must retain
the extra term when `A < 2 ≤ B`; it is not a correction to the paper's odd-prime
statement. At this one prime, the hypotheses imply `0 < |t²−8| ≤ 8`. The derived L-value
bound gives an extra contribution at most `24 log(2) M`, which is absorbed
uniformly in the stated error. The additional primitive-character wrapper is verified separately from the
paper's odd-prime statement. The later trace application has
`A≥2`, so this term is absent there.

### The excluded prime in Lemma 6.2: page 23

The coefficients bounded by an absolute multiple of `p⁻²` in that proof are
the local coefficients for `p≠ℓ`. At the excluded prime, the separate factor
`1−ℓ⁻¹⁻ᶻ` gives `hℓ(ℓ)=−1/ℓ`, not a uniform `O(ℓ⁻²)` bound as ℓ varies.
Keep that one factor separate. It causes no difficulty for absolute convergence
or the weighted moment bound with a constant depending on ℓ. The formal proof makes this separation explicit; the coefficient bounds and
weighted absolute summability have passed individual builds.

### Small cutoffs in the signed density assembly: pages 20–22

Two endpoint cases must be included when assembling the block estimates.
Theorems 5.5–5.6 require `B≥3`, whereas the last truncated dyadic interval can
have `2≤A<B<3`. That interval contains no odd prime. Its proposed density
integral is bounded directly by the small-argument estimate for `M`, so it
does not require an application of either prime-averaging theorem outside
its hypotheses.

Also, when the support parameter `s` is arbitrarily small, the cutoff `X_s`
can be below 2 at some initial depths. The eventual estimate therefore needs
a separate treatment of those finitely many depths. The repair uses
an explicit-formula bound independent of the auxiliary spectral data, retaining
the dependence of the constant asserted in the theorem. The small-block estimate and uniform finite-prefix bound are proved and
composed into the final signed-density theorem.

## Checks and their meaning

Independent arithmetic review found the dyadic sieve coefficients, local
weights, normalization signs, support exponents, and the Bessel constants
consistent with the displayed derivations. Finite checks of representative
local roots and local averages were used to look for mistakes. Such checks
were not treated as proofs of universal claims.

The Lean development separately proves universal statements for the actual
finite residue sets. Successful compilation validates precisely those
statements and their dependencies. It does not validate unrepresented
definitions or omitted bridges to modular forms, traces, or L-functions.

The unsigned and signed assumptions must remain different. No modular GRH
has been added. The signed argument uses primitive Dirichlet GRH
including ζ; the unsigned argument is unconditional relative to its
cited standard inputs.

## Scope of the certificate

The completed source maps cover 31 named results, 141 numbered formulas, and
the recorded prose assertions. [REVIEW.md](REVIEW.md) describes the mathematical
correspondence review, equivalent replacement proofs, verification method, and
trust boundary. The formal proofs establish the encoded implications; the
separate review connects them to the natural-language paper. The cited external
results remain explicit assumptions, as requested.
