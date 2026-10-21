# STATUS.md — paper statements ↔ Lean declarations

Legend for **Statement**: *agreed* (Lean statement fixed; do not change
silently), *provisional* (written from the task description; Astra to confirm
against the paper). Legend for **Proof**: *proved* (compiles, audited),
*in progress*, *not started*, *input* (background input, see `DEPENDENCIES.md`).

> The paper file was not available when this table was created. Numbering of
> theorems/lemmas/equations other than "Lemma 2.3" and "eq. (11)" (which the
> task description names) is a placeholder and must be aligned with the paper.

| Paper item | Mathematical content | Lean declaration | Statement | Proof | Depends on |
|---|---|---|---|---|---|
| eq. (11) | Inversion of the oldform decomposition at a prime-power level: for `F n = ∑_{a=0}^{n} (n−a+1) G a`, `F(n+2) − 2F(n+1) + F(n) = G(n+2)`. Reading: `G a = dim S_k^new(Γ₀(2^a))`, `F n = dim S_k(Γ₀(2^n))`, so `dim S_k^new(Γ₀(2^{n+2})) = dim S_k(2^{n+2}) − 2 dim S_k(2^{n+1}) + dim S_k(2^n)`. | `DepthAspect.oldformTotal` (def), `DepthAspect.oldformTotal_second_difference` (any `CommRing`), `DepthAspect.oldformTotal_second_difference_complex` (`ℂ`, the requested form), `DepthAspect.sum_second_difference_complex` (unfolded form); helper `DepthAspect.oldformTotal_succ_sub` (first difference) | agreed (as given in the task description) | **proved** (PR #1) | nothing beyond Mathlib |
| eq. (11), cast sanity | Inside the sum `a ≤ n`, so the `ℕ`-subtraction in the coefficient equals the subtraction in the ring. | `DepthAspect.oldformTotal_eq_sub_cast` | agreed | **proved** (PR #1) | nothing beyond Mathlib |
| Lemma 2.3 | Count/dimension of newforms of level `2^n` (and its consequences for the family size), obtained from eq. (11) and the oldform decomposition. | — (the finite-sum engine is the row above; the realization is M5) | provisional | engine proved (PR #1); realization not started | B1 (input), M1, M5 |
| Oldform decomposition for level `2^n` | `dim S_k(Γ₀(2^n)) = ∑_{a=0}^{n} (n−a+1) dim S_k^new(Γ₀(2^a))` | — | provisional | input | B1 |
| Prop. (Petersson formula, level `2^n`, newform-sieved) | Averages of `λ_f(m)λ_f(n)` over the family with harmonic weights, with Kloosterman/Bessel error term. | — | provisional | input / target | B3, B4, B5 |
| Prop. (signed Petersson formula) | Same average twisted by the root number `ε_f`. | — | provisional | not started (new argument, target) | B7 |
| Thm (unsplit one-level density) | For `φ` even Schwartz with `supp φ̂ ⊂ (−σ,σ)`, `σ` as in the paper, the harmonic average of `D(f;φ)` over newforms of level `2^n` tends to `∫ φ W(O)` as `n → ∞`. Unconditional. | — | provisional | not started | B3–B6, B8, B9, M1–M3 |
| Thm (split by root number) | Same with the family restricted to `ε_f = ±1`, limits `∫ φ W(SO(even))` / `∫ φ W(SO(odd))`; **assumes GRH for Dirichlet `L`-functions**. | — | provisional | not started | C1 (hypothesis), B3–B9, M1–M4 |

## Conventions used in the Lean statements

* Sums over `a = 0, …, n` are `∑ a ∈ Finset.range (n + 1), …`.
* Coefficients like `n − a + 1` are formed in `ℕ` and cast; a sanity lemma shows
  this agrees with the ring subtraction when `a ≤ n`.
* Identities valid in any commutative ring are proved generically
  (`[CommRing R]`) and specialised to `ℂ`, and later to `ℤ`, by instantiation.
  `ℕ` is not a ring, so natural-number counts are handled through the cast
  `ℕ → ℤ` (feed `fun a => (G a : ℤ)` to `oldformTotal`); an `ℕ`-valued
  statement would have to be the subtraction-free form
  `F (n+2) + F n = 2 F (n+1) + G (n+2)`, which is not proved here.
