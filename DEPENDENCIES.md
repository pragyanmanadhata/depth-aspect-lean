# DEPENDENCIES.md — inputs, hypotheses, missing infrastructure, discharge status

This file is the ledger of everything the formalization *assumes*. Every
hypothesis of a project theorem must be traceable to a row here. Rows are
labelled `B*` (background input from the literature), `C*` (intended
conjectural hypothesis), `M*` (missing definition or realization proof).

Status values: **assumed** (enters as an explicit hypothesis), **discharged**
(proved in this repository or available in Mathlib, with the declaration
named), **not needed yet**, **never discharged** (conjectural).

> Provenance note. The paper file was not available in the session that
> created this ledger. Rows were written from the task description, the
> standard structure of one-level-density arguments for holomorphic newforms,
> and a search of the pinned Mathlib checkout. Astra's specification is
> authoritative; rows marked *(provisional)* must be confirmed or corrected
> against the paper before they are relied on.

## Pinned environment

| | |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` |
| Mathlib | tag `v4.35.0` = commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (2026-10-13) |
| Transitive deps | pinned in `lake-manifest.json` (batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli) |

## A. Background inputs (non-conjectural)

| Id | Input (statement sketch) | Source | Mathlib `v4.35.0` search result | Lean treatment | Status |
|---|---|---|---|---|---|
| B1 | **Oldform decomposition at a prime power.** `S_k(Γ₀(2^n)) = ⊕_{a=0}^{n} ⊕_{d ∣ 2^{n−a}} ι_d S_k^new(Γ₀(2^a))`, hence `dim S_k(Γ₀(2^n)) = ∑_{a=0}^{n} (n−a+1)·dim S_k^new(Γ₀(2^a))`. | Atkin–Lehner (1970); Li (1975) | Not present. No newforms, oldforms, Atkin–Lehner operators or Hecke operators on `ModularForm`; only the abstract Hecke ring `Mathlib/NumberTheory/HeckeRing/Defs.lean` and `Gamma0` in `Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`. | Hypothesis of the dimension/count statement of Lemma 2.3: a function `G : ℕ → ℂ` (newform counts) and `F` (full-space counts) satisfying the displayed relation. The *finite-sum inversion* is proved without it (`oldformTotal_second_difference`). | **assumed**; separate prerequisite, not started |
| B2 | **Dimension formula** for `S_k(Γ₀(N))` (or at least its asymptotic in `N = 2^n`). *(provisional: needed only if the paper's main term uses explicit dimensions rather than the Petersson-normalized count.)* | Shimura; Cohen–Oesterlé | Level one only: `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`. | Hypothesis, if needed. | not needed yet |
| B3 | **Petersson trace formula** for `Γ₀(2^n)` and its newform-sieved version (harmonic weights, Kloosterman sums `S(m,n;c)`, Bessel kernel `J_{k−1}`). | Petersson; Iwaniec–Luo–Sarnak §2; Petrow–Young / Ng for non-squarefree level *(provisional attribution)* | Petersson inner product integrand: `Mathlib/NumberTheory/ModularForms/Petersson.lean`; Hecke bound and Parseval for `q`-expansions: `Mathlib/NumberTheory/ModularForms/Bounds.lean`. No Poincaré series, no trace formula. | Hypothesis (structure packaging the formula with its error term). | **assumed** |
| B4 | **Weil bound** `|S(m,n;c)| ≤ τ(c)·gcd(m,n,c)^{1/2}·c^{1/2}`. | Weil | Not present (0 hits for Kloosterman; Gauss sums exist in `Mathlib/NumberTheory/GaussSum.lean`). | Hypothesis. | **assumed** |
| B5 | **Bessel function bounds** for `J_{k−1}(x)` (small- and large-`x` regimes) used to truncate the Kloosterman terms. | Watson; ILS Lemma 2.1 | `besselJ` is defined in `Mathlib/Analysis/SpecialFunctions/Bessel.lean` (via `₀F₁`, parity, analyticity). No asymptotic bounds found. | Hypothesis, stated for Mathlib's `besselJ`. | **assumed** |
| B6 | **Explicit formula** for `L(s,f)`, `f` a newform of level `2^n`, with conductor `2^n`, Γ-factor `Γ_ℂ(s + (k−1)/2)`, test function `φ` even Schwartz with `supp φ̂ ⊂ (−σ,σ)`. | Iwaniec–Kowalski Thm 5.12; ILS §4 | `L`-function of a modular form and its functional equation: `Mathlib/NumberTheory/ModularForms/LFunction.lean` (built on `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`). No zero-counting, no explicit formula. Fourier transform and Schwartz space exist (`Mathlib/Analysis/Fourier/*`, `SchwartzMap`). | Hypothesis: a structure `ExplicitFormulaData` relating `D(f;φ)` to prime sums. | **assumed** |
| B7 | **Root number** of a newform of level `2^n`: `ε_f = i^k · η_f` with `η_f` the Atkin–Lehner `W_{2^n}`-eigenvalue; the Atkin–Lehner-twisted Petersson formula used to split the family by sign. | Atkin–Lehner; ILS §2 (squarefree case) — the paper's new input for level `2^n` *(provisional)* | Not present. | Hypothesis for the inputs; the paper's new twisted-formula argument is a target for formalization. | **assumed** (inputs) / target (new argument) |
| B8 | **Prime sums**: Chebyshev/PNT-type bounds, `∑_{p ≤ x} log p / p = log x + O(1)`, and sums over primes weighted by `φ̂(log p / log 2^n)`. | Mertens; PNT | Chebyshev `θ, ψ` with upper/lower bounds: `Mathlib/NumberTheory/Chebyshev.lean`; Abel summation: `Mathlib/NumberTheory/AbelSummation.lean`; `ArithmeticFunction.vonMangoldt`. PNT with error term is **not** in Mathlib (research library: *PrimeNumberTheoremAnd*). | Hypothesis where an error term beyond Chebyshev is needed; otherwise discharge from Mathlib. | **assumed**; partly dischargeable |
| B9 | **Symmetry-type densities** `W(O)`, `W(SO(even))`, `W(SO(odd))` and the Plancherel identities `∫ φ W = φ̂(0) ± φ(0)/2` used to identify the main terms. | Katz–Sarnak | Fourier inversion on `ℝ` for Schwartz functions exists. | To be proved in-repo from Mathlib (pure Fourier analysis). | not needed yet; dischargeable |

## B. Intended conjectural hypotheses

| Id | Hypothesis | Used by | Mathlib search result | Lean treatment | Status |
|---|---|---|---|---|---|
| C1 | **GRH for Dirichlet `L`-functions**: every non-trivial zero of `L(s,χ)`, `χ` a Dirichlet character (all moduli needed by the paper; *provisional: possibly only characters of 2-power modulus*), has real part `1/2`. | Signed (root-number-split) theorem | Only `RiemannHypothesis` for `ζ` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`). Dirichlet `L`-functions, analytic continuation and functional equation exist (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`); no GRH statement. | Define `DirichletGRH : Prop` in-repo on top of `DirichletCharacter.LFunction`; pass it as an explicit hypothesis of the signed theorem. | **never discharged** (intended hypothesis) |

The unsplit theorem is intended to be unconditional: it must not take `C1`.

## C. Missing definitions and realization proofs

| Id | Missing item | Why it is needed | Search result | Plan | Status |
|---|---|---|---|---|---|
| M1 | Newforms of level `2^n`, weight `k`, as a type/finset `Newforms k n` with Hecke eigenvalues `λ_f(m)` (normalized) and root number `ε_f`. | Family definition; every main theorem quantifies over it. | Not in Mathlib (see B1, B7). Research libraries to check before building: FLT project (automorphic forms infrastructure), Mathlib's modular-forms roadmap. | Introduce as a *structure of hypotheses* (axiomatic interface) first; realize from Mathlib's `CuspForm (Gamma0 (2^n)) k` later. | open |
| M2 | Harmonic weights `ω_f = Γ(k−1)/(4π)^{k−1} ⟨f,f⟩` and the Petersson-normalized average `∑_f^h`. | Main theorems are stated with harmonic weights *(provisional)*. | `petersson` integrand only. | Interface field in M1. | open |
| M3 | One-level density `D(f;φ) = ∑_γ φ(γ · log(2^n)/2π)` over non-trivial zeros of `L(s,f)`. | Statement of the main theorems. | Zeros of `L(s,f)` are not a Mathlib object. | Interface field; realization via `ModularForm.LFunction` later. | open |
| M4 | `DirichletGRH` as a `Prop`. | C1 | Not present. | Define in-repo (small). | open |
| M5 | Realization proof that `oldformTotal` with `G a = dim S_k^new(Γ₀(2^a))` equals `dim S_k(Γ₀(2^n))`. | Turns the proved identity into Lemma 2.3 proper. | Requires B1 (not in Mathlib). | Separate prerequisite; depends on B1/M1. | open |

## D. Discharge status summary

| Item | Status | Where |
|---|---|---|
| Finite-sum inversion behind Lemma 2.3 / eq. (11) | **proved**, axiom-free beyond the standard three | `DepthAspect/OldformSecondDifference.lean` (feature branch / PR) |
| B1 oldform decomposition | assumed | — |
| B3–B8 analytic inputs | assumed | — |
| B9 symmetry densities | dischargeable, not started | — |
| C1 Dirichlet GRH | intended hypothesis, never discharged | — |
| M1–M5 | open | — |
