import DepthAspect.UniformSpectralPrimeBounds
import DepthAspect.SignedTraceBound
import DepthAspect.SignedFamilyCounts

/-!
# Shared unsigned and signed arithmetic spectral data

The finite family and normalized eigenvalues are exactly those used by the
unsigned density theorem. Its full oldform space and the newspace below are
separate vector spaces. Added fields are the standard Fricke eigenvector
normalization, root signs, and cited general signed trace and quadratic
class-number identities. No specialized sign count or trace estimate is a
field, and the Hecke identity at one is derived from the basis.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

structure SignedArithmeticData (r : ℕ) (Family Full New : ℕ → Type*)
    [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
    [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)] where
  unsigned : UnsignedDensity.ArithmeticSpectralData (2 * r) Family Full
  rootNumber : ∀ N, Family N → ℝ
  rootNumber_sign : ∀ N f, rootNumber N f = 1 ∨ rootNumber N f = -1
  newOperator : ∀ N, ℕ → New N →ₗ[ℂ] New N
  fricke : ∀ N, New N →ₗ[ℂ] New N
  newBasis : ∀ N, 0 < N → Module.Basis (Family N) ℂ (New N)
  newEigenvector : ∀ N (hN : 0 < N) m, 0 < m → Nat.Coprime m N → ∀ f,
    newOperator N m (newBasis N hN f) =
      ((((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * unsigned.eigenvalues N f m) •
        newBasis N hN f
  frickeEigenvector : ∀ N (hN : 0 < N) f,
    fricke N (newBasis N hN f) =
      ((-1 : ℂ) ^ (r + 1) * (rootNumber N f : ℂ)) • newBasis N hN f
  signed_trace_formula : GeneralSignedTraceFormula r unsigned.hurwitzClass New newOperator fricke
  quadratic_class_formula : QuadraticClassFormula.GeneralFormula unsigned.hurwitzClass

namespace SignedArithmeticData

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- The actual sign filter inside the shared finite family. -/
noncomputable def signClass (S : SignedArithmeticData r Family Full New)
    (N : ℕ) (σ : ℝ) : Finset (Family N) :=
  Finset.univ.filter (fun f => S.rootNumber N f = σ)

noncomputable def signAverage (S : SignedArithmeticData r Family Full New)
    (N : ℕ) (σ : ℝ) (X : Family N → ℂ) : ℂ :=
  (∑ f ∈ S.signClass N σ, X f) / ((S.signClass N σ).card : ℂ)

/-- The paper's A_P includes the factor sqrt P. The unscaled signed
Hecke sum is kept separate to make the normalization explicit. -/
noncomputable def primeSignedTrace (S : SignedArithmeticData r Family Full New)
    (N P : ℕ) : ℂ :=
  (Real.sqrt P : ℂ) * signedHeckeSum (fun f => (S.rootNumber N f : ℂ))
    (S.unsigned.eigenvalues N) P

theorem primeSignedTrace_eq_expression (S : SignedArithmeticData r Family Full New)
    (n P : ℕ) (hP : 0 < P) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ n) P =
      (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
        newSignedExpression (2 * r) (2 ^ n) P S.unsigned.hurwitzClass /
          (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) := by
  have hcop : Nat.Coprime P (2 ^ n) := hodd.coprime_two_right.pow_right n
  have h := signedHeckeSum_eq_trace r P hP (S.newBasis _ (by positivity))
    (S.newOperator (2 ^ n) P) (S.fricke (2 ^ n))
    (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (S.unsigned.eigenvalues (2 ^ n))
    (S.newEigenvector _ (by positivity) P hP hcop) (S.frickeEigenvector _ (by positivity))
  rw [S.signed_trace_formula.trace_formula _ P (by positivity) hP hcop] at h
  unfold primeSignedTrace
  rw [h]
  ring

/-- The sign-family cardinality is derived from its literal filter. -/
theorem signClass_card (S : SignedArithmeticData r Family Full New)
    (N : ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    2 * ((S.signClass N σ).card : ℝ) =
      (Fintype.card (Family N) : ℝ) + σ * (∑ f, S.rootNumber N f) := by
  simpa only [signClass, Finset.card_univ] using
    twice_sign_card (Finset.univ : Finset (Family N)) (S.rootNumber N) σ hσ
      (fun f _ => S.rootNumber_sign N f)

/-- T₁=id is a consequence of the shared normalized eigenvalue-one
identity and the complete newspace basis. -/
theorem newOperator_one (S : SignedArithmeticData r Family Full New)
    (N : ℕ) (hN : 0 < N) : S.newOperator N 1 = LinearMap.id := by
  apply (S.newBasis N hN).ext
  intro f
  have h := S.newEigenvector N hN 1 (by decide) (by simp) f
  simpa only [Nat.cast_one, Real.one_rpow, Complex.ofReal_one,
    S.unsigned.normalized_one, mul_one, one_smul, LinearMap.id_apply] using h

/-- The actual root-number sum is the evaluated even-depth class trace. -/
theorem rootNumber_sum_even (S : SignedArithmeticData r Family Full New)
    (a : ℕ) (ha : 3 ≤ a) :
    (∑ f, S.rootNumber (2 ^ (2 * a)) f) = (2 : ℝ) ^ (a - 3) := by
  have h := real_rootNumberSum_from_general_formula Family New r (2 * a)
    (by omega) S.unsigned.hurwitzClass S.newOperator S.fricke S.signed_trace_formula
    S.newOperator_one (S.rootNumber (2 ^ (2 * a))) (S.newBasis _ (by positivity))
    (S.frickeEigenvector _ (by positivity))
  rw [SignedClassNumbers.indexOneClassTrace_even _ S.quadratic_class_formula.minus_four a ha] at h
  exact h

/-- The odd-depth index-one count, including depth seven. -/
theorem rootNumber_sum_odd (S : SignedArithmeticData r Family Full New)
    (a : ℕ) (ha : 2 ≤ a) :
    (∑ f, S.rootNumber (2 ^ (2 * a + 1)) f) = (2 : ℝ) ^ (a - 2) := by
  have h := real_rootNumberSum_from_general_formula Family New r (2 * a + 1)
    (by omega) S.unsigned.hurwitzClass S.newOperator S.fricke S.signed_trace_formula
    S.newOperator_one (S.rootNumber (2 ^ (2 * a + 1))) (S.newBasis _ (by positivity))
    (S.frickeEigenvector _ (by positivity))
  rw [SignedClassNumbers.indexOneClassTrace_odd _ S.quadratic_class_formula.minus_eight a ha] at h
  exact h

theorem even_signClass_nonempty (S : SignedArithmeticData r Family Full New)
    (a : ℕ) (ha : 4 ≤ a) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (Finset.univ.filter (fun f => S.rootNumber (2 ^ (2 * a)) f = σ)).Nonempty := by
  classical
  exact even_signClass_nonempty_from_general_inputs Family New r a ha
    S.unsigned.hurwitzClass S.newOperator S.fricke S.signed_trace_formula
    S.newOperator_one S.unsigned.dimension_formula S.quadratic_class_formula
    (S.rootNumber _) (S.newBasis _ (by positivity))
    (S.frickeEigenvector _ (by positivity)) (S.rootNumber_sign _) σ hσ

theorem odd_signClass_nonempty (S : SignedArithmeticData r Family Full New)
    (a : ℕ) (ha : 3 ≤ a) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (Finset.univ.filter (fun f => S.rootNumber (2 ^ (2 * a + 1)) f = σ)).Nonempty := by
  classical
  exact odd_signClass_nonempty_from_general_inputs Family New r a ha
    S.unsigned.hurwitzClass S.newOperator S.fricke S.signed_trace_formula
    S.newOperator_one S.unsigned.dimension_formula S.quadratic_class_formula
    (S.rootNumber _) (S.newBasis _ (by positivity))
    (S.frickeEigenvector _ (by positivity)) (S.rootNumber_sign _) σ hσ

/-- Both actual sign filters are nonempty throughout the paper's range,
including n=7 and weight two. -/
theorem signClass_nonempty (S : SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (S.signClass (2 ^ n) σ).Nonempty := by
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨a, ha⟩ := heven
    have heq : n = 2 * a := by omega
    rw [heq] at hn ⊢
    exact S.even_signClass_nonempty a (by omega) σ hσ
  · obtain ⟨a, ha⟩ := hodd
    have heq : n = 2 * a + 1 := by omega
    rw [heq] at hn ⊢
    exact S.odd_signClass_nonempty a (by omega) σ hσ

/-- Exact projection (119) for complex-valued observations on the same
family as the unsigned result. Denominators are justified by the proved
nonemptiness of the literal sign filters. -/
theorem signAverage_projection (S : SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (X : Family (2 ^ n) → ℂ) :
    S.signAverage (2 ^ n) σ X =
      (SpectralFamily.average X + (σ : ℂ) *
        SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) * X f)) /
      (1 + (σ : ℂ) * SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ))) := by
  classical
  have hσC : (σ : ℂ) = 1 ∨ (σ : ℂ) = -1 := by
    rcases hσ with h | h <;> simp [h]
  have hεC : ∀ f ∈ (Finset.univ : Finset (Family (2 ^ n))),
      (S.rootNumber (2 ^ n) f : ℂ) = 1 ∨ (S.rootNumber (2 ^ n) f : ℂ) = -1 := by
    intro f hf
    rcases S.rootNumber_sign (2 ^ n) f with h | h <;> simp [h]
  have hfilter : (Finset.univ.filter
      (fun f => (S.rootNumber (2 ^ n) f : ℂ) = (σ : ℂ))) = S.signClass (2 ^ n) σ := by
    ext f
    simp [signClass]
  have hsign := S.signClass_nonempty n hn σ hσ
  have hall : (Finset.univ : Finset (Family (2 ^ n))).Nonempty :=
    hsign.mono (Finset.filter_subset _ _)
  have h := complex_sign_family_average (Finset.univ : Finset (Family (2 ^ n)))
    (fun f => (S.rootNumber (2 ^ n) f : ℂ)) X (σ : ℂ) hσC hεC hall
    (by rw [hfilter]; exact hsign)
  simpa only [signAverage, hfilter, Finset.card_univ, SpectralFamily.average] using h

/-- Lemma 5.1 for the same literal finite family used by the unsigned
density result, with every internal trace-size input discharged. -/
theorem signed_square_bound (S : SignedArithmeticData r Family Full New)
    (n p : ℕ) (hn : 7 ≤ n) (hp : p.Prime) (hodd : Odd p) (δ : ℝ) (hδ : 0 < δ) :
    ‖signedHeckeSum (fun f => (S.rootNumber (2 ^ n) f : ℂ))
      (S.unsigned.eigenvalues (2 ^ n)) (p ^ 2)‖ ≤
      48 * ((2 * r + 1 : ℕ) : ℝ) * TraceBounds.uniformClassConstant δ *
        (4 : ℝ) ^ (1 / 2 + δ) *
        (((2 : ℝ) ^ n) ^ (1 / 2 + δ) * (p : ℝ) ^ (2 * δ) +
          ((2 : ℝ) ^ n) ^ δ * (p : ℝ) ^ (1 + 2 * δ)) := by
  have hcop : Nat.Coprime (p ^ 2) (2 ^ n) := hodd.coprime_two_right.pow 2 n
  exact signedHeckeSum_prime_square_bound_from_general_inputs New r n p hn hp hodd
    S.newOperator S.fricke (S.newBasis _ (by positivity))
    (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (S.unsigned.eigenvalues (2 ^ n))
    (S.newEigenvector _ (by positivity) _ (pow_pos hp.pos 2) hcop)
    (S.frickeEigenvector _ (by positivity)) S.unsigned.primitiveClass S.unsigned.hurwitzClass
    S.signed_trace_formula S.unsigned.primitive_nonneg S.unsigned.primitive_decomposition
    S.unsigned.ordered_class_number_formula δ hδ

end SignedArithmeticData
end DepthAspect.SignedSieve
