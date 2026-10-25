import DepthAspect.SignedIndexOneTrace
import DepthAspect.SignedClassNumbers
import DepthAspect.QuadraticClassFormula
import DepthAspect.MartinDimension
import DepthAspect.Algebra

/-!
# Actual root-sign counts from general trace and dimension identities

The sign sum is derived from the cited general Skoruppa–Zagier identity,
the simultaneous eigenbasis, and the general class-number identity. The
finite sign classes are then proved nonempty using the exact general Martin
specialization, including the depth-seven boundary.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators
open SignedClassNumbers QuadraticCharacterValues DyadicClassScaling

/-- The real root-number sum is the actual three-class-number expression. -/
theorem real_rootNumberSum_from_general_formula
    (Family V : ℕ → Type*) [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (r n : ℕ) (hn : 5 ≤ n) (H : ℤ → ℝ)
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N)
    (hSZ : GeneralSignedTraceFormula r H V T W)
    (hT1 : ∀ N, 0 < N → T N 1 = LinearMap.id)
    (ε : Family (2 ^ n) → ℝ) (b : Module.Basis (Family (2 ^ n)) ℂ (V (2 ^ n)))
    (hW : ∀ f, W (2 ^ n) (b f) =
      ((-1 : ℂ) ^ (r + 1) * (ε f : ℂ)) • b f) :
    (∑ f, ε f) = indexOneClassTrace H n := by
  have h := rootNumberSum_from_general_formula Family V r n hn H T W hSZ hT1
    (fun f => (ε f : ℂ)) b hW
  apply Complex.ofReal_injective
  unfold indexOneClassTrace
  push_cast
  exact h

/-- An actual finite sign class is nonempty once the proved total sign
sum has magnitude at most half of the positive total cardinality. -/
theorem signClass_nonempty_of_balance {ι : Type*} [Fintype ι] (ε : ι → ℝ)
    (hε : ∀ f, ε f = 1 ∨ ε f = -1) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hd : (0 : ℝ) < Fintype.card ι)
    (hR : |∑ f, ε f| ≤ (Fintype.card ι : ℝ) / 2) :
    (Finset.univ.filter (fun f => ε f = σ)).Nonempty := by
  classical
  have hc := twice_sign_card (Finset.univ : Finset ι) ε σ hσ (fun f _ => hε f)
  simp only [Finset.card_univ] at hc
  have hpos := both_sign_dimensions_positive (Fintype.card ι : ℝ) (∑ f, ε f) hd hR
  have hp : (0 : ℝ) < (Finset.univ.filter (fun f => ε f = σ)).card := by
    rcases hσ with rfl | rfl
    · simp only [one_mul] at hc
      linarith [hpos.1]
    · simp only [neg_one_mul] at hc
      linarith [hpos.2]
  exact Finset.card_pos.mp (by exact_mod_cast hp)

/-- Exact even-depth sign classes are nonempty from the general Martin and
signed/class-number formulas, without assuming any sign-balance estimate. -/
theorem even_signClass_nonempty_from_general_inputs
    (Family V : ℕ → Type*) [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (r a : ℕ) (ha : 4 ≤ a) (H : ℤ → ℝ)
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N)
    (hSZ : GeneralSignedTraceFormula r H V T W)
    (hT1 : ∀ N, 0 < N → T N 1 = LinearMap.id)
    (hMartin : MartinDimension.SatisfiesMartinFormula (2 * r + 2)
      (fun N => (Fintype.card (Family N) : ℝ)))
    (hClass : QuadraticClassFormula.GeneralFormula H)
    (ε : Family (2 ^ (2 * a)) → ℝ)
    (b : Module.Basis (Family (2 ^ (2 * a))) ℂ (V (2 ^ (2 * a))))
    (hW : ∀ f, W (2 ^ (2 * a)) (b f) =
      ((-1 : ℂ) ^ (r + 1) * (ε f : ℂ)) • b f)
    (hε : ∀ f, ε f = 1 ∨ ε f = -1) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (Finset.univ.filter (fun f => ε f = σ)).Nonempty := by
  have hR := real_rootNumberSum_from_general_formula Family V r (2 * a)
    (by omega) H T W hSZ hT1 ε b hW
  rw [indexOneClassTrace_even H hClass.minus_four a (by omega)] at hR
  have hd := MartinDimension.dimension_even (2 * r + 2) a (by omega)
    (fun N => (Fintype.card (Family N) : ℝ)) hMartin
  have hq : (16 : ℝ) ≤ 2 ^ a := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h
    exact h
  have hk : (2 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 2 * r + 2 by omega)
  have hRvalue : (2 : ℝ) ^ (a - 3) = evenImbalance ((2 : ℝ) ^ a) := by
    unfold evenImbalance
    conv_rhs => rw [show a = (a - 3) + 3 by omega, pow_add]
    norm_num
  apply signClass_nonempty_of_balance ε hε σ hσ
  · rw [hd]
    exact even_dimension_pos _ _ hk hq
  · rw [hR, abs_of_pos (by positivity), hRvalue, hd]
    exact even_imbalance_le_half _ _ hk hq

/-- Odd depth starts at seven; the boundary k=2,n=7 follows from the exact
formula and therefore does not rely on an insufficient coarse estimate. -/
theorem odd_signClass_nonempty_from_general_inputs
    (Family V : ℕ → Type*) [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (r a : ℕ) (ha : 3 ≤ a) (H : ℤ → ℝ)
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N)
    (hSZ : GeneralSignedTraceFormula r H V T W)
    (hT1 : ∀ N, 0 < N → T N 1 = LinearMap.id)
    (hMartin : MartinDimension.SatisfiesMartinFormula (2 * r + 2)
      (fun N => (Fintype.card (Family N) : ℝ)))
    (hClass : QuadraticClassFormula.GeneralFormula H)
    (ε : Family (2 ^ (2 * a + 1)) → ℝ)
    (b : Module.Basis (Family (2 ^ (2 * a + 1))) ℂ (V (2 ^ (2 * a + 1))))
    (hW : ∀ f, W (2 ^ (2 * a + 1)) (b f) =
      ((-1 : ℂ) ^ (r + 1) * (ε f : ℂ)) • b f)
    (hε : ∀ f, ε f = 1 ∨ ε f = -1) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (Finset.univ.filter (fun f => ε f = σ)).Nonempty := by
  have hR := real_rootNumberSum_from_general_formula Family V r (2 * a + 1)
    (by omega) H T W hSZ hT1 ε b hW
  rw [indexOneClassTrace_odd H hClass.minus_eight a (by omega)] at hR
  have hd := MartinDimension.dimension_odd (2 * r + 2) a (by omega)
    (fun N => (Fintype.card (Family N) : ℝ)) hMartin
  have hq : (8 : ℝ) ≤ 2 ^ a := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h
    exact h
  have hk : (2 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ 2 * r + 2 by omega)
  have hRvalue : (2 : ℝ) ^ (a - 2) = oddImbalance ((2 : ℝ) ^ a) := by
    unfold oddImbalance
    conv_rhs => rw [show a = (a - 2) + 2 by omega, pow_add]
    norm_num
  apply signClass_nonempty_of_balance ε hε σ hσ
  · rw [hd]
    exact odd_dimension_pos _ _ hk (by positivity)
  · rw [hR, abs_of_pos (by positivity), hRvalue, hd]
    exact odd_imbalance_le_half _ _ hk hq

end DepthAspect.SignedSieve
