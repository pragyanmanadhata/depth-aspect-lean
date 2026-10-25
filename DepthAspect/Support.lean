import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Support exponents in Sections 4, 5 and 7

These are proofs of the paper's choices of small parameters and the signs of all
error exponents. They do not assert the analytic estimates which precede them.
-/

namespace DepthAspect

/-- Equation (63), with all the inequalities used in (64). -/
theorem unsigned_parameter_choice {s η : ℝ}
    (hs : 0 < s) (hs' : s < 3 / 2)
    (hη : 0 < η) (hη' : η < 1 / 2) :
    let δ := η / (2 * (1 + s))
    0 < δ ∧ δ < 1 / 2 ∧ s * δ < η / 2 ∧
      -(3 / 2 : ℝ) + s * (1 + δ) ≤ s - 3 / 2 + η ∧
      -(3 / 2 : ℝ) + s * (1 / 2 + δ) ≤ -1 / 2 + η ∧
      -(1 / 2 : ℝ) + s * δ ≤ -1 / 2 + η := by
  dsimp only
  have hd : 0 < 2 * (1 + s) := by positivity
  have hδ : 0 < η / (2 * (1 + s)) := div_pos hη hd
  have hδ' : η / (2 * (1 + s)) < 1 / 2 := by
    apply (div_lt_iff₀ hd).2
    nlinarith
  have heq : η / (2 * (1 + s)) * (2 * (1 + s)) = η :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hprod : s * (η / (2 * (1 + s))) < η / 2 := by nlinarith
  refine ⟨hδ, hδ', hprod, ?_, ?_, ?_⟩ <;> nlinarith

/-- Exactly the two negative powers appearing in (42). -/
theorem unsigned_exponents_negative {s η : ℝ}
    (hη : η < min (1 / 2) (3 / 2 - s)) :
    s - 3 / 2 + η < 0 ∧ -(1 / 2 : ℝ) + η < 0 := by
  have h₁ := lt_of_lt_of_le hη (min_le_left _ _)
  have h₂ := lt_of_lt_of_le hη (min_le_right _ _)
  constructor <;> linarith

/-- A concrete admissible choice exists for every support strictly below 3/2. -/
theorem unsigned_parameter_exists {s : ℝ} (hs : s < 3 / 2) :
    ∃ η : ℝ, 0 < η ∧ η < min (1 / 2) (3 / 2 - s) := by
  have h : 0 < min (1 / 2 : ℝ) (3 / 2 - s) := lt_min (by norm_num) (by linarith)
  exact ⟨min (1 / 2) (3 / 2 - s) / 2, by positivity, by linarith⟩

/-- All four powers in (118) are negative under its stated hypotheses. -/
theorem signed_exponents_negative {s η : ℝ} (hs : 0 < s)
    (hη₁ : η < 1 - 3 * s / 4) (hη₂ : η < 1 / 2 - s / 4) :
    -1 + 3 * s / 4 + η < 0 ∧
    -(1 / 2 : ℝ) + s / 4 + η < 0 ∧
    -1 + s / 2 + η < 0 ∧
    -(1 / 2 : ℝ) + η < 0 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- A concrete admissible choice exists for every support strictly below 4/3. -/
theorem signed_parameter_exists {s : ℝ} (hs : s < 4 / 3) :
    ∃ η : ℝ, 0 < η ∧ η < 1 - 3 * s / 4 ∧ η < 1 / 2 - s / 4 := by
  have h₁ : 0 < 1 - 3 * s / 4 := by linarith
  have h₂ : 0 < (1 / 2 : ℝ) - s / 4 := by linarith
  refine ⟨min (1 - 3 * s / 4) (1 / 2 - s / 4) / 2, ?_, ?_, ?_⟩
  · exact div_pos (lt_min h₁ h₂) (by norm_num)
  · have := min_le_left (1 - 3 * s / 4) (1 / 2 - s / 4); linarith
  · have := min_le_right (1 - 3 * s / 4) (1 / 2 - s / 4); linarith

/-- The unsigned absolute-majorant method has the stated threshold. -/
theorem unsigned_support_threshold {a : ℝ} (ha : 0 < a) :
    (∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ -3 / 2 + a * (1 + δ) < 0) ↔
      a < 3 / 2 := by
  constructor
  · rintro ⟨δ, hδ, _, hexp⟩
    have := mul_pos ha hδ
    nlinarith
  · intro h
    let δ := min (1 / 4) ((3 / 2 - a) / (2 * a))
    have ha2 : 0 < 2 * a := by positivity
    have hd : 0 < δ := lt_min (by norm_num) (div_pos (by linarith) ha2)
    have hd₁ : δ ≤ 1 / 4 := min_le_left _ _
    have hd₂ : δ ≤ (3 / 2 - a) / (2 * a) := min_le_right _ _
    have hd₃ := (le_div_iff₀ ha2).1 hd₂
    exact ⟨δ, hd, by linarith, by nlinarith⟩

/-- The growing trace-index range imposes the signed threshold 4/3. -/
theorem signed_support_threshold (a : ℝ) :
    (∃ ε : ℝ, 0 < ε ∧ -1 + 3 * a / 4 + ε < 0) ↔ a < 4 / 3 := by
  constructor
  · rintro ⟨ε, hε, hexp⟩; linarith
  · intro ha
    refine ⟨(1 - 3 * a / 4) / 2, ?_, ?_⟩ <;> linarith

/-- With the proposed square-root prime-average error, the threshold becomes 2. -/
theorem improved_signed_support_threshold (a : ℝ) :
    (∃ ε : ℝ, 0 < ε ∧ -1 + a / 2 + ε < 0) ↔ a < 2 := by
  constructor
  · rintro ⟨ε, hε, hexp⟩; linarith
  · intro ha
    refine ⟨(1 - a / 2) / 2, ?_, ?_⟩ <;> linarith

end DepthAspect
