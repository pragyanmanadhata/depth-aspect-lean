import DepthAspect.Support
import Mathlib.Tactic.FieldSimp

/-! Exact support thresholds in the last paragraph of Section 7. These
statements describe the exponents of the proved bounds; they do not assert
that the true density theorem fails at or above those thresholds. -/
namespace DepthAspect.SectionSevenConditionalSupport

/-- The two errors in (141) admit a positive loss with negative level
exponents exactly for support below 4/3. -/
theorem current_support_threshold {a : ℝ} (ha : 0 < a) :
    (∃ ε : ℝ, 0 < ε ∧
      -1 / 2 + a * (1 / 4 + ε) < 0 ∧
      -1 + a * (3 / 4 + ε) < 0) ↔ a < 4 / 3 := by
  constructor
  · rintro ⟨ε, hε, _, hsecond⟩
    nlinarith [mul_pos ha hε]
  · intro ha'
    let ε : ℝ := (4 - 3 * a) / (8 * a)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    have he : a * ε = (4 - 3 * a) / 8 := by
      dsimp [ε]
      field_simp [ha.ne']
    refine ⟨ε, hε, ?_, ?_⟩ <;> nlinarith

/-- The first term of (141) by itself allows every fixed support below
two, and has no negative exponent with a positive loss at or above two. -/
theorem first_term_threshold {a : ℝ} (ha : 0 < a) :
    (∃ ε : ℝ, 0 < ε ∧ -1 / 2 + a * (1 / 4 + ε) < 0) ↔ a < 2 := by
  constructor
  · rintro ⟨ε, hε, he⟩
    nlinarith [mul_pos ha hε]
  · intro ha'
    let ε : ℝ := (2 - a) / (8 * a)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    have he : a * ε = (2 - a) / 8 := by
      dsimp [ε]
      field_simp [ha.ne']
    refine ⟨ε, hε, ?_⟩
    nlinarith

/-- With the hypothetical B^(1/2+ε) prime-average estimate, both resulting
block exponents are negative exactly for support below two. -/
theorem improved_support_threshold {a : ℝ} (ha : 0 < a) :
    (∃ ε : ℝ, 0 < ε ∧ -1 / 2 + a * ε < 0 ∧
      -1 + a * (1 / 2 + ε) < 0) ↔ a < 2 := by
  constructor
  · rintro ⟨ε, hε, _, hsecond⟩
    nlinarith [mul_pos ha hε]
  · intro ha'
    let ε : ℝ := (2 - a) / (4 * a)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    have he : a * ε = (2 - a) / 4 := by
      dsimp [ε]
      field_simp [ha.ne']
    refine ⟨ε, hε, ?_, ?_⟩ <;> nlinarith

/-- The square-term exponents in (116) allow every fixed support below
two. Thus they do not impose the stricter 4/3 threshold. -/
theorem square_terms_below_two {a : ℝ} (ha : 0 < a) (ha' : a < 2) :
    ∃ η : ℝ, 0 < η ∧ -1 + a / 2 + η < 0 ∧ -1 / 2 + η < 0 := by
  refine ⟨(2 - a) / 4, by linarith, ?_, ?_⟩ <;> linarith

end DepthAspect.SectionSevenConditionalSupport
