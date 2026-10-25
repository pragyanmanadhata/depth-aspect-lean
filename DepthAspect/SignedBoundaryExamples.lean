import DepthAspect.SignedArithmeticData

/-! # The weight-two sign-class exceptions at depths five and six -/
namespace DepthAspect.SignedSieve.SignedArithmeticData

open scoped BigOperators

variable {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)] [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem weight_two_depth_five (S : SignedArithmeticData 0 Family Full New) :
    Fintype.card (Family (2 ^ 5)) = 1 ∧
    (∑ f, S.rootNumber (2 ^ 5) f) = 1 ∧
    (S.signClass (2 ^ 5) (-1)).card = 0 := by
  have hd := MartinDimension.dimension_odd 2 2 (by decide)
    (fun N => (Fintype.card (Family N) : ℝ)) S.unsigned.dimension_formula
  norm_num [oddDimension] at hd
  have hR := S.rootNumber_sum_odd 2 (by decide)
  norm_num at hR
  have hc := S.signClass_card (2 ^ 5) (-1) (Or.inr rfl)
  norm_num [hd, hR] at hc
  refine ⟨by exact_mod_cast hd, hR, ?_⟩
  simp only [hc, Finset.card_empty]

theorem weight_two_depth_six (S : SignedArithmeticData 0 Family Full New) :
    Fintype.card (Family (2 ^ 6)) = 1 ∧
    (∑ f, S.rootNumber (2 ^ 6) f) = 1 ∧
    (S.signClass (2 ^ 6) (-1)).card = 0 := by
  have hd := MartinDimension.dimension_even 2 3 (by decide)
    (fun N => (Fintype.card (Family N) : ℝ)) S.unsigned.dimension_formula
  norm_num [evenDimension] at hd
  have hR := S.rootNumber_sum_even 3 (by decide)
  norm_num at hR
  have hc := S.signClass_card (2 ^ 6) (-1) (Or.inr rfl)
  norm_num [hd, hR] at hc
  refine ⟨by exact_mod_cast hd, hR, ?_⟩
  simp only [hc, Finset.card_empty]

end DepthAspect.SignedSieve.SignedArithmeticData
