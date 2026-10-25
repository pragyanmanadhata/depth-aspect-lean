import DepthAspect.FiniteCharacterFourier

/-! Unit translation preserves the actual mean and Fourier coefficient norm. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace DepthAspect.FiniteCharacterTranslation
open FiniteCharacterFourier
variable {q : ℕ} [NeZero q]

 theorem coefficient_translate_relation (g : (ZMod q)ˣ → ℂ)
    (u : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    coefficient g χ = conj (χ u) * coefficient (fun x => g (u * x)) χ := by
  unfold coefficient
  rw [← Equiv.sum_comp (Equiv.mulLeft u)]
  simp only [Equiv.coe_mulLeft, Units.val_mul, map_mul]
  calc
    _ = (∑ x : (ZMod q)ˣ, conj (χ u) * (g (u * x) * conj (χ x))) /
        Fintype.card (ZMod q)ˣ := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by rw [← Finset.mul_sum, mul_div_assoc]

 theorem principal_translate (g : (ZMod q)ˣ → ℂ) (u : (ZMod q)ˣ) :
    coefficient (fun x => g (u * x)) 1 = coefficient g 1 := by
  simpa using (coefficient_translate_relation g u 1).symm

 theorem norm_coefficient_translate (g : (ZMod q)ˣ → ℂ)
    (u : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    ‖coefficient (fun x => g (u * x)) χ‖ = ‖coefficient g χ‖ := by
  rw [coefficient_translate_relation g u χ, norm_mul, Complex.norm_conj,
    χ.unit_norm_eq_one u, one_mul]

 theorem beta_translate (g : (ZMod q)ˣ → ℂ) (u : (ZMod q)ˣ) :
    beta (fun x => g (u * x)) = beta g := by
  unfold beta
  simp only [norm_coefficient_translate]

end DepthAspect.FiniteCharacterTranslation
