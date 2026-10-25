import DepthAspect.TraceBounds
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The zeta notation in the explicit trace constant

This identifies the literal convergent positive majorant series with the
Riemann zeta function in equation (34); no zeta value is assumed.
-/
namespace DepthAspect.TraceBounds

theorem zetaMajorant_eq_riemannZeta (δ : ℝ) (hδ : 0 < δ) :
    (zetaMajorant δ : ℂ) = riemannZeta ((1 + 2 * δ : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using (show 1 < 1 + 2 * δ by linarith))]
  unfold zetaMajorant
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  rw [show -1 - 2 * δ = -(1 + 2 * δ) by ring,
    Real.rpow_neg hn, Complex.ofReal_inv, Complex.ofReal_cpow hn]
  push_cast <;> simp only [one_div]

theorem zetaMajorant_eq_riemannZeta_re (δ : ℝ) (hδ : 0 < δ) :
    zetaMajorant δ = (riemannZeta ((1 + 2 * δ : ℝ) : ℂ)).re := by
  exact congrArg Complex.re (zetaMajorant_eq_riemannZeta δ hδ)

theorem ellipticConstant_eq_zeta (Ccl δ : ℝ) (hδ : 0 < δ) :
    ellipticConstant Ccl δ =
      512 * (4 : ℝ) ^ (1 / 2 + δ) * Ccl *
        (riemannZeta ((1 + 2 * δ : ℝ) : ℂ)).re /
        (1 - (2 : ℝ) ^ (-1 / 2 - 2 * δ)) := by
  rw [ellipticConstant, zetaMajorant_eq_riemannZeta_re δ hδ]
  simp only [decayRatio, show -(1 / 2 + 2 * δ) = -1 / 2 - 2 * δ by ring]

end DepthAspect.TraceBounds
