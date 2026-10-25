import DepthAspect.LocalCancellation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sum-first presentation of the elliptic support cutoff

This module presents `LocalCancellation.weighted_local_cancellation` in the
paper's notation: first form the finite elliptic weight `Xi_n`, then take its
second difference. All summands are the actual projective root counts.
The identification with Popa's elliptic weights remains the external
trace-formula interface and is not asserted by this module.
-/

open scoped BigOperators
namespace DepthAspect.EllipticSupport
open ContentReduction

/-- A finite elliptic weight built from actual two-chart counts. Arbitrary
commutative-ring weights include the real weighted primitive class numbers. -/
noncomputable def ellipticWeight {ι R : Type*} [CommRing R]
    (s : Finset ι) (w : ι → R) (e : ι → ℕ) (A B C : ι → ℤ) (n : ℕ) : R :=
  ∑ i ∈ s, w i * (rho n (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : R)

/-- Corollary 3.2 in sum-first form. The substantive local cancellation is
proved in `LocalCancellation`; only finite-sum algebra is added here. -/
theorem elliptic_second_difference_eq_zero
    {ι R : Type*} [CommRing R]
    (s : Finset ι) (w : ι → R) (e : ι → ℕ) (A B C : ι → ℤ)
    (n : ℕ) (hn : 2 ≤ n) (D : ℤ)
    (hprim : ∀ i ∈ s, Odd (A i) ∨ Odd (B i) ∨ Odd (C i))
    (hdisc : ∀ i ∈ s,
      D = (2 : ℤ) ^ (2 * e i) * ((B i) ^ 2 - 4 * A i * C i))
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ D) :
    ellipticWeight s w e A B C n - 2 * ellipticWeight s w e A B C (n - 1) +
      ellipticWeight s w e A B C (n - 2) = 0 := by
  have hscaled : ∀ i ∈ s,
      (2 ^ e i * B i) ^ 2 - 4 * (2 ^ e i * A i) * (2 ^ e i * C i) = D := by
    intro i hi
    rw [LocalCancellation.scaled_discriminant, ← hdisc i hi]
  have hc := LocalCancellation.weighted_local_cancellation s w e A B C n hn D hprim hscaled hbad
  push_cast at hc
  calc
    _ = ∑ i ∈ s, w i *
        ((rho n (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : R) -
        2 * (rho (n - 1) (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : R) +
        (rho (n - 2) (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : R)) := by
      unfold ellipticWeight
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := hc

/-- A nonzero elliptic second difference forces the common discriminant to be
divisible by `2^(n−2)`, which is `N/4` at level `N=2^n`. -/
theorem elliptic_second_difference_support
    {ι R : Type*} [CommRing R]
    (s : Finset ι) (w : ι → R) (e : ι → ℕ) (A B C : ι → ℤ)
    (n : ℕ) (hn : 2 ≤ n) (D : ℤ)
    (hprim : ∀ i ∈ s, Odd (A i) ∨ Odd (B i) ∨ Odd (C i))
    (hdisc : ∀ i ∈ s,
      D = (2 : ℤ) ^ (2 * e i) * ((B i) ^ 2 - 4 * A i * C i))
    (hnonzero : ellipticWeight s w e A B C n -
      2 * ellipticWeight s w e A B C (n - 1) + ellipticWeight s w e A B C (n - 2) ≠ 0) :
    (2 : ℤ) ^ (n - 2) ∣ D := by
  by_contra hbad
  exact hnonzero (elliptic_second_difference_eq_zero s w e A B C n hn D hprim hdisc hbad)

end DepthAspect.EllipticSupport
