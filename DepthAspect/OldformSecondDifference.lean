module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The oldform second-difference identity (finite-sum engine of Lemma 2.3)

Let `G : ℕ → ℂ` and define the *oldform-weighted total*

  `F n = ∑_{a = 0}^{n} (n - a + 1) · G a`.

This is the shape of the Atkin–Lehner oldform decomposition for the level
`2^n`: if `G a` is the dimension of the newform space of level `2^a`, then
`F n` is the dimension of the full space of level `2^n`, because a newform of
level `2^a` contributes `σ₀(2^{n-a}) = n - a + 1` oldforms at level `2^n`.

The main result, `oldformTotal_second_difference`, is the purely
combinatorial statement that the second backward difference of `F`
recovers `G`:

  `F (n+2) - 2 F (n+1) + F n = G (n+2)`.

This is the finite-sum identity behind equation (11) of the paper and the
proof of Lemma 2.3. The *analytic* input (that `G` and `F` really are the
newform and full-space dimensions, i.e. the oldform decomposition itself) is
deliberately **not** part of this file; see `DEPENDENCIES.md`, item B1.

The identity holds in any commutative ring, so it is proved for a general
`CommRing R` and then specialised to `ℂ`.
-/

@[expose] public section

open Finset

namespace DepthAspect

section Generic

variable {R : Type*} [CommRing R]

/-- The oldform-weighted total `F n = ∑_{a=0}^{n} (n - a + 1) * G a`.

The coefficient is formed in `ℕ` (where `n - a` is an honest subtraction
because `a ≤ n` inside the sum) and then cast into `R`; see
`oldformTotal_eq_sub_cast` for the equivalent form with the subtraction
performed in `R`. -/
def oldformTotal (G : ℕ → R) (n : ℕ) : R :=
  ∑ a ∈ range (n + 1), ((n - a + 1 : ℕ) : R) * G a

/-- Sanity check on the cast: inside the sum `a ≤ n`, so the truncated
natural-number subtraction agrees with subtraction in `R`. -/
theorem oldformTotal_eq_sub_cast (G : ℕ → R) (n : ℕ) :
    oldformTotal G n = ∑ a ∈ range (n + 1), ((n : R) - a + 1) * G a := by
  unfold oldformTotal
  refine sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
  push_cast [Nat.cast_sub ha']
  ring

/-- First backward difference: `F (n+1) - F n = ∑_{a=0}^{n+1} G a`. -/
theorem oldformTotal_succ_sub (G : ℕ → R) (n : ℕ) :
    oldformTotal G (n + 1) - oldformTotal G n = ∑ a ∈ range (n + 1 + 1), G a := by
  unfold oldformTotal
  rw [sum_range_succ (fun a => ((n + 1 - a + 1 : ℕ) : R) * G a) (n + 1),
    sum_range_succ G (n + 1)]
  have h : ∑ a ∈ range (n + 1), ((n + 1 - a + 1 : ℕ) : R) * G a
      = ∑ a ∈ range (n + 1), (((n - a + 1 : ℕ) : R) * G a + G a) := by
    refine sum_congr rfl fun a ha => ?_
    have ha' : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [Nat.sub_add_comm ha']
    push_cast
    ring
  rw [h, sum_add_distrib, Nat.sub_self]
  push_cast
  ring

/-- **Second backward difference recovers `G`** (generic version):
`F (n+2) - 2 F (n+1) + F n = G (n+2)`. -/
theorem oldformTotal_second_difference (G : ℕ → R) (n : ℕ) :
    oldformTotal G (n + 2) - 2 * oldformTotal G (n + 1) + oldformTotal G n = G (n + 2) := by
  have h₁ := oldformTotal_succ_sub G (n + 1)
  have h₂ := oldformTotal_succ_sub G n
  rw [sum_range_succ G (n + 1 + 1), ← h₂] at h₁
  show oldformTotal G (n + 1 + 1) - 2 * oldformTotal G (n + 1) + oldformTotal G n = G (n + 1 + 1)
  linear_combination h₁

end Generic

section Complex

/-- The requested statement over `ℂ`: for `G : ℕ → ℂ` and
`F n = ∑_{a=0}^{n} (n - a + 1) · G a` (coefficients cast into `ℂ`),

  `F (n+2) - 2 F (n+1) + F n = G (n+2)` for every `n`. -/
theorem oldformTotal_second_difference_complex (G : ℕ → ℂ) (n : ℕ) :
    oldformTotal G (n + 2) - 2 * oldformTotal G (n + 1) + oldformTotal G n = G (n + 2) :=
  oldformTotal_second_difference G n

/-- The same statement with the definition of `F` unfolded, so that the
theorem can be read without reference to `oldformTotal`. -/
theorem sum_second_difference_complex (G : ℕ → ℂ) (n : ℕ) :
    (∑ a ∈ range (n + 2 + 1), ((n + 2 - a + 1 : ℕ) : ℂ) * G a)
      - 2 * (∑ a ∈ range (n + 1 + 1), ((n + 1 - a + 1 : ℕ) : ℂ) * G a)
      + (∑ a ∈ range (n + 1), ((n - a + 1 : ℕ) : ℂ) * G a) = G (n + 2) :=
  oldformTotal_second_difference_complex G n

end Complex

end DepthAspect

end
