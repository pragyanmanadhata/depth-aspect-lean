module

public import Mathlib.Data.Nat.Notation

/-!
# DepthAspect — conventions

The paper's family is the set of holomorphic newforms of weight `k` and level
`2^n`, with the *depth* `n → ∞`. This file fixes the little shared vocabulary
used across the project. Everything substantive lives in its own file (one
file per paper component); see `STATUS.md` for the map.

Project files use Lean's module system (`module`, `public import`,
`@[expose] public section`), as the pinned Mathlib does.
-/

@[expose] public section

namespace DepthAspect

/-- The level of depth `n` at the prime `2`, i.e. `2 ^ n`. -/
def level (n : ℕ) : ℕ := 2 ^ n

@[simp] theorem level_zero : level 0 = 1 := rfl

/-- `2 ^ (n + 1) = 2 * 2 ^ n`; the proof is `Nat.mul_comm` since `Nat.pow_succ` is definitional. -/
theorem level_succ (n : ℕ) : level (n + 1) = 2 * level n := Nat.mul_comm (2 ^ n) 2

theorem level_pos (n : ℕ) : 0 < level n := Nat.two_pow_pos n

end DepthAspect

end
