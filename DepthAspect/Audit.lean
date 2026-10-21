module

import DepthAspect.Basic

/-!
# Axiom audit

Every completed result of the project is listed here with a `#guard_msgs`
check on `#print axioms`. The build fails if a result ever depends on
anything beyond the three standard axioms of Lean/Mathlib
(`propext`, `Classical.choice`, `Quot.sound`); in particular a `sorry`
(`sorryAx`) or any project-declared `axiom` breaks the build.

Add one block per completed theorem, in the order of `STATUS.md`.
-/

/-- info: 'DepthAspect.level_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms DepthAspect.level_succ

/-- info: 'DepthAspect.level_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms DepthAspect.level_pos
