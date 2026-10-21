module

import DepthAspect.Basic

/-!
# Axiom audit

Every completed result of the project is listed here with a `#guard_msgs`
check on `#print axioms`. The build fails if a result ever depends on
anything beyond the three standard axioms of Lean/Mathlib
(`propext`, `Classical.choice`, `Quot.sound`); in particular an unfinished
proof (which would add the axiom `sorryAx`) or any project-declared axiom
breaks the build.

Add one block per completed theorem, following the order of `STATUS.md`,
with helper lemmas listed after the results they serve.
-/

/-- info: 'DepthAspect.level_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms DepthAspect.level_zero

/-- info: 'DepthAspect.level_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms DepthAspect.level_succ

/-- info: 'DepthAspect.level_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms DepthAspect.level_pos
