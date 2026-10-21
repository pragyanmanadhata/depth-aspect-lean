module

import DepthAspect.Basic
import DepthAspect.OldformSecondDifference

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

/-! ## eq. (11) / Lemma 2.3: the oldform second-difference identity -/

/-- info: 'DepthAspect.oldformTotal_second_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DepthAspect.oldformTotal_second_difference

/-- info: 'DepthAspect.oldformTotal_second_difference_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DepthAspect.oldformTotal_second_difference_complex

/-- info: 'DepthAspect.sum_second_difference_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DepthAspect.sum_second_difference_complex

/-- info: 'DepthAspect.oldformTotal_eq_sub_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DepthAspect.oldformTotal_eq_sub_cast

-- Helper (first difference), listed after the results it serves.
/-- info: 'DepthAspect.oldformTotal_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DepthAspect.oldformTotal_succ_sub
