import DepthAspect.DirichletRH
import DepthAspect.PrimitiveGRHTransport
import DepthAspect.ImprimitiveSmoothing

/-!
# The cited general implications of primitive Dirichlet RH

The zero-location assumption and the two cited analytic theorems are distinct
inputs. The estimates concern all primitive characters before any trace index,
discriminant, local coefficient function, or test weight is selected. Their
constants are uniform in the modulus and character. No internal paper result
(81)–(105) is included among the fields of this package.
-/
namespace DepthAspect.GRHConsequences
open DirichletRH PrimitiveGRHTransport ImprimitiveSmoothing

/-- External general analytic theorems cited as IK Theorem 5.15 and
Corollary 5.20, in the exact uniform forms used by the paper. These are theorem
implications from the actual zero-location hypothesis, not alternative
definitions of that hypothesis. -/
structure CitedGeneralTheorems : Prop where
  vonMangoldt : PrimitiveDirichletRH →
    ∃ C : ℝ, 0 < C ∧ PrimitiveVonMangoldtEstimate C
  strip : PrimitiveDirichletRH → ∀ η : ℝ, 0 < η →
    ∃ C : ℝ, 0 < C ∧ PrimitiveStripEstimate η C

/-- Both analytic estimates follow from the zero-location premise through
the explicitly cited general theorem interfaces. -/
theorem uniform_estimates (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems) :
    (∃ C : ℝ, 0 < C ∧ PrimitiveVonMangoldtEstimate C) ∧
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ PrimitiveStripEstimate η C) :=
  ⟨cited.vonMangoldt hRH, cited.strip hRH⟩

end DepthAspect.GRHConsequences
