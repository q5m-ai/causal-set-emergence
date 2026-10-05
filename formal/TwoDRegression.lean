import BoundaryDraft.TwoDExamples
import BoundaryDraft.TwoDOverlap

/-!
Independent expansions of the 2D contract. These regressions do NOT assert
TwoDDeterministicGoal or TwoDExpectedGoal. The signed analytic producers and
their unconditional assembly are checked separately in TwoDLimitRegression.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft.TwoDRegression

example {h f : DimensionSpatial 1 → ℝ} (hf : SmoothTwoD h f) :
    ∀ p ∈ {p : DimensionSpacetime 1 | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2},
    ∀ q ∈ {p : DimensionSpacetime 1 | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2},
    ∀ z ∈ dimensionCausalInterval p q, f z.2 - h z.2 < z.1 ∧ z.1 < f z.2 :=
  hf.causallyConvex_region

example {h f : DimensionSpatial 1 → ℝ} (hf : SmoothTwoD h f) :
    (μH[0] : Measure (DimensionSpatial 1)).restrict
      (closure {x | 0 < h x} ∩ {x | h x = 0}) =
    Measure.count.restrict (closure {x | 0 < h x} ∩ {x | h x = 0}) :=
  hf.jointMeasure_eq_count

example {h f : DimensionSpatial 1 → ℝ} (hf : SmoothTwoD h f) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteDimensionAction (dimensionMeasuredOrder 1) 2 ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (twoDRegion h f))) =
      dimensionWeightedAction 1 2 4 (1 / 2) ρ (twoDRegion h f) (fun _ => 1) := by
  simpa [twoDAction, dimensionPointCoefficient_two, dimensionPairCoefficient_two,
    dimensionIntervalCoefficient_two] using hf.expectedAction_eq hρ

example {h f : DimensionSpatial 1 → ℝ} (hf : SmoothTwoD h f) :
    twoDBoundaryIntegral h f = ∑ x ∈ hf.joint_finite.toFinset,
      Real.cosh (twoDAngle h f x) / Real.sinh (twoDAngle h f x) :=
  hf.boundaryIntegral_eq_coth_sum

example : SmoothTwoD twoDIntervalHeight twoDSineFuture := twoDIntervalSine_admissible
example : SmoothTwoD twoDIntervalHeight (fun _ => 0) := twoDIntervalPlanar_admissible
example : SmoothTwoD (fun _ => 0) (fun _ => 0) := twoDEmpty_admissible
example : (-1 / 8, (0 : DimensionSpatial 1)) ∈ twoDRegion twoDIntervalHeight twoDSineFuture :=
  twoDIntervalSine_nonempty
example : 0 < twoDIntervalHeight 0 ∧ fderiv ℝ twoDIntervalHeight 0 = 0 :=
  twoDIntervalHeight_critical

/-- Null and diagonal time fibres have not been deleted from the definitions. -/
example {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (x : TwoDSpace) :
    {s : ℝ | (s, x) ∈ twoDRegion h f ∧ (s + 0, x + 0) ∈ twoDRegion h f} =
      Ioo (f x - max 0 (h x)) (f (x + 0) - 0) :=
  hf.causal_time_fibre x 0 0 (by simp)

example (z : ℝ) : dimensionKernel 2 z = (1 - 2 * z + z ^ 2 / 2) * Real.exp (-z) :=
  twoDKernel_eq z

end BoundaryDraft.TwoDRegression
