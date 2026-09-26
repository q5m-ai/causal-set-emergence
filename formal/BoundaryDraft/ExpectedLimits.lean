import BoundaryDraft.ExpectationBridge
import BoundaryDraft.GraphLimit
import BoundaryDraft.GraphExamples
import BoundaryDraft.EllipsoidLimit
import BoundaryDraft.NullCapLimit

/-!
# Expected-action versions of the checked deterministic limits

Only the finite-density expectation identity is new input to these transfers.
The existing deterministic statements and their geometric hypotheses are
unchanged. These are limits of expectations, not random convergence claims.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

noncomputable section
namespace BoundaryDraft

theorem GraphCapData.expectedBDGAction_eq {h : Spatial → ℝ} (hh : GraphCapData h)
    {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (graphCapRegion h) = continuumMean ρ (graphCapRegion h) :=
  hh.boundedCausalRegion.expectedBDGAction_eq hρ

/-- The general graph-cap limit, now of the expected discrete action. -/
theorem AdmissibleGraphCap.expectedBDGAction_limit {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion h)) atTop
      (𝓝 (graphBoundaryIntegral h)) := by
  apply hh.graphCapLimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hh.toGraphCapData.expectedBDGAction_eq hρ).symm

/-- The same expected-action limit with the canonical variable-angle target. -/
theorem AdmissibleGraphCap.expectedBDGAction_limit_eq_angle {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion h)) atTop
      (𝓝 (∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h)) := by
  rw [← hh.graphBoundaryIntegral_eq_angle]
  exact hh.expectedBDGAction_limit

/-- Exact expectation identity under the original ellipsoid hypotheses. -/
theorem ellipsoid_expectedBDGAction_eq (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (graphCapRegion (ellipsoidProfile a b)) =
      continuumMean ρ (graphCapRegion (ellipsoidProfile a b)) :=
  (ellipsoid_graphCapData a b ha hb).expectedBDGAction_eq hρ

/-- Transfer of the original concrete ellipsoid theorem, not a reproof or a
replacement of its deterministic target. Unequal axes remain allowed. -/
theorem ellipsoid_expectedBDGAction_limit (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    Tendsto (fun ρ => expectedBDGAction ρ (graphCapRegion (ellipsoidProfile a b))) atTop
      (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a)) := by
  apply (ellipsoidLimitGoal a b ha hb).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (ellipsoid_expectedBDGAction_eq a b ha hb hρ).symm

/-- Exact null-cap identity needs no extra boundary-regularity assumption. -/
theorem nullCap_expectedBDGAction_eq (T a : ℝ) (hT : 0 < T) {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (nullCapRegion T a) = continuumMean ρ (nullCapRegion T a) :=
  (boundedCausalRegion_nullCap T a hT).expectedBDGAction_eq hρ

/-- Transfer of the unchanged null-cap theorem under exactly `0 < a < T`.
The target is the existing algebraic area, not a new induced-joint theorem. -/
theorem nullCap_expectedBDGAction_limit (T a : ℝ) (ha : 0 < a) (haT : a < T) :
    Tendsto (fun ρ => expectedBDGAction ρ (nullCapRegion T a)) atTop
      (𝓝 (nullJointArea T a)) := by
  apply (nullCapLimitGoal T a ha haT).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (nullCap_expectedBDGAction_eq T a (ha.trans haT) hρ).symm

end BoundaryDraft
