import BoundaryDraft.DimensionTwoEndpoints
import BoundaryDraft.DimensionFourGeometry
import BoundaryDraft.Pilot3Contract

/-!
Dimension coverage is explicit: the new pilot is physical dimension three;
2D regular endpoint geometry counts every endpoint; the 4D coordinate view
works for EVERY unchanged C3 member. No common all-dimensional geometry or
new dimension-indexed asymptotic theorem is inferred from these controls.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
noncomputable section

example : Pilot3Spacetime = DimensionSpacetime 2 := rfl
example : DimensionSpacetime 1 = (ℝ × EuclideanSpace ℝ (Fin 1)) := rfl
example : DimensionSpacetime 3 = (ℝ × EuclideanSpace ℝ (Fin 3)) := rfl

example (J : Finset (DimensionSpatial 1)) :
    dimensionTwoEndpointMeasure J = Measure.count.restrict (J : Set (DimensionSpatial 1)) :=
  dimensionTwoEndpointMeasure_eq_count J

private def endpoint (t : ℝ) : DimensionSpatial 1 := (WithLp.equiv 2 _).symm (fun _ => t)
private theorem endpoint_inj (a b : ℝ) : endpoint a = endpoint b ↔ a = b := by
  constructor
  · intro he
    exact congrArg (fun x : DimensionSpatial 1 => x 0) he
  · exact congrArg endpoint

-- All four endpoints, with arbitrary signed weights, not only one interval.
example (w : DimensionSpatial 1 → ℝ) :
    (∫ x, w x ∂dimensionTwoEndpointMeasure {endpoint (-3), endpoint (-1), endpoint 1, endpoint 3}) =
      w (endpoint (-3)) + w (endpoint (-1)) + w (endpoint 1) + w (endpoint 3) := by
  classical
  rw [dimensionTwoEndpoint_integral]
  norm_num [Finset.sum_insert, endpoint_inj, add_assoc]

example {h : DimensionSpatial 1 → ℝ} (hb : Bornology.IsBounded {x | 0 < h x})
    (hs : ∀ x ∈ closure {x | 0 < h x}, ContDiffAt ℝ ∞ h x)
    (hr : ∀ x ∈ dimensionTwoSpatialJoint h, fderiv ℝ h x ≠ 0) (w : DimensionSpatial 1 → ℝ) :
    Integrable w (dimensionTwoJointMeasure h) ∧
      (∫ x, w x ∂dimensionTwoJointMeasure h) = ∑ x ∈ (dimensionTwo_joint_finite hb hs hr).toFinset, w x :=
  dimensionTwo_joint_integral hb hs hr w

-- This is the ORIGINAL C3 hypothesis, not SmoothPilot3 or a strengthened class.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (x : DimensionSpatial 3)
    (hx : x ∈ graphClosedPositive h) : ContDiffAt ℝ 3 (fun y : DimensionSpatial 3 => f y) x :=
  hf.smooth_future x hx

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    DimensionBoundedCausalRegion (dimensionFourTwoFaceRegion h f) := hf.dimensionFour_boundedCausalRegion

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    Measure.map (dimensionSpacetimeCoordinates 3) (dimensionFourJointArea h f) = twoFaceJointArea h f ∧
      dimensionFourBoundaryIntegral h f = twoFaceBoundaryIntegral h f :=
  ⟨hf.dimensionFour_jointArea_coordinates, hf.dimensionFour_boundaryIntegral⟩

example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionExpectedAction 3 ρ (dimensionFourTwoFaceRegion h f) = expectedBDGAction ρ (twoFaceRegion h f) :=
  hf.dimensionFour_expectation hρ

-- Only the already proved 4D limit is transported, never a pilot limit.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) : Tendsto (fun ρ =>
    dimensionWeightedAction 3 (dimensionPointCoefficient 4) (dimensionPairCoefficient 4)
      (dimensionIntervalCoefficient 4) ρ (dimensionFourTwoFaceRegion h f) (fun _ => 1))
      atTop (𝓝 (dimensionFourBoundaryIntegral h f)) := hf.dimensionFour_limit_compatibility
