import BoundaryDraft.DimensionExpectationCompatibility
import BoundaryDraft.TwoFaceCharts
import BoundaryDraft.TwoFaceLimit

/-!
# Exact 4D geometry compatibility for every unchanged C3 member

This is a coordinate view of the EXISTING four-dimensional class, not a
smooth-order enlargement or a new all-dimensional admissibility contract.
The checked dimension-indexed coordinates transport its region, fixed area,
actual action and expectation without changing any old hypothesis or target.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- The old two-face region in the existing physical-dimension-four coordinates. -/
def dimensionFourTwoFaceRegion (h f : Spatial → ℝ) : Set (DimensionSpacetime 3) :=
  {p | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2}

def dimensionFourLift (f : Spatial → ℝ) (x : DimensionSpatial 3) : DimensionSpacetime 3 := (f x, x)

def dimensionFourJointArea (h f : Spatial → ℝ) : Measure (DimensionSpacetime 3) :=
  Measure.map (dimensionFourLift f) (twoFaceProjectedArea h f)

def dimensionFourBoundaryIntegral (h f : Spatial → ℝ) : ℝ :=
  ∫ p, twoFaceWeight h f p.2 ∂dimensionFourJointArea h f

theorem dimensionFour_mem_region (h f : Spatial → ℝ) (p : DimensionSpacetime 3) :
    dimensionSpacetimeCoordinates 3 p ∈ twoFaceRegion h f ↔ p ∈ dimensionFourTwoFaceRegion h f := by
  simp only [twoFaceRegion, dimensionFourTwoFaceRegion, mem_setOf_eq, dimensionSpacetimeCoordinates_apply,
    Fin.cons_zero, spatialPart, Fin.cons_succ]
  rfl

theorem dimensionFour_region_image (h f : Spatial → ℝ) :
    dimensionSpacetimeCoordinates 3 '' dimensionFourTwoFaceRegion h f = twoFaceRegion h f := by
  ext p
  obtain ⟨q, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective p
  rw [(dimensionSpacetimeCoordinates 3).injective.mem_set_image, dimensionFour_mem_region]

theorem continuous_dimensionFourCoordinates_symm : Continuous (dimensionSpacetimeCoordinates 3).symm := by
  have he : ((dimensionSpacetimeCoordinates 3).symm : Spacetime → DimensionSpacetime 3) =
      fun p => (p 0, (WithLp.equiv 2 _).symm (spatialPart p)) := by
    funext p
    apply (dimensionSpacetimeCoordinates 3).injective
    rw [(dimensionSpacetimeCoordinates 3).apply_symm_apply, dimensionSpacetimeCoordinates_apply]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [he]
  exact (continuous_apply 0).prodMk ((PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
    (continuous_pi fun i => continuous_apply i.succ))

theorem dimensionFour_lift_coordinates (f : Spatial → ℝ) (x : DimensionSpatial 3) :
    dimensionSpacetimeCoordinates 3 (dimensionFourLift f x) = twoFaceLift f x := by
  rw [dimensionSpacetimeCoordinates_apply]
  rfl

theorem dimensionFour_normal_coordinates (f : Spatial → ℝ) (x : DimensionSpatial 3) :
    dimensionSpacetimeCoordinates 3
      ((Real.sqrt (1 - ‖graphGradient f x‖ ^ 2))⁻¹ • ((1 : ℝ), graphGradient f x)) = twoFaceNormal f x := by
  rw [dimensionSpacetimeCoordinates_apply]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem dimensionFour_minkowski (p q : DimensionSpacetime 3) :
    dimensionMinkowski 3 p q = minkowskiInner (dimensionSpacetimeCoordinates 3 p) (dimensionSpacetimeCoordinates 3 q) := by
  rw [dimensionSpacetimeCoordinates_apply, dimensionSpacetimeCoordinates_apply]
  exact (minkowskiInner_jointVector p.1 q.1 p.2 q.2).symm

/-- The old spatial two-area coefficient remains pi/4, unlike the pilot's
one-dimensional normalization one. This is an equality of fixed measures. -/
theorem dimensionFour_projectedArea (h f : Spatial → ℝ) :
    twoFaceProjectedArea h f =
      (ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure (DimensionSpatial 3)).restrict
        (closure {x : DimensionSpatial 3 | 0 < h x} ∩ {x | h x = 0})).withDensity
          (fun x => ENNReal.ofReal (Real.sqrt (1 - ‖graphGradient f x -
            inner (𝕜 := ℝ) (graphGradient f x) (‖graphGradient h x‖⁻¹ • graphGradient h x) •
              (‖graphGradient h x‖⁻¹ • graphGradient h x)‖ ^ 2))) := rfl

namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem dimensionFour_measurable_region : MeasurableSet (dimensionFourTwoFaceRegion h f) := by
  have he : dimensionFourTwoFaceRegion h f = (dimensionSpacetimeCoordinates 3) ⁻¹' twoFaceRegion h f := by
    ext p
    exact (dimensionFour_mem_region h f p).symm
  rw [he]
  exact hf.measurableSet_region.preimage (dimensionSpacetimeCoordinates 3).measurable

/-- EVERY old C3 member supplies the actual dimension-indexed region constructor. -/
theorem dimensionFour_boundedCausalRegion : DimensionBoundedCausalRegion (dimensionFourTwoFaceRegion h f) where
  measurable := hf.dimensionFour_measurable_region
  bounded := by
    apply (hf.isCompact_closure_region.image continuous_dimensionFourCoordinates_symm).isBounded.subset
    intro p hp
    exact ⟨dimensionSpacetimeCoordinates 3 p, subset_closure ((dimensionFour_mem_region h f p).mpr hp),
      (dimensionSpacetimeCoordinates 3).symm_apply_apply p⟩
  causallyConvex := by
    intro p hp q hq z hz
    apply (dimensionFour_mem_region h f z).mp
    apply hf.causallyConvex_region _ ((dimensionFour_mem_region h f p).mpr hp)
      _ ((dimensionFour_mem_region h f q).mpr hq)
    exact ⟨(dimensionSpacetimeCoordinates_causal p z).mpr hz.1, (dimensionSpacetimeCoordinates_causal z q).mpr hz.2⟩

theorem dimensionFour_jointArea_coordinates :
    Measure.map (dimensionSpacetimeCoordinates 3) (dimensionFourJointArea h f) = twoFaceJointArea h f := by
  have hl : Measurable (dimensionFourLift f) := (hf.continuous_future.prodMk continuous_id).measurable
  rw [dimensionFourJointArea, Measure.map_map (dimensionSpacetimeCoordinates 3).measurable hl]
  congr 1
  funext x
  exact dimensionFour_lift_coordinates f x

theorem dimensionFour_boundaryIntegral : dimensionFourBoundaryIntegral h f = twoFaceBoundaryIntegral h f := by
  have he : MeasurableEmbedding (dimensionFourLift f) := by
    apply (hf.continuous_future.prodMk continuous_id).measurableEmbedding
    intro x y hxy
    exact congrArg Prod.snd hxy
  rw [dimensionFourBoundaryIntegral, dimensionFourJointArea, he.integral_map]
  rfl

omit hf in
theorem dimensionFour_action (ρ : ℝ) :
    dimensionWeightedAction 3 (dimensionPointCoefficient 4) (dimensionPairCoefficient 4)
      (dimensionIntervalCoefficient 4) ρ (dimensionFourTwoFaceRegion h f) (fun _ => 1) =
        continuumMean ρ (twoFaceRegion h f) := by
  rw [dimensionWeightedAction_four_eq_continuumMean, dimensionFour_region_image]

theorem dimensionFour_expectation {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionExpectedAction 3 ρ (dimensionFourTwoFaceRegion h f) = expectedBDGAction ρ (twoFaceRegion h f) := by
  rw [dimensionExpectedAction_four hρ hf.dimensionFour_measurable_region
    hf.dimensionFour_boundedCausalRegion.bounded.measure_lt_top, dimensionFour_region_image]

/-- Only a coordinate specialization of the ALREADY PROVED 4D limit. It is
not a new limit theorem in dimension three or in arbitrary dimension. -/
theorem dimensionFour_limit_compatibility : Tendsto (fun ρ =>
    dimensionWeightedAction 3 (dimensionPointCoefficient 4) (dimensionPairCoefficient 4)
      (dimensionIntervalCoefficient 4) ρ (dimensionFourTwoFaceRegion h f) (fun _ => 1))
      atTop (𝓝 (dimensionFourBoundaryIntegral h f)) := by
  simp only [dimensionFour_action, hf.dimensionFour_boundaryIntegral]
  exact hf.twoFaceLimit

end AdmissibleTwoFace
end BoundaryDraft
