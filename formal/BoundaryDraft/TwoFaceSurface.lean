import BoundaryDraft.TwoFaceAngle
import BoundaryDraft.GraphSliceTransport

/-!
# Finite induced two-face targets and exact planar recovery

Finiteness and absolute integrability are derived from compact regular geometry,
not assumed from the value of the target. Chart identification is separate.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

theorem twoFaceAreaDensity_nonneg (h f : Spatial → ℝ) (x : JointSpace) :
    0 ≤ twoFaceAreaDensity h f x := Real.sqrt_nonneg _

theorem twoFaceAreaDensity_le_one (h f : Spatial → ℝ) (x : JointSpace) :
    twoFaceAreaDensity h f x ≤ 1 := by
  have := Real.sqrt_le_sqrt (show 1 - ‖twoFaceTangentialGradient h f x‖ ^ 2 ≤ 1 by
    linarith [sq_nonneg ‖twoFaceTangentialGradient h f x‖])
  simpa only [Real.sqrt_one] using this

/-- Lorentzian area is bounded by spatial projected area, not Euclidean
spacetime area. This bound does not assert that the two areas agree. -/
theorem twoFaceProjectedArea_le (h f : Spatial → ℝ) :
    twoFaceProjectedArea h f ≤ graphSurfaceMeasure h := by
  calc
    _ ≤ (graphSurfaceMeasure h).withDensity (fun _ => 1) :=
      withDensity_mono (Eventually.of_forall fun x => by
        simpa using ENNReal.ofReal_le_ofReal (twoFaceAreaDensity_le_one h f x))
    _ = _ := by simp

theorem ae_graphJoint {h : Spatial → ℝ} (hh : RegularHeight h) :
    ∀ᵐ x ∂graphSurfaceMeasure h, x ∈ graphJoint h := by
  apply Measure.ae_smul_measure
  exact ae_restrict_mem hh.measurableSet_joint

theorem twoFaceProjectedArea_restrict_joint (h f : Spatial → ℝ)
    (hJ : MeasurableSet (graphJoint h)) :
    (twoFaceProjectedArea h f).restrict (graphJoint h) = twoFaceProjectedArea h f := by
  rw [twoFaceProjectedArea, restrict_withDensity hJ, graphSurfaceMeasure,
    Measure.restrict_smul, Measure.restrict_restrict_of_subset (Subset.refl (graphJoint h))]

namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem finite_projectedArea : IsFiniteMeasure (twoFaceProjectedArea h f) := by
  letI := hf.toAdmissibleGraphCap.finite_graphSurfaceMeasure
  exact isFiniteMeasure_of_le (graphSurfaceMeasure h) (twoFaceProjectedArea_le h f)

theorem finite_jointArea : IsFiniteMeasure (twoFaceJointArea h f) := by
  letI := hf.finite_projectedArea
  exact Measure.isFiniteMeasure_map _ _

theorem integrable_weight : Integrable (twoFaceWeight h f) (twoFaceProjectedArea h f) := by
  letI := hf.finite_projectedArea
  have hi := hf.continuousOn_weight.integrableOn_compact
    (μ := twoFaceProjectedArea h f) hf.toAdmissibleGraphCap.isCompact_joint
  simpa only [IntegrableOn, twoFaceProjectedArea_restrict_joint h f
    hf.toAdmissibleGraphCap.measurableSet_joint] using hi

theorem integrable_areaDensity : Integrable (twoFaceAreaDensity h f) (graphSurfaceMeasure h) := by
  letI := hf.toAdmissibleGraphCap.finite_graphSurfaceMeasure
  have hi := hf.continuousOn_areaDensity.integrableOn_compact
    (μ := graphSurfaceMeasure h) hf.toAdmissibleGraphCap.isCompact_joint
  simpa only [IntegrableOn, graphSurfaceMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset (Subset.refl (graphJoint h))] using hi

theorem aemeasurable_areaDensity :
    AEMeasurable (fun x => ENNReal.ofReal (twoFaceAreaDensity h f x)) (graphSurfaceMeasure h) :=
  hf.integrable_areaDensity.aestronglyMeasurable.aemeasurable.ennreal_ofReal

/-- A concrete proof of the unchanged area/nondegeneracy goal, not its
replacement by a structure field. -/
theorem area_goal :
    (∀ x ∈ graphJoint h, 1 < twoFaceCosh h f x ∧ 0 < twoFaceAreaDensity h f x) ∧
    IsFiniteMeasure (twoFaceProjectedArea h f) ∧
    Integrable (twoFaceWeight h f) (twoFaceProjectedArea h f) :=
  ⟨fun x hx => ⟨hf.cosh_gt_one x hx, hf.areaDensity_pos x hx⟩,
    hf.finite_projectedArea, hf.integrable_weight⟩

end AdmissibleTwoFace

theorem twoFaceAreaGoal : TwoFaceAreaGoal := fun _ _ hf => hf.area_goal

@[simp] theorem twoFaceAreaDensity_planar (h : Spatial → ℝ) (x : JointSpace) :
    twoFaceAreaDensity h (fun _ => 0) x = 1 := by
  simp [twoFaceAreaDensity, twoFaceTangentialGradient]

/-- Equality of measures, for every profile, not just agreement on a sphere. -/
@[simp] theorem twoFaceProjectedArea_planar (h : Spatial → ℝ) :
    twoFaceProjectedArea h (fun _ => 0) = graphSurfaceMeasure h := by
  simp [twoFaceProjectedArea]

namespace AdmissibleGraphCap
variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem twoFaceWeight_planar (x : JointSpace) (hx : x ∈ graphJoint h) :
    twoFaceWeight h (fun _ => 0) x = 1 / ‖graphGradient h x‖ := by
  have hk := hh.graphSlope_pos x hx
  have hk1 := hh.graphSlope_lt_one x hx.1
  have hd : 0 < 1 - graphSlope h x ^ 2 := by nlinarith
  have hs := Real.sqrt_pos.mpr hd
  have hs2 := Real.sq_sqrt hd.le
  have hC : twoFaceCosh h (fun _ => 0) x = 1 / Real.sqrt (1 - graphSlope h x ^ 2) := by
    change minkowskiInner (jointUnitNormal _) (jointUnitNormal _) = _
    rw [jointUnitNormal_inner, hh.twoFace_planar.gradient_past x hx.1]
    simp [graphSlope]
  have hd2 : (1 / Real.sqrt (1 - graphSlope h x ^ 2)) ^ 2 - 1 =
      (graphSlope h x / Real.sqrt (1 - graphSlope h x ^ 2)) ^ 2 := by
    field_simp
  rw [twoFaceWeight, hC, hd2, Real.sqrt_sq (div_pos hk hs).le]
  change _ = 1 / graphSlope h x
  field_simp

theorem twoFaceBoundaryIntegral_planar :
    twoFaceBoundaryIntegral h (fun _ => 0) = graphBoundaryIntegral h := by
  unfold twoFaceBoundaryIntegral
  rw [twoFaceProjectedArea_planar]
  apply integral_congr_ae
  filter_upwards [ae_graphJoint hh] with x hx
  exact hh.twoFaceWeight_planar x hx

end AdmissibleGraphCap

theorem twoFacePlanarTargetGoal : TwoFacePlanarTargetGoal :=
  fun h hh => ⟨twoFaceProjectedArea_planar h, hh.twoFaceBoundaryIntegral_planar⟩

end BoundaryDraft
