import BoundaryDraft.IndependentFaceAngle
import BoundaryDraft.TwoFaceCharts

/-!
# The unchanged intrinsic area target under independent bounds

The normalized spatial Hausdorff measure and Lorentzian Gram density are
unchanged. Raw future germs need not be globally continuous: the map to the
joint is compared almost everywhere with the continuous upper envelope.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

theorem finite_projectedArea : IsFiniteMeasure (twoFaceProjectedArea h f) := by
  letI := hf.toRegularHeight.finite_graphSurfaceMeasure
  exact isFiniteMeasure_of_le (graphSurfaceMeasure h) (twoFaceProjectedArea_le h f)

theorem finite_jointArea : IsFiniteMeasure (twoFaceJointArea h f) := by
  letI := hf.finite_projectedArea
  exact Measure.isFiniteMeasure_map _ _

theorem integrable_weight : Integrable (twoFaceWeight h f) (twoFaceProjectedArea h f) := by
  letI := hf.finite_projectedArea
  have hi := hf.continuousOn_weight.integrableOn_compact
    (μ := twoFaceProjectedArea h f) hf.toRegularHeight.isCompact_joint
  simpa only [IntegrableOn, twoFaceProjectedArea_restrict_joint h f
    hf.toRegularHeight.measurableSet_joint] using hi

theorem integrable_areaDensity : Integrable (twoFaceAreaDensity h f) (graphSurfaceMeasure h) := by
  letI := hf.toRegularHeight.finite_graphSurfaceMeasure
  have hi := hf.continuousOn_areaDensity.integrableOn_compact
    (μ := graphSurfaceMeasure h) hf.toRegularHeight.isCompact_joint
  simpa only [IntegrableOn, graphSurfaceMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset (Subset.refl (graphJoint h))] using hi

theorem ae_projected_joint : ∀ᵐ x ∂twoFaceProjectedArea h f, x ∈ graphJoint h := by
  rw [← twoFaceProjectedArea_restrict_joint h f hf.toRegularHeight.measurableSet_joint]
  exact ae_restrict_mem hf.toRegularHeight.measurableSet_joint

/-- Only the envelope lift is globally continuous. This does not assert
regularity of the clipped envelope at a joint point. -/
theorem measurableEmbedding_upperLift : MeasurableEmbedding (twoFaceLift hf.upperEnvelope) := by
  have hc : Continuous (twoFaceLift hf.upperEnvelope) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hf.strictGraphLipschitz_upper.continuous.comp (PiLp.continuous_equiv 2 _)
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous
  apply hc.measurableEmbedding
  intro x y he
  apply (WithLp.equiv 2 _).injective
  ext i
  exact congrFun he i.succ

theorem upperLift_eq (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    twoFaceLift hf.upperEnvelope x = twoFaceLift f x := by
  unfold twoFaceLift
  rw [hf.upper_eq x hx]

/-- Irrelevant exterior raw values do not alter the actual joint-area measure. -/
theorem jointArea_eq_map_upper : twoFaceJointArea h f =
    Measure.map (twoFaceLift hf.upperEnvelope) (twoFaceProjectedArea h f) := by
  apply Measure.map_congr
  filter_upwards [hf.ae_projected_joint] with x hx
  exact (hf.upperLift_eq x hx.1).symm

theorem gramDensity (x : JointSpace) (hx : x ∈ graphJoint h) (v w : JointSpace)
    (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0)
    (hw : fderiv ℝ (fun y : JointSpace => h y) x w = 0) :
    jointGramDensity (jointGraphTangent (graphGradient f x) v)
        (jointGraphTangent (graphGradient f x) w) =
      twoFaceAreaDensity h f x * graphAreaJacobian v w := by
  have hn := hf.toRegularHeight.graphInward_norm x hx
  have hvn : inner (𝕜 := ℝ) (graphInward h x) v = 0 := by
    rw [graph_differential_eq_inner] at hv
    simp [graphInward, inner_smul_left, hv]
  have hwn : inner (𝕜 := ℝ) (graphInward h x) w = 0 := by
    rw [graph_differential_eq_inner] at hw
    simp [graphInward, inner_smul_left, hw]
  rw [jointGramDensity, jointGraph_gram _ _ _ _ hn hvn hwn,
    ← joint_tangential_norm_sq _ _ hn]
  rw [Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (show 0 ≤ graphAreaJacobian v w from norm_nonneg _)]
  rfl

end AdmissibleIndependentTwoFace

namespace SliceHeightChart
variable {h f : Spatial → ℝ} (c : SliceHeightChart h) (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- The chart derivative is that of the raw C³ germ, not the envelope. -/
theorem hasFDerivAt_jointChart_independent (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) :
    HasFDerivAt (c.jointChart f)
      ((jointGraphLinear (graphGradient f (c.slice 0 u))).comp (c.jointSliceDerivative u)) u :=
  (hasFDerivAt_twoFaceLift
    ((hf.smooth_future _ (c.slice_mem_joint u hu).1).differentiableAt (by norm_num))).comp u
      (c.hasFDerivAt_jointSlice u)

theorem jointFrame_eq_fderiv_independent (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0)
    (i : Fin 2) :
    c.jointFrame f u i = fderiv ℝ (c.jointChart f) u (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  rw [(c.hasFDerivAt_jointChart_independent hf u hu).fderiv, ContinuousLinearMap.comp_apply,
    jointGraphLinear_apply]
  rfl

theorem jointSlice_tangent_independent (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0)
    (v : SurfacePlane) :
    fderiv ℝ (fun y : JointSpace => h y) (c.slice 0 u) (c.jointSliceDerivative u v) = 0 := by
  have hd := ((hf.smooth_near _ (c.slice_mem_joint u hu).1).differentiableAt
    (by norm_num)).hasFDerivAt.comp u (c.hasFDerivAt_jointSlice u)
  have he : (fun z => h (c.slice 0 z)) =ᶠ[𝓝 u] (fun _ => 0) :=
    mem_of_superset ((c.isOpen_sliceDomain 0).mem_nhds hu)
      (fun z hz => (c.slice_mem_joint z hz).2)
  have heq := (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const (0 : ℝ) u)
  exact congrArg (fun L : SurfacePlane →L[ℝ] ℝ => L v) heq

theorem jointDensity_eq_independent (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) :
    c.jointDensity f u = twoFaceAreaDensity h f (c.slice 0 u) *
      surfaceGraphJacobian (c.scalarSlice 0) u := by
  rw [jointDensity, jointFrame, jointFrame, hf.gramDensity _ (c.slice_mem_joint u hu)
    _ _ (c.jointSlice_tangent_independent hf u hu _) (c.jointSlice_tangent_independent hf u hu _),
    c.jointSlice_area]

theorem jointChart_upper_eqOn (s : Set SurfacePlane) (hsD : s ⊆ c.sliceDomain 0) :
    EqOn (c.jointChart hf.upperEnvelope) (c.jointChart f) s :=
  fun u hu => hf.upperLift_eq _ (c.slice_mem_joint u (hsD hu)).1

theorem measurableSet_jointChart_image_independent (s : Set SurfacePlane)
    (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain 0) :
    MeasurableSet (c.jointChart f '' s) := by
  rw [← (c.jointChart_upper_eqOn hf s hsD).image_eq]
  exact (hf.measurableEmbedding_upperLift.comp
    (c.measurableEmbedding_slice 0)).measurableSet_image.mpr hs

/-- Equality on every measurable chart subset, with the unchanged intrinsic
Gram density and Hausdorff normalization. -/
theorem jointArea_chart_independent (s : Set SurfacePlane)
    (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain 0) :
    (twoFaceJointArea h f).restrict (c.jointChart f '' s) =
      Measure.map (c.jointChart f) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (c.jointDensity f u))) := by
  have him : MeasurableSet (c.slice 0 '' s) :=
    (c.measurableEmbedding_slice 0).measurableSet_image.mpr hs
  have hpre : twoFaceLift hf.upperEnvelope ⁻¹' (c.jointChart f '' s) = c.slice 0 '' s := by
    rw [← (c.jointChart_upper_eqOn hf s hsD).image_eq, jointChart, image_comp,
      hf.measurableEmbedding_upperLift.injective.preimage_image]
  have hsp : (graphSurfaceMeasure h).restrict (c.slice 0 '' s) =
      Measure.map (c.slice 0) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (surfaceGraphJacobian (c.scalarSlice 0) u))) := by
    rw [← graphLevelMeasure_zero, c.graphLevelMeasure_slice_image 0 le_rfl s hs hsD]
    congr 1
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hs] with u hu
    rw [c.scalarSlice_jacobian 0 u (hsD hu)]
  have hw : AEMeasurable
      (fun u => ENNReal.ofReal (twoFaceAreaDensity h f (c.slice 0 u))) (volume.restrict s) := by
    have hc : ContinuousOn (fun u => twoFaceAreaDensity h f (c.slice 0 u)) s :=
      hf.continuousOn_areaDensity.comp (c.continuous_slice 0).continuousOn
        (fun u hu => c.slice_mem_joint u (hsD hu))
    exact (hc.aestronglyMeasurable hs).aemeasurable.ennreal_ofReal
  rw [hf.jointArea_eq_map_upper, hf.measurableEmbedding_upperLift.restrict_map, hpre,
    twoFaceProjectedArea, restrict_withDensity him, hsp,
    joint_withDensity_map (c.measurableEmbedding_slice 0)]
  simp only [Function.comp_def]
  rw [← withDensity_mul₀
      (measurable_surfaceGraphJacobian (c.scalarSlice 0)).ennreal_ofReal.aemeasurable hw,
    Measure.map_map hf.measurableEmbedding_upperLift.measurable
      (c.measurableEmbedding_slice 0).measurable]
  have hd : (volume.restrict s).withDensity
      ((fun u => ENNReal.ofReal (surfaceGraphJacobian (c.scalarSlice 0) u)) *
        (fun u => ENNReal.ofReal (twoFaceAreaDensity h f (c.slice 0 u)))) =
      (volume.restrict s).withDensity (fun u => ENNReal.ofReal (c.jointDensity f u)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hs] with u hu
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (surfaceGraphJacobian_pos (c.scalarSlice 0) u).le,
      c.jointDensity_eq_independent hf u (hsD hu), mul_comm]
  rw [hd]
  apply Measure.map_congr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem hs] with u hu
  exact c.jointChart_upper_eqOn hf s hsD hu

/-- Chart overlap is equality of measures, not just equality of total areas. -/
theorem jointArea_overlap_independent (d : SliceHeightChart h) (s t : Set SurfacePlane)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsD : s ⊆ c.sliceDomain 0) (htD : t ⊆ d.sliceDomain 0) :
    (Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))).restrict (d.jointChart f '' t) =
    (Measure.map (d.jointChart f) ((volume.restrict t).withDensity
      (fun u => ENNReal.ofReal (d.jointDensity f u)))).restrict (c.jointChart f '' s) := by
  rw [← c.jointArea_chart_independent hf s hs hsD, ← d.jointArea_chart_independent hf t ht htD,
    Measure.restrict_comm]
  exact d.measurableSet_jointChart_image_independent hf t ht htD

end SliceHeightChart
end BoundaryDraft
