import BoundaryDraft.TwoFaceSurface

/-!
# Intrinsic chart rule for the two-face joint

The canonical spatial scalar-graph area theorem supplies the existing surface
measure. Multiplication by the derived Lorentzian Gram factor gives the
spacetime measure on every measurable chart subset, including chart overlaps.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- Lift of a tangent vector, as a continuous linear map. -/
def jointGraphLinear (q : JointSpace) : JointSpace →L[ℝ] Spacetime :=
  ContinuousLinearMap.pi (fun i => Fin.cases
    (InnerProductSpace.toDual ℝ JointSpace q)
    (fun j => PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) i)

@[simp] theorem jointGraphLinear_apply (q v : JointSpace) :
    jointGraphLinear q v = jointGraphTangent q v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [jointGraphLinear, jointGraphTangent, jointVector]

theorem hasFDerivAt_twoFaceLift {f : Spatial → ℝ} {x : JointSpace}
    (hf : DifferentiableAt ℝ (fun y : JointSpace => f y) x) :
    HasFDerivAt (twoFaceLift f) (jointGraphLinear (graphGradient f x)) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf.hasGradientAt.hasFDerivAt
  · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt

/-- Weighted pushforward through an embedding, proved as an identity of
measures. No change-of-area law is supplied as a premise. -/
theorem joint_withDensity_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {g : X → Y} (hg : MeasurableEmbedding g) (μ : Measure X) (w : Y → ℝ≥0∞) :
    (Measure.map g μ).withDensity w = Measure.map g (μ.withDensity (w ∘ g)) := by
  ext s hs
  rw [withDensity_apply _ hs, hg.restrict_map, hg.lintegral_map,
    Measure.map_apply hg.measurable hs, withDensity_apply _ (hg.measurable hs)]
  rfl

namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem continuous_future : Continuous (fun x : JointSpace => f x) := by
  obtain ⟨κ, η, _, hη, _, _, hLip⟩ := hf.slope_budget
  have hl : LipschitzWith ⟨η, hη⟩ (fun x : JointSpace => f x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := hLip x y
    change |f x - f y| ≤ η * ‖y - x‖ at he
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using he
  exact hl.continuous

theorem continuous_lift : Continuous (twoFaceLift f) := by
  apply continuous_pi
  intro i
  refine Fin.cases hf.continuous_future (fun j => ?_) i
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous

theorem measurableEmbedding_lift : MeasurableEmbedding (twoFaceLift f) := by
  apply Continuous.measurableEmbedding hf.continuous_lift
  intro x y he
  apply (WithLp.equiv 2 _).injective
  ext i
  exact congrFun he i.succ

theorem gramDensity (x : JointSpace) (hx : x ∈ graphJoint h) (v w : JointSpace)
    (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0)
    (hw : fderiv ℝ (fun y : JointSpace => h y) x w = 0) :
    jointGramDensity (jointGraphTangent (graphGradient f x) v)
        (jointGraphTangent (graphGradient f x) w) =
      twoFaceAreaDensity h f x * graphAreaJacobian v w := by
  have hn := hf.toAdmissibleGraphCap.graphInward_norm x hx
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

end AdmissibleTwoFace

namespace SliceHeightChart
variable {h : Spatial → ℝ} (c : SliceHeightChart h)

/-- Actual derivative of the extended spatial slice. -/
def jointSliceDerivative (u : SurfacePlane) : SurfacePlane →L[ℝ] JointSpace :=
  c.rotation.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (surfaceGraphDerivative (fderiv ℝ (c.scalarSlice 0) u))

theorem hasFDerivAt_jointSlice (u : SurfacePlane) :
    HasFDerivAt (c.slice 0) (c.jointSliceDerivative u) u :=
  c.rotation.symm.toContinuousLinearEquiv.hasFDerivAt.comp u
    (hasStrictFDerivAt_surfaceGraph _ _ _
      ((c.contDiff_scalarSlice 0).contDiffAt.hasStrictFDerivAt (by norm_num))).hasFDerivAt

/-- Tangent frame of the spacetime chart, not an arbitrary assigned frame. -/
def jointFrame (f : Spatial → ℝ) (u : SurfacePlane) (i : Fin 2) : Spacetime :=
  jointGraphTangent (graphGradient f (c.slice 0 u))
    (c.jointSliceDerivative u (EuclideanSpace.basisFun (Fin 2) ℝ i))

def jointChart (f : Spatial → ℝ) : SurfacePlane → Spacetime := twoFaceLift f ∘ c.slice 0

def jointDensity (f : Spatial → ℝ) (u : SurfacePlane) : ℝ :=
  jointGramDensity (c.jointFrame f u 0) (c.jointFrame f u 1)

theorem slice_mem_joint (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) :
    c.slice 0 u ∈ graphJoint h := c.slice_mem_level 0 le_rfl u hu

theorem hasFDerivAt_jointChart {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) :
    HasFDerivAt (c.jointChart f)
      ((jointGraphLinear (graphGradient f (c.slice 0 u))).comp (c.jointSliceDerivative u)) u :=
  (hasFDerivAt_twoFaceLift
    ((hf.smooth_future _ (c.slice_mem_joint u hu).1).differentiableAt (by norm_num))).comp u
      (c.hasFDerivAt_jointSlice u)

theorem jointFrame_eq_fderiv {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) (i : Fin 2) :
    c.jointFrame f u i = fderiv ℝ (c.jointChart f) u (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  rw [(c.hasFDerivAt_jointChart hf u hu).fderiv, ContinuousLinearMap.comp_apply,
    jointGraphLinear_apply]
  rfl

theorem jointSlice_tangent {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) (v : SurfacePlane) :
    fderiv ℝ (fun y : JointSpace => h y) (c.slice 0 u) (c.jointSliceDerivative u v) = 0 := by
  have hd := ((hf.smooth_near _ (c.slice_mem_joint u hu).1).differentiableAt
    (by norm_num)).hasFDerivAt.comp u (c.hasFDerivAt_jointSlice u)
  have he : (fun z => h (c.slice 0 z)) =ᶠ[𝓝 u] (fun _ => 0) :=
    mem_of_superset ((c.isOpen_sliceDomain 0).mem_nhds hu)
      (fun z hz => (c.slice_mem_joint z hz).2)
  have heq := (hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const (0 : ℝ) u)
  exact congrArg (fun L : SurfacePlane →L[ℝ] ℝ => L v) heq

theorem jointSlice_area (u : SurfacePlane) :
    graphAreaJacobian
      (c.jointSliceDerivative u (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (c.jointSliceDerivative u (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      surfaceGraphJacobian (c.scalarSlice 0) u := by
  simp only [jointSliceDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [graphAreaJacobian_eq_sqrt_gram]
  simp only [c.rotation.symm.norm_map, c.rotation.symm.inner_map_map]
  rw [← graphAreaJacobian_eq_sqrt_gram, surfaceGraphDerivative_areaJacobian]
  rfl

theorem jointDensity_eq {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) :
    c.jointDensity f u = twoFaceAreaDensity h f (c.slice 0 u) *
      surfaceGraphJacobian (c.scalarSlice 0) u := by
  rw [jointDensity, jointFrame, jointFrame, hf.gramDensity _ (c.slice_mem_joint u hu)
    _ _ (c.jointSlice_tangent hf u hu _) (c.jointSlice_tangent hf u hu _), c.jointSlice_area]

theorem jointDensity_pos {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) : 0 < c.jointDensity f u := by
  rw [c.jointDensity_eq hf u hu]
  exact mul_pos (hf.areaDensity_pos _ (c.slice_mem_joint u hu)) (surfaceGraphJacobian_pos _ _)

theorem continuous_slice (t : ℝ) : Continuous (c.slice t) :=
  c.rotation.symm.continuous.comp (continuous_surfaceGraph (c.contDiff_scalarSlice t).continuous)

/-- The intrinsic chart rule holds as an equality of measures on every
measurable chart subset. Overlaps are retained, never thrown away as seams. -/
theorem jointArea_chart {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain 0) :
    (twoFaceJointArea h f).restrict (c.jointChart f '' s) =
      Measure.map (c.jointChart f) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (c.jointDensity f u))) := by
  have him : MeasurableSet (c.slice 0 '' s) :=
    (c.measurableEmbedding_slice 0).measurableSet_image.mpr hs
  have hpre : twoFaceLift f ⁻¹' (c.jointChart f '' s) = c.slice 0 '' s := by
    rw [jointChart, image_comp, hf.measurableEmbedding_lift.injective.preimage_image]
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
  rw [twoFaceJointArea, hf.measurableEmbedding_lift.restrict_map, hpre,
    twoFaceProjectedArea, restrict_withDensity him, hsp,
    joint_withDensity_map (c.measurableEmbedding_slice 0)]
  simp only [Function.comp_def]
  rw [← withDensity_mul₀
      (measurable_surfaceGraphJacobian (c.scalarSlice 0)).ennreal_ofReal.aemeasurable hw,
    Measure.map_map hf.measurableEmbedding_lift.measurable (c.measurableEmbedding_slice 0).measurable]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (surfaceGraphJacobian_pos (c.scalarSlice 0) u).le,
    c.jointDensity_eq hf u (hsD hu), mul_comm]

/-- The two chart descriptions coincide on their full overlap. This is a
measure identity, not just equality of total areas or of one test integral. -/
theorem jointArea_overlap {f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (d : SliceHeightChart h) (s t : Set SurfacePlane)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsD : s ⊆ c.sliceDomain 0) (htD : t ⊆ d.sliceDomain 0) :
    (Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))).restrict (d.jointChart f '' t) =
    (Measure.map (d.jointChart f) ((volume.restrict t).withDensity
      (fun u => ENNReal.ofReal (d.jointDensity f u)))).restrict (c.jointChart f '' s) := by
  rw [← c.jointArea_chart hf s hs hsD, ← d.jointArea_chart hf t ht htD,
    Measure.restrict_comm]
  exact (hf.measurableEmbedding_lift.comp (d.measurableEmbedding_slice 0)).measurableSet_image.mpr ht

end SliceHeightChart

/-- These are genuine covering charts: each joint point occurs in the interior
of a constructed regular parameter domain. No chart-existence field is added. -/
theorem AdmissibleGraphCap.exists_jointChart {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (x : JointSpace) (hx : x ∈ graphJoint h) :
    ∃ c : SliceHeightChart h, ∃ u ∈ c.sliceDomain 0, c.slice 0 u = x := by
  obtain ⟨c, hxC, hc⟩ := hh.exists_sliceHeightChart x hx.1 (hh.regular_zero x hx.1 hx.2)
  let u := surfaceGraphBase (c.chart x)
  have he : surfaceGraph (fun _ => (0 : ℝ)) u = c.chart x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 = c.chart x 0
      rw [c.height, hx.2]
    · rfl
  have hu : u ∈ c.sliceDomain 0 := by
    change surfaceGraph (fun _ => (0 : ℝ)) u ∈ Metric.ball c.center c.radius
    rw [he, hc]
    exact Metric.mem_ball_self c.radius_pos
  exact ⟨c, u, hu, by rw [c.slice_eq_symm 0 u hu, he, c.chart.left_inv hxC]⟩

end BoundaryDraft
