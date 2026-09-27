import BoundaryDraft.TwoFaceCharts
import BoundaryDraft.ActionTransport

/-!
# Intrinsically computed area under ambient transport

The reference surface is an original regular spatial joint. For an embedding
into spacetime we compute area from its ACTUAL derivative and the Lorentzian
Gram determinant, divided by the reference frame's Euclidean area. The
transported area is NOT defined to be the pushforward of the old answer.
Lorentz covariance and dilation scaling follow from the metric calculation.

The geometric applications here are the two-graph subclass and its affine
Lorentz/positive-dilation images, not unrestricted Lorentzian manifolds.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- Geometric tangent-frame data only. Existence is derived below. -/
structure JointTangentFrame (h : Spatial → ℝ) (x : JointSpace) where
  first : JointSpace
  second : JointSpace
  tangent_first : fderiv ℝ (fun y : JointSpace => h y) x first = 0
  tangent_second : fderiv ℝ (fun y : JointSpace => h y) x second = 0
  area_pos : 0 < graphAreaJacobian first second

namespace AdmissibleGraphCap
variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem nonempty_jointTangentFrame (x : JointSpace) (hx : x ∈ graphJoint h) :
    Nonempty (JointTangentFrame h x) := by
  obtain ⟨c, u, hu, he⟩ := hh.exists_jointChart x hx
  refine ⟨{
    first := c.jointSliceDerivative u (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    second := c.jointSliceDerivative u (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    tangent_first := ?_
    tangent_second := ?_
    area_pos := ?_ }⟩
  · simpa only [he] using c.jointSlice_tangent hh.twoFace_planar u hu
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  · simpa only [he] using c.jointSlice_tangent hh.twoFace_planar u hu
      (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  · rw [c.jointSlice_area]
    exact surfaceGraphJacobian_pos _ _

/-- A reference frame chosen from constructed regular charts. Later identities
hold for every frame, so this choice does not fix a preferred joint atlas. -/
def jointTangentFrame (x : JointSpace) (hx : x ∈ graphJoint h) : JointTangentFrame h x :=
  Classical.choice (hh.nonempty_jointTangentFrame x hx)

end AdmissibleGraphCap

/-- The relative area factor computed from an embedding's actual derivative.
This definition contains no action, transport identity, or target integral. -/
def jointFrameDensity {h : Spatial → ℝ} {x : JointSpace} (T : JointTangentFrame h x)
    (ψ : JointSpace → Spacetime) : ℝ :=
  jointGramDensity (fderiv ℝ ψ x T.first) (fderiv ℝ ψ x T.second) /
    graphAreaJacobian T.first T.second

def jointInducedDensity {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (ψ : JointSpace → Spacetime) (x : JointSpace) : ℝ := by
  classical
  exact if hx : x ∈ graphJoint h then jointFrameDensity (hh.jointTangentFrame x hx) ψ else 0

def jointInducedProjected {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (ψ : JointSpace → Spacetime) : Measure JointSpace :=
  (graphSurfaceMeasure h).withDensity (fun x => ENNReal.ofReal (jointInducedDensity hh ψ x))

def jointInducedArea {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (ψ : JointSpace → Spacetime) : Measure Spacetime :=
  Measure.map ψ (jointInducedProjected hh ψ)

/-- Every regular tangent frame gives the original coordinate density. Thus
neither the reference-frame choice nor its orientation enters the measure. -/
theorem AdmissibleTwoFace.frameDensity_lift {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) (x : JointSpace) (hx : x ∈ graphJoint h)
    (T : JointTangentFrame h x) :
    jointFrameDensity T (twoFaceLift f) = twoFaceAreaDensity h f x := by
  rw [jointFrameDensity, (hasFDerivAt_twoFaceLift
    ((hf.smooth_future x hx.1).differentiableAt (by norm_num))).fderiv,
    jointGraphLinear_apply, jointGraphLinear_apply,
    hf.gramDensity x hx T.first T.second T.tangent_first T.tangent_second]
  exact mul_div_cancel_right₀ _ T.area_pos.ne'

theorem AdmissibleTwoFace.inducedProjected_lift {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    jointInducedProjected hf.toAdmissibleGraphCap (twoFaceLift f) = twoFaceProjectedArea h f := by
  apply withDensity_congr_ae
  filter_upwards [ae_graphJoint hf.toAdmissibleGraphCap] with x hx
  simp only [jointInducedDensity, dif_pos hx, hf.frameDensity_lift x hx]

theorem AdmissibleTwoFace.inducedArea_lift {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    jointInducedArea hf.toAdmissibleGraphCap (twoFaceLift f) = twoFaceJointArea h f := by
  rw [jointInducedArea, hf.inducedProjected_lift, twoFaceJointArea]

namespace PoincareEquiv

/-- Translation disappears from the actual tangent derivative. -/
theorem hasFDerivAt (F : PoincareEquiv) (p : Spacetime) :
    HasFDerivAt F F.linear.toContinuousLinearEquiv.toContinuousLinearMap p :=
  F.linear.toContinuousLinearEquiv.hasFDerivAt.add_const F.translation

/-- The metric-computed density, not a transported measure by definition. -/
theorem frameDensity_comp (F : PoincareEquiv) {h : Spatial → ℝ} {x : JointSpace}
    (T : JointTangentFrame h x) {ψ : JointSpace → Spacetime}
    (hψ : DifferentiableAt ℝ ψ x) :
    jointFrameDensity T (F ∘ ψ) = jointFrameDensity T ψ := by
  rw [jointFrameDensity, ((F.hasFDerivAt _).comp x hψ.hasFDerivAt).fderiv]
  change jointGramDensity (F.linear (fderiv ℝ ψ x T.first))
    (F.linear (fderiv ℝ ψ x T.second)) / graphAreaJacobian T.first T.second = _
  rw [jointGramDensity_lorentz]
  rfl

theorem inducedDensity_comp (F : PoincareEquiv) {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) {ψ : JointSpace → Spacetime}
    (hψ : ∀ x ∈ graphJoint h, DifferentiableAt ℝ ψ x) (x : JointSpace) :
    jointInducedDensity hh (F ∘ ψ) x = jointInducedDensity hh ψ x := by
  by_cases hx : x ∈ graphJoint h
  · simp only [jointInducedDensity, dif_pos hx, F.frameDensity_comp _ (hψ x hx)]
  · simp only [jointInducedDensity, dif_neg hx]

/-- Affine Lorentz covariance of independently metric-computed area. -/
theorem inducedArea_comp (F : PoincareEquiv) {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) {ψ : JointSpace → Spacetime} (hψm : Measurable ψ)
    (hψ : ∀ x ∈ graphJoint h, DifferentiableAt ℝ ψ x) :
    jointInducedArea hh (F ∘ ψ) = Measure.map F (jointInducedArea hh ψ) := by
  simp only [jointInducedArea, jointInducedProjected, F.inducedDensity_comp hh hψ]
  rw [Measure.map_map F.toHomeomorph.continuous.measurable hψm]

theorem twoFace_inducedArea (F : PoincareEquiv) {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    jointInducedArea hf.toAdmissibleGraphCap (F ∘ twoFaceLift f) =
      Measure.map F (twoFaceJointArea h f) := by
  rw [F.inducedArea_comp _ hf.continuous_lift.measurable
    (fun x hx => (hasFDerivAt_twoFaceLift
      ((hf.smooth_future x hx.1).differentiableAt (by norm_num))).differentiableAt),
    hf.inducedArea_lift]

/-- Weight preservation uses BOTH transported future unit normals. -/
theorem twoFace_weight (F : PoincareEquiv) (h f : Spatial → ℝ) (x : JointSpace) :
    let C := minkowskiInner (F.linear (twoFaceNormal (fun y => f y - h y) x))
      (F.linear (twoFaceNormal f x))
    C / Real.sqrt (C ^ 2 - 1) = twoFaceWeight h f x := by
  dsimp only
  rw [F.preserves_inner]
  rfl

/-- Transport for every signed observable, not merely for total area. -/
theorem twoFace_integral (F : PoincareEquiv) {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) (φ : Spacetime → ℝ) :
    (∫ p, φ p ∂jointInducedArea hf.toAdmissibleGraphCap (F ∘ twoFaceLift f)) =
      ∫ p, φ (F p) ∂twoFaceJointArea h f := by
  rw [F.twoFace_inducedArea hf, F.toHomeomorph.measurableEmbedding.integral_map]

/-- Time orientation of transported unit normals, including spatial parity. -/
theorem future_unit_normal (F : PoincareEquiv) (n : Spacetime)
    (ht : 0 < n 0) (hu : minkowskiInner n n = 1) :
    0 < F.linear n 0 ∧ minkowskiInner (F.linear n) (F.linear n) = 1 := by
  have hunit : minkowskiInner (F.linear n) (F.linear n) = 1 := by rw [F.preserves_inner, hu]
  have ha : minkowskiInner (F.linear (timeAxis 1)) (F.linear (timeAxis 1)) = 1 := by
    rw [F.preserves_inner]; simp [minkowskiInner]
  have hc : 0 ≤ minkowskiInner (F.linear n) (F.linear (timeAxis 1)) := by
    rw [F.preserves_inner]; simpa [minkowskiInner] using ht.le
  have hn := time_nonneg_of_minkowskiInner_nonneg (by rw [hunit]; norm_num)
    F.future_time (by rw [ha]; norm_num) hc
  refine ⟨lt_of_le_of_ne hn ?_, hunit⟩
  intro hz
  have hsum : 0 ≤ ∑ i : Fin 3, F.linear n i.succ * F.linear n i.succ :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  simp only [minkowskiInner, ← hz, mul_zero, zero_sub] at hunit
  linarith

/-- Every transported chart still has its independently computed Gram density. -/
theorem twoFace_chart (F : PoincareEquiv) {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) (c : SliceHeightChart h)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain 0) :
    (jointInducedArea hf.toAdmissibleGraphCap (F ∘ twoFaceLift f)).restrict
        ((F ∘ c.jointChart f) '' s) =
      Measure.map (F ∘ c.jointChart f) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (jointGramDensity
          (F.linear (c.jointFrame f u 0)) (F.linear (c.jointFrame f u 1))))) := by
  have hm : Measurable (c.jointChart f) :=
    (hf.measurableEmbedding_lift.comp (c.measurableEmbedding_slice 0)).measurable
  rw [F.twoFace_inducedArea hf, F.toHomeomorph.measurableEmbedding.restrict_map,
    image_comp, F.toHomeomorph.injective.preimage_image, c.jointArea_chart hf s hs hsD,
    Measure.map_map F.toHomeomorph.continuous.measurable hm]
  simp only [jointGramDensity_lorentz, SliceHeightChart.jointDensity]

end PoincareEquiv

/-- Dilation acts on the actual derivative before the Gram density is taken. -/
theorem jointFrameDensity_smul {h : Spatial → ℝ} {x : JointSpace}
    (T : JointTangentFrame h x) {ψ : JointSpace → Spacetime}
    (hψ : DifferentiableAt ℝ ψ x) (s : ℝ) :
    jointFrameDensity T (fun x => s • ψ x) = s ^ 2 * jointFrameDensity T ψ := by
  rw [jointFrameDensity, (hψ.hasFDerivAt.const_smul s).fderiv]
  simp only [ContinuousLinearMap.smul_apply, jointGramDensity_smul, jointFrameDensity]
  ring

theorem jointInducedDensity_smul {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    {ψ : JointSpace → Spacetime} (hψ : ∀ x ∈ graphJoint h, DifferentiableAt ℝ ψ x)
    (s : ℝ) (x : JointSpace) :
    jointInducedDensity hh (fun x => s • ψ x) x = s ^ 2 * jointInducedDensity hh ψ x := by
  by_cases hx : x ∈ graphJoint h
  · simp only [jointInducedDensity, dif_pos hx, jointFrameDensity_smul _ (hψ x hx)]
  · simp only [jointInducedDensity, dif_neg hx, mul_zero]

/-- Induced area has degree two, although ambient volume has degree four. -/
theorem jointInducedArea_smul {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    {ψ : JointSpace → Spacetime} (hψm : Measurable ψ)
    (hψ : ∀ x ∈ graphJoint h, DifferentiableAt ℝ ψ x) (s : ℝ) :
    jointInducedArea hh (fun x => s • ψ x) =
      ENNReal.ofReal (s ^ 2) • Measure.map (fun p : Spacetime => s • p) (jointInducedArea hh ψ) := by
  simp only [jointInducedArea, jointInducedProjected, jointInducedDensity_smul hh hψ s,
    ENNReal.ofReal_mul (sq_nonneg s)]
  have he : (fun x => ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (jointInducedDensity hh ψ x)) =
      ENNReal.ofReal (s ^ 2) • (fun x => ENNReal.ofReal (jointInducedDensity hh ψ x)) := rfl
  rw [he, withDensity_smul' _ _ ENNReal.ofReal_ne_top, Measure.map_smul,
    Measure.map_map (show Measurable (fun p : Spacetime => s • p) from
      measurable_const.smul measurable_id) hψm]
  rfl

theorem AdmissibleTwoFace.inducedArea_smul_lift {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) (s : ℝ) :
    jointInducedArea hf.toAdmissibleGraphCap (fun x => s • twoFaceLift f x) =
      ENNReal.ofReal (s ^ 2) • Measure.map (fun p : Spacetime => s • p) (twoFaceJointArea h f) := by
  rw [jointInducedArea_smul _ hf.continuous_lift.measurable
    (fun x hx => (hasFDerivAt_twoFaceLift
      ((hf.smooth_future x hx.1).differentiableAt (by norm_num))).differentiableAt),
    hf.inducedArea_lift]

/-- The original angle weight as an observable on the actual spacetime joint. -/
def twoFaceSpacetimeWeight (h f : Spatial → ℝ) (p : Spacetime) : ℝ :=
  twoFaceWeight h f ((WithLp.equiv 2 _).symm (spatialPart p))

@[simp] theorem twoFaceSpacetimeWeight_lift (h f : Spatial → ℝ) (x : JointSpace) :
    twoFaceSpacetimeWeight h f (twoFaceLift f x) = twoFaceWeight h f x := rfl

theorem AdmissibleTwoFace.integrable_spacetimeWeight {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    Integrable (twoFaceSpacetimeWeight h f) (twoFaceJointArea h f) := by
  rw [twoFaceJointArea, hf.measurableEmbedding_lift.integrable_map_iff]
  exact hf.integrable_weight

theorem AdmissibleTwoFace.integral_spacetimeWeight {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    (∫ p, twoFaceSpacetimeWeight h f p ∂twoFaceJointArea h f) = twoFaceBoundaryIntegral h f := by
  rw [twoFaceJointArea, hf.measurableEmbedding_lift.integral_map]
  rfl

/-- Full angle-weighted area covariance, with the weight pulled back through
the affine inverse. `twoFace_weight` identifies it with the transformed normals. -/
theorem PoincareEquiv.twoFace_boundaryIntegral (F : PoincareEquiv) {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    (∫ p, twoFaceSpacetimeWeight h f (F.symm p)
      ∂jointInducedArea hf.toAdmissibleGraphCap (F ∘ twoFaceLift f)) = twoFaceBoundaryIntegral h f := by
  rw [F.twoFace_integral hf]
  simpa only [F.symm_apply_apply] using hf.integral_spacetimeWeight

theorem PoincareEquiv.twoFace_integrable_weight (F : PoincareEquiv) {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    Integrable (fun p => twoFaceSpacetimeWeight h f (F.symm p))
      (jointInducedArea hf.toAdmissibleGraphCap (F ∘ twoFaceLift f)) := by
  rw [F.twoFace_inducedArea hf, F.toHomeomorph.measurableEmbedding.integrable_map_iff]
  simpa only [Function.comp_def, F.symm_apply_apply] using hf.integrable_spacetimeWeight

/-- Positive dilation leaves unit normals and hence angle weights unchanged:
a normal to a tangent is also normal to its positively dilated tangent. -/
theorem joint_normal_dilation (n v : Spacetime) (hn : minkowskiInner n v = 0) (s : ℝ) :
    minkowskiInner n (s • v) = 0 := by rw [minkowskiInner_smul_right, hn, mul_zero]

theorem AdmissibleTwoFace.boundaryIntegral_dilate {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) {s : ℝ} (hs : 0 < s) :
    (∫ p, twoFaceSpacetimeWeight h f (s⁻¹ • p)
      ∂jointInducedArea hf.toAdmissibleGraphCap (fun x => s • twoFaceLift f x)) =
      s ^ 2 * twoFaceBoundaryIntegral h f := by
  have he : MeasurableEmbedding (fun p : Spacetime => s • p) :=
    (dilationHomeomorph s hs).measurableEmbedding
  rw [hf.inducedArea_smul_lift, integral_smul_measure, he.integral_map]
  simp only [ENNReal.toReal_ofReal (sq_nonneg s), smul_eq_mul,
    dilationHomeomorph_apply, smul_smul, inv_mul_cancel₀ hs.ne', one_smul,
    hf.integral_spacetimeWeight]

theorem AdmissibleTwoFace.integrable_weight_dilate {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p => twoFaceSpacetimeWeight h f (s⁻¹ • p))
      (jointInducedArea hf.toAdmissibleGraphCap (fun x => s • twoFaceLift f x)) := by
  have he : MeasurableEmbedding (fun p : Spacetime => s • p) :=
    (dilationHomeomorph s hs).measurableEmbedding
  rw [hf.inducedArea_smul_lift,
    integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hs)) ENNReal.ofReal_ne_top,
    he.integrable_map_iff]
  simpa only [Function.comp_def, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    using hf.integrable_spacetimeWeight

/-- Dilation also preserves the local intrinsic chart characterization with
its degree-two Gram density. -/
theorem AdmissibleTwoFace.dilated_chart {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) {s : ℝ} (hs : 0 < s)
    (c : SliceHeightChart h) (U : Set SurfacePlane) (hU : MeasurableSet U)
    (hUD : U ⊆ c.sliceDomain 0) :
    (jointInducedArea hf.toAdmissibleGraphCap (fun x => s • twoFaceLift f x)).restrict
      ((fun u => s • c.jointChart f u) '' U) =
    Measure.map (fun u => s • c.jointChart f u) ((volume.restrict U).withDensity
      (fun u => ENNReal.ofReal (jointGramDensity (s • c.jointFrame f u 0)
        (s • c.jointFrame f u 1)))) := by
  have he : MeasurableEmbedding (fun p : Spacetime => s • p) :=
    (dilationHomeomorph s hs).measurableEmbedding
  have hm : Measurable (c.jointChart f) :=
    (hf.measurableEmbedding_lift.comp (c.measurableEmbedding_slice 0)).measurable
  have him : (fun u => s • c.jointChart f u) '' U =
      (fun p : Spacetime => s • p) '' (c.jointChart f '' U) := image_comp _ _ _
  rw [hf.inducedArea_smul_lift, Measure.restrict_smul, he.restrict_map, him,
    he.injective.preimage_image, c.jointArea_chart hf U hU hUD, Measure.map_map he.measurable hm]
  simp only [jointGramDensity_smul, ENNReal.ofReal_mul (sq_nonneg s)]
  have hd : (fun u => ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (c.jointDensity f u)) =
      ENNReal.ofReal (s ^ 2) • (fun u => ENNReal.ofReal (c.jointDensity f u)) := rfl
  change _ = Measure.map (fun u => s • c.jointChart f u)
    ((volume.restrict U).withDensity (fun u => ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (c.jointDensity f u)))
  rw [hd, withDensity_smul' _ _ ENNReal.ofReal_ne_top, Measure.map_smul]
  rfl

theorem PoincareEquiv.finite_twoFace_inducedArea (F : PoincareEquiv) {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    IsFiniteMeasure (jointInducedArea hf.toAdmissibleGraphCap (F ∘ twoFaceLift f)) := by
  rw [F.twoFace_inducedArea hf]
  letI := hf.finite_jointArea
  infer_instance

theorem AdmissibleTwoFace.finite_dilatedArea {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) (s : ℝ) :
    IsFiniteMeasure (jointInducedArea hf.toAdmissibleGraphCap (fun x => s • twoFaceLift f x)) := by
  rw [hf.inducedArea_smul_lift]
  letI := hf.finite_jointArea
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end BoundaryDraft
