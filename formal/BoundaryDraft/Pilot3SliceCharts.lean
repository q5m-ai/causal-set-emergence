import BoundaryDraft.Pilot3ChartTransport

/-!
# Canonical curve-measure transport on height slices

The inverse cutoff gives an actual global smooth graph representing each
local slice. Its derivative speed is the same tangential factor appearing
in the ambient determinant, and its area law uses the fixed spatial measure.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
noncomputable section
namespace BoundaryDraft

structure Pilot3SliceChart (h : Pilot3Space → ℝ) extends Pilot3HeightChart h where
  center : Pilot3Space
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball center radius ⊆ chart.target
  inverseExtension : Pilot3Space → Pilot3Space
  contDiff_extension : ContDiff ℝ ∞ inverseExtension
  extension_eq : EqOn inverseExtension chart.symm (Metric.ball center radius)

theorem Pilot3RegularHeight.exists_sliceChart {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
    (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) (hr : fderiv ℝ h x ≠ 0) :
    ∃ c : Pilot3SliceChart h, x ∈ c.chart.source ∧ c.center = c.chart x := by
  obtain ⟨c, hxC⟩ := hh.exists_heightChart x hx hr
  obtain ⟨k, r, hk, hr, hball, he⟩ := c.exists_inverse_extension _ (c.chart.map_source hxC)
  exact ⟨{
    toPilot3HeightChart := c
    center := c.chart x
    radius := r
    radius_pos := hr
    ball_subset := hball
    inverseExtension := k
    contDiff_extension := hk
    extension_eq := he }, hxC, rfl⟩

private theorem pilot3CurveLinear_zero_one : pilot3CurveLinear 0 1 = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  ext i
  fin_cases i <;> simp [pilot3CurveLinear, pilot3Coordinates, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

theorem pilot3_hausdorff_isometry_image (R : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space) (s : Set Pilot3Space) :
    (μH[1] : Measure Pilot3Space).restrict (R '' s) = Measure.map R ((μH[1] : Measure Pilot3Space).restrict s) := by
  have hm : Measure.map R (μH[1] : Measure Pilot3Space) = μH[1] := R.toIsometryEquiv.map_hausdorffMeasure 1
  have he := R.toHomeomorph.measurableEmbedding.restrict_map (μH[1] : Measure Pilot3Space) (R '' s)
  change (Measure.map R (μH[1] : Measure Pilot3Space)).restrict (R '' s) =
    Measure.map R ((μH[1] : Measure Pilot3Space).restrict (R ⁻¹' (R '' s))) at he
  rw [hm, R.injective.preimage_image] at he
  exact he

namespace Pilot3SliceChart
variable {h : Pilot3Space → ℝ} (c : Pilot3SliceChart h)

def scalarSlice (t u : ℝ) : ℝ := c.rotation (c.inverseExtension (pilot3Curve (fun _ => t) u)) 0

def slice (t u : ℝ) : Pilot3Space := c.rotation.symm (pilot3Curve (c.scalarSlice t) u)

def sliceDomain (t : ℝ) : Set ℝ := (pilot3Curve (fun _ => t)) ⁻¹' Metric.ball c.center c.radius

theorem isOpen_sliceDomain (t : ℝ) : IsOpen (c.sliceDomain t) :=
  Metric.isOpen_ball.preimage (continuous_pilot3Curve continuous_const)

theorem contDiff_scalarSlice (t : ℝ) : ContDiff ℝ ∞ (c.scalarSlice t) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff.comp
    (c.rotation.contDiff.comp (c.contDiff_extension.comp
      (pilot3Coordinates.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))))

theorem contDiff_slice (t : ℝ) : ContDiff ℝ ∞ (c.slice t) :=
  c.rotation.symm.contDiff.comp (pilot3Coordinates.symm.contDiff.comp
    ((c.contDiff_scalarSlice t).prodMk contDiff_id))

theorem continuous_slice (t : ℝ) : Continuous (c.slice t) := (c.contDiff_slice t).continuous

theorem measurableEmbedding_slice (t : ℝ) : MeasurableEmbedding (c.slice t) :=
  c.rotation.symm.toHomeomorph.measurableEmbedding.comp
    (continuous_measurableEmbedding_pilot3Curve (c.contDiff_scalarSlice t).continuous)

theorem slice_eq_symm (t u : ℝ) (hu : u ∈ c.sliceDomain t) :
    c.slice t u = c.chart.symm (pilot3Curve (fun _ => t) u) := by
  apply c.rotation.injective
  rw [slice, c.rotation.apply_symm_apply]
  have hb := c.base_symm _ (c.ball_subset hu)
  ext i
  fin_cases i
  · change c.rotation (c.inverseExtension (pilot3Curve (fun _ => t) u)) 0 = _
    rw [c.extension_eq hu]
    rfl
  · exact hb.symm

/-- Actual inverse tangent derivative in the fixed coordinate direction. -/
theorem hasDerivAt_slice (t u : ℝ) (hu : u ∈ c.sliceDomain t) :
    HasDerivAt (c.slice t)
      (fderiv ℝ c.chart.symm (pilot3Curve (fun _ => t) u) (EuclideanSpace.basisFun (Fin 2) ℝ 1)) u := by
  have hi := (c.hasFDerivAt_symm _ (c.ball_subset hu)).comp u
    (hasStrictFDerivAt_pilot3Curve _ _ _ (hasStrictFDerivAt_const t u)).hasFDerivAt
  have he : c.slice t =ᶠ[𝓝 u] (fun v => c.chart.symm (pilot3Curve (fun _ => t) v)) :=
    mem_of_superset ((c.isOpen_sliceDomain t).mem_nhds hu) (fun v hv => c.slice_eq_symm t v hv)
  simpa only [ContinuousLinearMap.comp_apply, pilot3CurveLinear_zero_one] using
    (hi.congr_of_eventuallyEq he).hasDerivAt

theorem scalarSlice_jacobian (t u : ℝ) (hu : u ∈ c.sliceDomain t) :
    pilot3CurveJacobian (c.scalarSlice t) u = c.sliceJacobian (pilot3Curve (fun _ => t) u) := by
  let G := pilot3CurveLinear (fderiv ℝ (c.scalarSlice t) u)
  have hg : HasFDerivAt (c.slice t) (c.rotation.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp G) u :=
    c.rotation.symm.toContinuousLinearEquiv.hasFDerivAt.comp u
      (hasStrictFDerivAt_pilot3Curve _ _ _
        ((c.contDiff_scalarSlice t).contDiffAt.hasStrictFDerivAt (by simp))).hasFDerivAt
  have he := (c.hasDerivAt_slice t u hu).unique hg.hasDerivAt
  change ‖G 1‖ = ‖fderiv ℝ c.chart.symm (pilot3Curve (fun _ => t) u) (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖
  rw [he]
  exact (c.rotation.symm.norm_map (G 1)).symm

theorem hausdorff_slice_image (t : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (μH[1] : Measure Pilot3Space).restrict (c.slice t '' s) =
      Measure.map (c.slice t) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (pilot3CurveJacobian (c.scalarSlice t) u))) := by
  change (μH[1] : Measure Pilot3Space).restrict ((c.rotation.symm ∘ pilot3Curve (c.scalarSlice t)) '' s) = _
  rw [image_comp, pilot3_hausdorff_isometry_image,
    pilot3_hausdorff_restrict_curve_image ((c.contDiff_scalarSlice t).of_le (by simp)) s hs,
    Measure.map_map c.rotation.symm.continuous.measurable
      (continuous_pilot3Curve (c.contDiff_scalarSlice t).continuous).measurable]
  rfl

theorem slice_mem_level (t : ℝ) (ht : 0 ≤ t) (u : ℝ) (hu : u ∈ c.sliceDomain t) :
    c.slice t u ∈ pilot3Level h t := by
  rw [c.slice_eq_symm t u hu]
  exact ⟨c.symm_mem_closedPositive _ (c.ball_subset hu) ht, c.height_symm _ (c.ball_subset hu)⟩

theorem slice_mem_joint (u : ℝ) (hu : u ∈ c.sliceDomain 0) : c.slice 0 u ∈ pilot3SpatialJoint h :=
  c.slice_mem_level 0 le_rfl u hu

/-- The canonical level measure, not an atlas-defined substitute. -/
theorem levelMeasure_slice_image (t : ℝ) (ht : 0 ≤ t) (s : Set ℝ) (hs : MeasurableSet s)
    (hsD : s ⊆ c.sliceDomain t) :
    (pilot3LevelMeasure h t).restrict (c.slice t '' s) =
      Measure.map (c.slice t) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (c.sliceJacobian (pilot3Curve (fun _ => t) u)))) := by
  have hsub : c.slice t '' s ⊆ pilot3Level h t := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_level t ht u (hsD hu)
  rw [pilot3LevelMeasure, Measure.restrict_restrict_of_subset hsub, c.hausdorff_slice_image t s hs]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [c.scalarSlice_jacobian t u (hsD hu)]

theorem integral_levelMeasure_slice_image (t : ℝ) (ht : 0 ≤ t) (s : Set ℝ) (hs : MeasurableSet s)
    (hsD : s ⊆ c.sliceDomain t) (F : Pilot3Space → ℝ) :
    (∫ x in c.slice t '' s, F x ∂pilot3LevelMeasure h t) =
      ∫ u in s, c.sliceJacobian (pilot3Curve (fun _ => t) u) * F (c.slice t u) := by
  have hsub : c.slice t '' s ⊆ pilot3Level h t := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_level t ht u (hsD hu)
  rw [pilot3LevelMeasure, Measure.restrict_restrict_of_subset hsub, c.hausdorff_slice_image t s hs,
    (c.measurableEmbedding_slice t).integral_map,
    integral_withDensity_eq_integral_toReal_smul (measurable_pilot3CurveJacobian _).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun hs
  intro u hu
  dsimp only
  rw [ENNReal.toReal_ofReal (pilot3CurveJacobian_pos _ _).le, smul_eq_mul, c.scalarSlice_jacobian t u (hsD hu)]

theorem integrableOn_levelMeasure_slice_image_iff (t : ℝ) (ht : 0 ≤ t) (s : Set ℝ)
    (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain t) (F : Pilot3Space → ℝ) :
    IntegrableOn F (c.slice t '' s) (pilot3LevelMeasure h t) ↔
      IntegrableOn (fun u => c.sliceJacobian (pilot3Curve (fun _ => t) u) * F (c.slice t u)) s := by
  have hsub : c.slice t '' s ⊆ pilot3Level h t := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_level t ht u (hsD hu)
  unfold IntegrableOn
  rw [pilot3LevelMeasure, Measure.restrict_restrict_of_subset hsub, c.hausdorff_slice_image t s hs,
    (c.measurableEmbedding_slice t).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul' (measurable_pilot3CurveJacobian _).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [ENNReal.toReal_ofReal (pilot3CurveJacobian_pos _ _).le, smul_eq_mul, c.scalarSlice_jacobian t u (hsD hu)]
  rfl

end Pilot3SliceChart
end BoundaryDraft
