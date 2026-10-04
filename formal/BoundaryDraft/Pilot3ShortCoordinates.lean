import BoundaryDraft.Pilot3NullCoordinates
import BoundaryDraft.ShortDisplacementCoordinates

/-!
# Exact short-cone null transport in physical dimension three

Only the dimension-independent time/radius change-of-variables lemmas are
reused from `ShortDisplacementCoordinates`. Spatial polar measure is r dr,
not r² dr. The ordinary full circle and the complete sharp short domain are
retained; the vertex has zero radial weight and null displacements remain.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

def pilot3ProperTimeDisplacement (ω : Pilot3Circle) (p : Plane) : Pilot3Spacetime :=
  pilot3NullPoint ω (p 1) (p 0)

theorem measurable_pilot3ProperTimeDisplacement :
    Measurable (fun p : Pilot3Circle × Plane => pilot3ProperTimeDisplacement p.1 p.2) := by
  unfold pilot3ProperTimeDisplacement pilot3NullPoint
  fun_prop

theorem pilot3_intervalSq_properTimeDisplacement (ω : Pilot3Circle) (p : Plane) (hp : p 1 ≠ 0) :
    dimensionIntervalSq 0 (pilot3ProperTimeDisplacement ω p) = p 0 := by
  simp only [dimensionIntervalSq, pilot3ProperTimeDisplacement, pilot3NullPoint,
    Prod.fst_zero, Prod.snd_zero, sub_zero, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, sq_abs]
  field_simp
  ring

/-- Ordinary polar area, with full angular measure and the linear radial weight. -/
theorem lintegral_pilot3Spatial_polar (F : Pilot3Space → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal r * F (r • ω.val)) ∂pilot3CircleMeasure := by
  have hp := (volume : Measure Pilot3Space).measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : ({(0 : Pilot3Space)}ᶜ : Set Pilot3Space), F x.val
        ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫⁻ p : Pilot3Circle × Ioi (0 : ℝ), F (p.2.val • p.1.val)
        ∂pilot3CircleMeasure.prod (Measure.volumeIoiPow 1) := by
      have ht := hp.symm (homeomorphUnitSphereProd Pilot3Space).toMeasurableEquiv
      have hh := ht.lintegral_comp (hF.comp measurable_subtype_coe)
      simpa [pilot3CircleMeasure, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace] using hh.symm
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro ω
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      simp only [pow_one]
      exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal r * F (r • ω.val))

/-- Nonnegative disintegration for arbitrary, not necessarily radial, observables. -/
theorem lintegral_pilot3Spacetime_polar (F : Pilot3Spacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z) = ∫⁻ ω, (∫⁻ p : Plane,
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal r * F (p 0, r • ω.val)) (p 1))
        ∂pilot3CircleMeasure := by
  let k := fun (t : ℝ) (ω : Pilot3Circle) (r : ℝ) => ENNReal.ofReal r * F (t, r • ω.val)
  have hk : Measurable (fun p : (ℝ × Pilot3Circle) × ℝ => k p.1.1 p.1.2 p.2) := by
    dsimp [k]
    fun_prop
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : Pilot3Space, F (t, x) := by
      rw [Measure.volume_eq_prod ℝ Pilot3Space]
      exact lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ), k t ω r) ∂pilot3CircleMeasure := by
      apply lintegral_congr
      intro t
      exact lintegral_pilot3Spatial_polar _ (hF.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ ω, (∫⁻ t : ℝ, ∫⁻ r in Ici (0 : ℝ), k t ω r) ∂pilot3CircleMeasure := by
      rw [lintegral_lintegral_swap hk.lintegral_prod_right.aemeasurable]
      simp_rw [Measure.restrict_congr_set Ioi_ae_eq_Ici]
    _ = _ := by
      apply lintegral_congr
      intro ω
      have hm : Measurable (fun p : ℝ × ℝ => (Ici (0 : ℝ)).indicator (k p.1 ω) p.2) := by
        have hh := hk.comp ((measurable_fst.prodMk (measurable_const (a := ω))).prodMk measurable_snd)
        simpa only [← indicator_comp_right, Function.comp_def] using
          hh.indicator (measurableSet_Ici.preimage measurable_snd)
      have he := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
      rw [← he.lintegral_comp (show Measurable (fun p : Plane =>
        (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal r * F (p 0, r • ω.val)) (p 1)) from
          hm.comp (volume_preserving_finTwoArrow ℝ).measurable), Measure.volume_eq_prod ℝ ℝ]
      change _ = ∫⁻ p : ℝ × ℝ, (Ici (0 : ℝ)).indicator (k p.1 ω) p.2 ∂volume.prod volume
      rw [lintegral_prod _ hm.aemeasurable]
      simp_rw [lintegral_indicator measurableSet_Ici]

theorem pilot3_polar_mem_shortFuture {δ t r : ℝ} (ω : Pilot3Circle) (hr : 0 ≤ r) :
    (t, r • ω.val) ∈ pilot3ShortFuture δ ↔ r ≤ t ∧ t + r < δ := by
  simp only [pilot3ShortFuture_eq, mem_setOf_eq, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, abs_of_nonneg hr]

/-- Exact nonnegative transport. The single zero of the 3D Jacobian at the
moving lower endpoint is kept, rather than replaced by the 4D double zero. -/
theorem lintegral_pilot3ShortFuture_properTime (δ : ℝ)
    (F : Pilot3Spacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in pilot3ShortFuture δ, F z) = ∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
      ENNReal.ofReal (pilot3NullJacobian (p 1) (p 0)) *
        F (pilot3ProperTimeDisplacement ω p)) ∂pilot3CircleMeasure := by
  rw [← lintegral_indicator (measurableSet_pilot3ShortFuture δ),
    lintegral_pilot3Spacetime_polar _ (hF.indicator (measurableSet_pilot3ShortFuture δ))]
  apply lintegral_congr
  intro ω
  have he (p : Plane) :
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal r *
        (pilot3ShortFuture δ).indicator F (p 0, r • ω.val)) (p 1) =
      (shortRadialDomain δ).indicator (fun p => ENNReal.ofReal (p 1) * F (p 0, p 1 • ω.val)) p := by
    by_cases hr : 0 ≤ p 1
    · rw [indicator_of_mem (show p 1 ∈ Ici (0 : ℝ) from hr)]
      have hm := pilot3_polar_mem_shortFuture (δ := δ) (t := p 0) ω hr
      by_cases hmem : (p 0, p 1 • ω.val) ∈ pilot3ShortFuture δ
      · obtain ⟨hrt, hc⟩ := hm.mp hmem
        rw [indicator_of_mem hmem]
        by_cases hpos : 0 < p 0 + p 1
        · rw [indicator_of_mem (show p ∈ shortRadialDomain δ from ⟨hr, hrt, hpos, hc⟩)]
        · have hz : p 1 = 0 := by linarith
          have hn : p ∉ shortRadialDomain δ := fun hp => hpos hp.2.2.1
          rw [indicator_of_not_mem hn, hz]
          simp
      · have hn : p ∉ shortRadialDomain δ := fun hp => hmem (hm.mpr ⟨hp.2.1, hp.2.2.2⟩)
        rw [indicator_of_not_mem hmem, indicator_of_not_mem hn, mul_zero]
    · have hn : p ∉ shortRadialDomain δ := fun hp => hr hp.1
      simp [hr, hn]
  simp_rw [he]
  rw [lintegral_indicator (measurableSet_shortRadialDomain δ), lintegral_shortRadial_properTime]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_shortProperTimeDomain δ)] with p hp
  have hv := hp.2.2.1
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, pilot3ProperTimeDisplacement, pilot3NullPoint]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * p 1))]
  congr 2
  rw [pilot3NullJacobian_eq hv.ne']
  ring

end BoundaryDraft
