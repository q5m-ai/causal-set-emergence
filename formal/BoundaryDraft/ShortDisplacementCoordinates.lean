import BoundaryDraft.ShortDisplacement

/-!
# Exact proper-time coordinates for short displacements

The sharp upper cutoff is the same one as `shortFuture`. The vertex has zero
radial Jacobian; all nonzero null displacements remain in the coordinate domain.
Transport is proved for nonnegative observables before any signed kernel is
inserted. No overlap regularity or asymptotic hypothesis occurs here.
-/

open MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- The proper-time-square/long-coordinate short domain, excluding only the
coordinate singularity at the vertex. -/
def shortProperTimeDomain (δ : ℝ) : Set Plane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ p 1 ^ 2 ∧ 0 < p 1 ∧ p 1 < δ}

/-- Time-radius version of the same domain. -/
def shortRadialDomain (δ : ℝ) : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ p 0 ∧ 0 < p 0 + p 1 ∧ p 0 + p 1 < δ}

theorem measurableSet_shortProperTimeDomain (δ : ℝ) :
    MeasurableSet (shortProperTimeDomain δ) := by
  exact ((isClosed_le continuous_const (continuous_apply 0)).measurableSet).inter
    (((isClosed_le (continuous_apply 0) ((continuous_apply 1).pow 2)).measurableSet).inter
      (((isOpen_lt continuous_const (continuous_apply 1)).measurableSet).inter
        (isOpen_lt (continuous_apply 1) continuous_const).measurableSet))

theorem measurableSet_shortRadialDomain (δ : ℝ) :
    MeasurableSet (shortRadialDomain δ) := by
  exact ((isClosed_le continuous_const (continuous_apply 1)).measurableSet).inter
    (((isClosed_le (continuous_apply 1) (continuous_apply 0)).measurableSet).inter
      (((isOpen_lt continuous_const ((continuous_apply 0).add (continuous_apply 1))).measurableSet).inter
        (isOpen_lt ((continuous_apply 0).add (continuous_apply 1)) continuous_const).measurableSet))

theorem properTimeRadial_image_short (δ : ℝ) :
    properTimeRadial '' shortProperTimeDomain δ = shortRadialDomain δ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hv : 0 < q 1 := hq.2.2.1
    have hs : 0 ≤ q 0 / q 1 := div_nonneg hq.1 hv.le
    have hsv : q 0 / q 1 ≤ q 1 := (div_le_iff₀ hv).mpr (by nlinarith [hq.2.1])
    change 0 ≤ (q 1 - q 0 / q 1) / 2 ∧
      (q 1 - q 0 / q 1) / 2 ≤ (q 1 + q 0 / q 1) / 2 ∧ _
    simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ⟨by linarith, by linarith, by linarith, by linarith [hq.2.2.2]⟩
  · intro hp
    have hv : 0 < p 0 + p 1 := hp.2.2.1
    refine ⟨![p 0 ^ 2 - p 1 ^ 2, p 0 + p 1], ?_, ?_⟩
    · change 0 ≤ p 0 ^ 2 - p 1 ^ 2 ∧ p 0 ^ 2 - p 1 ^ 2 ≤ (p 0 + p 1) ^ 2 ∧
        0 < p 0 + p 1 ∧ p 0 + p 1 < δ
      exact ⟨by nlinarith [hp.1, hp.2.1], by nlinarith [hp.1, hp.2.1], hv, hp.2.2.2⟩
    · have he : (p 0 ^ 2 - p 1 ^ 2) / (p 0 + p 1) = p 0 - p 1 := by
        apply (div_eq_iff hv.ne').mpr
        ring
      ext i
      fin_cases i <;> simp [properTimeRadial, he]

theorem properTimeRadial_injOn_short (δ : ℝ) :
    InjOn properTimeRadial (shortProperTimeDomain δ) := by
  intro p hp q hq he
  let ε := min (p 1) (q 1)
  have hε : 0 < ε := lt_min hp.2.2.1 hq.2.2.1
  exact properTimeRadial_injOn hε
    ⟨hp.1, hp.2.1, min_le_left _ _⟩ ⟨hq.1, hq.2.1, min_le_right _ _⟩ he

/-- Nonnegative change of variables on the complete short domain. -/
theorem lintegral_shortRadial_properTime (δ : ℝ) (f : Plane → ℝ≥0∞) :
    (∫⁻ p in shortRadialDomain δ, f p) = ∫⁻ p in shortProperTimeDomain δ,
      ENNReal.ofReal (1 / (2 * p 1)) * f (properTimeRadial p) := by
  rw [← properTimeRadial_image_short δ]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_shortProperTimeDomain δ)
    (fun p hp => (hasFDerivAt_properTimeRadial p hp.2.2.1.ne').hasFDerivWithinAt)
    (properTimeRadial_injOn_short δ)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_shortProperTimeDomain δ)] with p hp
  have hv := hp.2.2.1
  rw [det_properTimeRadialDerivative, abs_of_pos (by positivity : 0 < 1 / (2 * p 1))]

theorem polar_mem_shortFuture {δ t r : ℝ} (ω : OverlapSphere) (hr : 0 ≤ r) :
    Fin.cons t (spatialPolar ω r) ∈ shortFuture δ ↔ r ≤ t ∧ t + r < δ := by
  have hd := spatialDistance_spatialPolar ω r
  have hs : spatialSeparationSq 0 (Fin.cons t (spatialPolar ω r)) = r ^ 2 := by
    have hh := congrArg (fun a : ℝ => a ^ 2) hd
    simpa only [spatialDistance_sq, spatialSeparationSq, Pi.zero_apply, sub_zero,
      Fin.cons_succ, sq_abs] using hh
  simp only [shortFuture_eq, mem_setOf_eq, causalFuture, Pi.zero_apply, Fin.cons_zero,
    sub_zero, hs, spatialPart_cons, hd, abs_of_nonneg hr]
  constructor
  · rintro ⟨⟨ht, hrt⟩, hc⟩
    exact ⟨(sq_le_sq₀ hr ht).mp hrt, hc⟩
  · rintro ⟨hrt, hc⟩
    exact ⟨⟨hr.trans hrt, (sq_le_sq₀ hr (hr.trans hrt)).mpr hrt⟩, hc⟩

/-- Exact short-cone disintegration. The equality stratum at the upper cutoff
is absent, as specified by `shortFuture`; no positive null layer is discarded. -/
theorem lintegral_shortFuture_properTime (δ : ℝ)
    (f : Spacetime → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in shortFuture δ, f z) = ∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
      ENNReal.ofReal ((p 1 - p 0 / p 1) ^ 2 / (8 * p 1)) *
        f (properTimeDisplacement ω p)) ∂overlapSphereMeasure := by
  rw [← lintegral_indicator (measurableSet_shortFuture δ),
    lintegral_spacetime_polar _ (hf.indicator (measurableSet_shortFuture δ))]
  apply lintegral_congr
  intro ω
  have he (p : Plane) :
      (Ici (0 : ℝ)).indicator (fun r => ENNReal.ofReal (r ^ 2) *
        (shortFuture δ).indicator f (Fin.cons (p 0) (spatialPolar ω r))) (p 1) =
      (shortRadialDomain δ).indicator (fun p => ENNReal.ofReal (p 1 ^ 2) *
        f (Fin.cons (p 0) (spatialPolar ω (p 1)))) p := by
    by_cases hr : 0 ≤ p 1
    · rw [indicator_of_mem (show p 1 ∈ Ici (0 : ℝ) from hr)]
      have hm := polar_mem_shortFuture (δ := δ) (t := p 0) ω hr
      by_cases hmem : Fin.cons (p 0) (spatialPolar ω (p 1)) ∈ shortFuture δ
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
    · have hp : p ∉ shortRadialDomain δ := fun hp => hr hp.1
      simp [hr, hp]
  simp_rw [he]
  rw [lintegral_indicator (measurableSet_shortRadialDomain δ), lintegral_shortRadial_properTime]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_shortProperTimeDomain δ)] with p hp
  have hv := hp.2.2.1
  simp only [properTimeRadial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    properTimeDisplacement]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * p 1))]
  congr 2
  ring

end BoundaryDraft
