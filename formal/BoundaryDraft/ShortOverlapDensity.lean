import BoundaryDraft.ShortDisplacementCoordinates

/-!
# The actual short-displacement overlap density

The upper long-coordinate cutoff is exactly that of `shortFuture`. Nonnegative
transport precedes finite bounds and signed integration. All densities use the
original geometric `translatedOverlap`; no alternative action or overlap jet
is introduced. The apparent Jacobian singularity at zero is controlled by the
proper-time domain itself.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- Nonnegative overlap density in angular and short proper-time coordinates. -/
def shortProperTimeOverlap (M : Set Spacetime) (δ : ℝ) (ω : OverlapSphere)
    (p : Plane) : ℝ≥0∞ :=
  (shortProperTimeDomain δ).indicator (fun p =>
    ENNReal.ofReal ((p 1 - p 0 / p 1) ^ 2 / (8 * p 1)) *
      ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω p))) p

/-- The extended density, defined before any finiteness conclusion. -/
def shortOverlapDensityENN (M : Set Spacetime) (δ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ v : ℝ, shortProperTimeOverlap M δ ω ![σ,v]) ∂overlapSphereMeasure

/-- The real density for signed kernels and differences of regions. -/
def shortOverlapDensity (M : Set Spacetime) (δ σ : ℝ) : ℝ :=
  (shortOverlapDensityENN M δ σ).toReal

theorem measurable_shortProperTimeOverlap {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (fun p : OverlapSphere × Plane => shortProperTimeOverlap M δ p.1 p.2) := by
  have hj : Measurable (fun p : OverlapSphere × Plane =>
      ENNReal.ofReal ((p.2 1 - p.2 0 / p.2 1) ^ 2 / (8 * p.2 1)) *
        ENNReal.ofReal (translatedOverlap M (properTimeDisplacement p.1 p.2))) :=
    Measurable.mul (by fun_prop)
      ((measurable_translatedOverlap hm).comp measurable_properTimeDisplacement).ennreal_ofReal
  simpa only [shortProperTimeOverlap, ← indicator_comp_right, Function.comp_def] using
    hj.indicator ((measurableSet_shortProperTimeDomain δ).preimage measurable_snd)

private theorem measurable_shortPlanePair :
    Measurable (fun p : ℝ × ℝ => (![p.1,p.2] : Plane)) :=
  MeasurableEquiv.finTwoArrow.symm.measurable

private theorem measurable_shortDensityIntegrand {M : Set Spacetime}
    (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (fun p : (ℝ × OverlapSphere) × ℝ =>
      shortProperTimeOverlap M δ p.1.2 ![p.1.1,p.2]) := by
  apply (measurable_shortProperTimeOverlap hm δ).comp
    (f := fun p : (ℝ × OverlapSphere) × ℝ => (p.1.2, (![p.1.1,p.2] : Plane)))
  exact (measurable_snd.comp measurable_fst).prodMk
    (measurable_shortPlanePair.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem measurable_shortOverlapDensityENN {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (shortOverlapDensityENN M δ) :=
  (measurable_shortDensityIntegrand hm δ).lintegral_prod_right.lintegral_prod_right

theorem measurable_shortOverlapDensity {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (shortOverlapDensity M δ) :=
  (measurable_shortOverlapDensityENN hm δ).ennreal_toReal

theorem shortOverlapDensity_nonneg (M : Set Spacetime) (δ σ : ℝ) :
    0 ≤ shortOverlapDensity M δ σ := ENNReal.toReal_nonneg

private theorem lintegral_shortPlane_fibres (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p) = ∫⁻ σ : ℝ, ∫⁻ v : ℝ, f ![σ,v] := by
  have he := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  rw [← he.lintegral_comp hf, Measure.volume_eq_prod]
  exact lintegral_prod _ (hf.comp he.measurable).aemeasurable

/-- Nonnegative disintegration of the original short geometric overlap. -/
theorem lintegral_shortOverlap {M : Set Spacetime} (hm : MeasurableSet M)
    (δ : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in shortFuture δ, ENNReal.ofReal (translatedOverlap M z) * f (intervalSq 0 z)) =
      ∫⁻ σ : ℝ, shortOverlapDensityENN M δ σ * f σ := by
  have hq : Measurable (intervalSq (0 : Spacetime)) :=
    (continuous_intervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hF : Measurable (fun z => ENNReal.ofReal (translatedOverlap M z) * f (intervalSq 0 z)) :=
    (measurable_translatedOverlap hm).ennreal_ofReal.mul (hf.comp hq)
  rw [lintegral_shortFuture_properTime δ _ hF]
  have he (ω : OverlapSphere) :
      (∫⁻ p in shortProperTimeDomain δ,
        ENNReal.ofReal ((p 1 - p 0 / p 1) ^ 2 / (8 * p 1)) *
          (ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω p)) *
            f (intervalSq 0 (properTimeDisplacement ω p)))) =
        ∫⁻ p : Plane, shortProperTimeOverlap M δ ω p * f (p 0) := by
    rw [← lintegral_indicator (measurableSet_shortProperTimeDomain δ)]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ shortProperTimeDomain δ
    · simp [shortProperTimeOverlap, hp,
        intervalSq_properTimeDisplacement ω p hp.2.2.1.ne', mul_assoc]
    · simp [shortProperTimeOverlap, hp]
  change (∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
    ENNReal.ofReal ((p 1 - p 0 / p 1) ^ 2 / (8 * p 1)) *
      (ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω p)) *
        f (intervalSq 0 (properTimeDisplacement ω p)))) ∂overlapSphereMeasure) = _
  simp_rw [he]
  have hi := measurable_shortDensityIntegrand hm δ
  have hw (ω : OverlapSphere) : Measurable (shortProperTimeOverlap M δ ω) :=
    (measurable_shortProperTimeOverlap hm δ).comp
      (f := fun p : Plane => (ω,p)) (measurable_const.prodMk measurable_id)
  have hplane (ω : OverlapSphere) := lintegral_shortPlane_fibres
    (fun p => shortProperTimeOverlap M δ ω p * f (p 0))
    ((hw ω).mul (hf.comp (measurable_pi_apply 0)))
  simp_rw [hplane]
  change (∫⁻ ω, (∫⁻ σ : ℝ, ∫⁻ v : ℝ, shortProperTimeOverlap M δ ω ![σ,v] * f σ)
    ∂overlapSphereMeasure) = _
  have him : Measurable (fun p : (ℝ × OverlapSphere) × ℝ =>
      shortProperTimeOverlap M δ p.1.2 ![p.1.1,p.2] * f p.1.1) :=
    hi.mul (hf.comp (measurable_fst.comp measurable_fst))
  rw [← lintegral_lintegral_swap him.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro σ
  have hv (ω : OverlapSphere) : Measurable (fun v : ℝ => shortProperTimeOverlap M δ ω ![σ,v]) :=
    (hw ω).comp (measurable_shortPlanePair.comp (measurable_const.prodMk measurable_id))
  simp_rw [lintegral_mul_const (f σ) (hv _)]
  have hinner : Measurable (fun p : ℝ × OverlapSphere =>
      ∫⁻ v : ℝ, shortProperTimeOverlap M δ p.2 ![p.1,v]) := hi.lintegral_prod_right
  exact lintegral_mul_const _
    (hinner.comp (f := fun ω : OverlapSphere => (σ,ω)) (measurable_const.prodMk measurable_id))

/-- The upper cutoff excludes the coordinate singularity at `v = 0`.
The proper-time restriction controls the Jacobian by `δ / 8`. -/
theorem shortProperTimeJacobian_bounds {δ σ v : ℝ} (hσ : 0 ≤ σ)
    (hσv : σ ≤ v ^ 2) (hv : v ∈ Ioo 0 δ) :
    0 ≤ (v - σ / v) ^ 2 / (8 * v) ∧ (v - σ / v) ^ 2 / (8 * v) ≤ δ / 8 := by
  have hs : 0 ≤ σ / v := div_nonneg hσ hv.1.le
  have hsv : σ / v ≤ v := (div_le_iff₀ hv.1).mpr (by nlinarith)
  have hsq : (v - σ / v) ^ 2 ≤ v ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hsv) hv.1.le).mpr (sub_le_self v hs)
  refine ⟨div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hv.1.le), ?_⟩
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hv.1)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hv.2.le) hv.1.le]

/-- Pointwise finite domination on the fixed finite long-coordinate interval. -/
theorem shortProperTimeOverlap_le {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) (ω : OverlapSphere) (σ v : ℝ) :
    shortProperTimeOverlap M δ ω ![σ,v] ≤ (Ioo 0 δ).indicator
      (fun _ => ENNReal.ofReal (δ / 8 * volume.real M)) v := by
  by_cases hd : (![σ,v] : Plane) ∈ shortProperTimeDomain δ
  · have hv : v ∈ Ioo 0 δ := hd.2.2
    rw [indicator_of_mem hv, shortProperTimeOverlap, indicator_of_mem hd]
    have hj := (shortProperTimeJacobian_bounds hd.1 hd.2.1 hv).2
    have he := translatedOverlap_le_volume hm hb (properTimeDisplacement ω ![σ,v])
    calc
      _ ≤ ENNReal.ofReal (δ / 8) * ENNReal.ofReal (volume.real M) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hj) (ENNReal.ofReal_le_ofReal he)
      _ = _ := (ENNReal.ofReal_mul (by linarith [hv.1, hv.2] : 0 ≤ δ / 8)).symm
  · rw [shortProperTimeOverlap, indicator_of_not_mem hd]
    exact bot_le

/-- An explicit uniform bound, without a lower positive long cutoff. -/
theorem shortOverlapDensityENN_le {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ σ : ℝ) :
    shortOverlapDensityENN M δ σ ≤ ENNReal.ofReal (δ / 8 * volume.real M) *
      volume (Ioo 0 δ) * overlapSphereMeasure univ := by
  calc
    _ ≤ ∫⁻ _ω : OverlapSphere, (∫⁻ v : ℝ, (Ioo 0 δ).indicator
        (fun _ => ENNReal.ofReal (δ / 8 * volume.real M)) v) ∂overlapSphereMeasure :=
      lintegral_mono fun ω => lintegral_mono (shortProperTimeOverlap_le hm hb δ ω σ)
    _ = _ := by simp only [lintegral_indicator measurableSet_Ioo, lintegral_const,
      Measure.restrict_apply_univ]

theorem shortOverlapDensityENN_lt_top {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ σ : ℝ) : shortOverlapDensityENN M δ σ < ⊤ :=
  (shortOverlapDensityENN_le hm hb δ σ).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top)
      (measure_lt_top _ _))

theorem bounded_shortOverlapDensity {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |shortOverlapDensity M δ σ| ≤ C := by
  let C : ℝ≥0∞ := ENNReal.ofReal (δ / 8 * volume.real M) *
    volume (Ioo 0 δ) * overlapSphereMeasure univ
  have hC : C < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top)
      (measure_lt_top _ _)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun σ => ?_⟩
  rw [shortOverlapDensity, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hC.ne (shortOverlapDensityENN_le hm hb δ σ)

theorem shortOverlapDensityENN_negative (M : Set Spacetime) (δ : ℝ) {σ : ℝ} (hσ : σ < 0) :
    shortOverlapDensityENN M δ σ = 0 := by
  have he (ω : OverlapSphere) (v : ℝ) : shortProperTimeOverlap M δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    exact (not_le_of_gt hσ) hp.1
  simp [shortOverlapDensityENN, he]

/-- The density even vanishes at the upper endpoint, since the cutoff is strict. -/
theorem shortOverlapDensityENN_zero_of_le (M : Set Spacetime) (δ : ℝ)
    {σ : ℝ} (hσ : δ ^ 2 ≤ σ) : shortOverlapDensityENN M δ σ = 0 := by
  have he (ω : OverlapSphere) (v : ℝ) : shortProperTimeOverlap M δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    have hv : 0 < v := hp.2.2.1
    have hvδ : v < δ := hp.2.2.2
    have hsq : σ ≤ v ^ 2 := hp.2.1
    have := (sq_lt_sq₀ hv.le (hv.trans hvδ).le).mpr hvδ
    linarith
  simp only [shortOverlapDensityENN, he, lintegral_zero]

theorem support_shortOverlapDensity_subset (M : Set Spacetime) (δ : ℝ) :
    Function.support (shortOverlapDensity M δ) ⊆ Icc 0 (δ ^ 2) := by
  intro σ hσ
  by_contra hn
  by_cases hneg : σ < 0
  · exact hσ (by simp [shortOverlapDensity, shortOverlapDensityENN_negative M δ hneg])
  · have hlarge : δ ^ 2 < σ := lt_of_not_ge (fun hle => hn ⟨le_of_not_gt hneg, hle⟩)
    exact hσ (by simp [shortOverlapDensity, shortOverlapDensityENN_zero_of_le M δ hlarge.le])

theorem hasCompactSupport_shortOverlapDensity (M : Set Spacetime) (δ : ℝ) :
    HasCompactSupport (shortOverlapDensity M δ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    by_contra hs
    exact hx (support_shortOverlapDensity_subset M δ hs)

theorem shortOverlapDensity_zero_of_volume_zero {M : Set Spacetime} (hM : volume M = 0)
    (δ σ : ℝ) : shortOverlapDensity M δ σ = 0 := by
  simp [shortOverlapDensity, shortOverlapDensityENN, shortProperTimeOverlap,
    translatedOverlap_zero_of_volume_zero hM]

/-- The literal nonnegative average on nonnegative proper-time square. The
sharp upper cutoff is retained, including its omission at equality. -/
theorem shortOverlapDensityENN_eq_average (M : Set Spacetime) (δ : ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    shortOverlapDensityENN M δ σ = ∫⁻ ω, (∫⁻ v in Ioo 0 δ,
      if σ ≤ v ^ 2 then ENNReal.ofReal ((v - σ / v) ^ 2 / (8 * v)) *
        ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω ![σ,v])) else 0)
      ∂overlapSphereMeasure := by
  apply lintegral_congr
  intro ω
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro v
  have hd : (![σ,v] : Plane) ∈ shortProperTimeDomain δ ↔ σ ≤ v ^ 2 ∧ v ∈ Ioo 0 δ := by
    simp only [shortProperTimeDomain, mem_setOf_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hσ, true_and, mem_Ioo]
  by_cases hv : v ∈ Ioo 0 δ <;> by_cases hs : σ ≤ v ^ 2 <;>
    simp [shortProperTimeOverlap, hd, hv, hs]

/-- The real fibre. Its integration is only over `0 < v < δ`; the proper-time
condition then controls the apparent `1 / v` singularity. -/
def shortOverlapFibre (M : Set Spacetime) (σ : ℝ) (ω : OverlapSphere) (v : ℝ) : ℝ :=
  if σ ≤ v ^ 2 then (v - σ / v) ^ 2 / (8 * v) *
    translatedOverlap M (properTimeDisplacement ω ![σ,v]) else 0

theorem measurable_shortOverlapFibre {M : Set Spacetime} (hm : MeasurableSet M) (σ : ℝ) :
    Measurable (fun p : OverlapSphere × ℝ => shortOverlapFibre M σ p.1 p.2) := by
  have hp : Measurable (fun p : OverlapSphere × ℝ => properTimeDisplacement p.1 ![σ,p.2]) :=
    measurable_properTimeDisplacement.comp (measurable_fst.prodMk
      (measurable_shortPlanePair.comp (measurable_const.prodMk measurable_snd)))
  exact Measurable.ite
    (isClosed_le continuous_const (continuous_snd.pow 2)).measurableSet
    ((by fun_prop : Measurable (fun p : OverlapSphere × ℝ => (p.2 - σ / p.2) ^ 2 / (8 * p.2))).mul
      ((measurable_translatedOverlap hm).comp hp)) measurable_const

/-- Signed integration will use this pointwise real dominator, not a formal
exchange of totalized integrals. -/
theorem shortOverlapFibre_bounds {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (ω : OverlapSphere) (v : ℝ) (hv : v ∈ Ioo 0 δ) :
    0 ≤ shortOverlapFibre M σ ω v ∧
      shortOverlapFibre M σ ω v ≤ δ / 8 * volume.real M := by
  have hδ : 0 ≤ δ / 8 := by linarith [hv.1, hv.2]
  by_cases hs : σ ≤ v ^ 2
  · rw [shortOverlapFibre, if_pos hs]
    have hj := shortProperTimeJacobian_bounds hσ hs hv
    exact ⟨mul_nonneg hj.1 (translatedOverlap_nonneg M _),
      mul_le_mul hj.2 (translatedOverlap_le_volume hm hb _)
        (translatedOverlap_nonneg M _) hδ⟩
  · rw [shortOverlapFibre, if_neg hs]
    exact ⟨le_rfl, mul_nonneg hδ ENNReal.toReal_nonneg⟩

/-- Every fibre, not merely almost every direction, is absolutely integrable. -/
theorem integrableOn_shortOverlapFibre {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (ω : OverlapSphere) :
    IntegrableOn (shortOverlapFibre M σ ω) (Ioo 0 δ) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  apply (integrable_const (δ / 8 * volume.real M)).mono'
    (((measurable_shortOverlapFibre hm σ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hbnd := shortOverlapFibre_bounds hm hb δ hσ ω v hv
  change ‖shortOverlapFibre M σ ω v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg hbnd.1]
  exact hbnd.2

/-- Joint absolute integrability before the real angular/long-coordinate
Fubini interchange. This includes measurability for the actual overlap. -/
theorem integrable_shortOverlapFibre {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (fun p : OverlapSphere × ℝ => shortOverlapFibre M σ p.1 p.2)
      (overlapSphereMeasure.prod (volume.restrict (Ioo 0 δ))) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hv : ∀ᵐ p : OverlapSphere × ℝ
      ∂overlapSphereMeasure.prod (volume.restrict (Ioo 0 δ)), p.2 ∈ Ioo 0 δ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)
  apply (integrable_const (δ / 8 * volume.real M)).mono'
    (measurable_shortOverlapFibre hm σ).aestronglyMeasurable
  filter_upwards [hv] with p hp
  have hbnd := shortOverlapFibre_bounds hm hb δ hσ p.1 p.2 hp
  rw [Real.norm_eq_abs, abs_of_nonneg hbnd.1]
  exact hbnd.2

/-- The real fibre formula, after establishing both pointwise finiteness of
the ENNReal density and joint absolute integrability of the displayed fibre. -/
theorem shortOverlapDensity_eq_average {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    shortOverlapDensity M δ σ = ∫ ω, (∫ v in Ioo 0 δ,
      if σ ≤ v ^ 2 then (v - σ / v) ^ 2 / (8 * v) *
        translatedOverlap M (properTimeDisplacement ω ![σ,v]) else 0) ∂overlapSphereMeasure := by
  let μ := overlapSphereMeasure.prod (volume.restrict (Ioo 0 δ))
  have hi := integrable_shortOverlapFibre hm hb δ hσ
  have hn : ∀ᵐ p : OverlapSphere × ℝ ∂μ, 0 ≤ shortOverlapFibre M σ p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const (measurable_shortOverlapFibre hm σ))).mpr
    exact Filter.Eventually.of_forall fun ω => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact (shortOverlapFibre_bounds hm hb δ hσ ω v hv).1
  have he : shortOverlapDensityENN M δ σ =
      ∫⁻ p : OverlapSphere × ℝ, ENNReal.ofReal (shortOverlapFibre M σ p.1 p.2) ∂μ := by
    rw [shortOverlapDensityENN_eq_average M δ hσ,
      lintegral_prod _ (measurable_shortOverlapFibre hm σ).ennreal_ofReal.aemeasurable]
    apply lintegral_congr
    intro ω
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    by_cases hs : σ ≤ v ^ 2
    · simp only [hs, if_true, shortOverlapFibre]
      exact (ENNReal.ofReal_mul (shortProperTimeJacobian_bounds hσ hs hv).1).symm
    · simp only [hs, if_false, shortOverlapFibre, ENNReal.ofReal_zero]
  change (shortOverlapDensityENN M δ σ).toReal = _
  rw [he, ← integral_eq_lintegral_of_nonneg_ae hn
    (measurable_shortOverlapFibre hm σ).aestronglyMeasurable]
  exact integral_prod _ hi

/-- Finite mass is inherited from the actual bounded geometric overlap. -/
theorem lintegral_shortOverlapDensityENN_lt_top {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) : (∫⁻ σ, shortOverlapDensityENN M δ σ) < ⊤ := by
  have hi : IntegrableOn (translatedOverlap M) (shortFuture δ) := by
    simpa only [one_mul] using integrableOn_short_overlap hm hb δ (fun _ => 1) continuous_const
  have he := lintegral_shortOverlap hm δ (fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (translatedOverlap_nonneg M))]
  exact ENNReal.ofReal_lt_top

theorem integrable_shortOverlapDensity {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) : Integrable (shortOverlapDensity M δ) :=
  integrable_toReal_of_lintegral_ne_top (measurable_shortOverlapDensityENN hm δ).aemeasurable
    (lintegral_shortOverlapDensityENN_lt_top hm hb δ).ne

/-- Geometric short overlap measure on the original spacetime, independent of
its proper-time density. -/
def shortOverlapMeasure (M : Set Spacetime) (δ : ℝ) : Measure Spacetime :=
  (volume.restrict (shortFuture δ)).withDensity (fun z => ENNReal.ofReal (translatedOverlap M z))

theorem map_shortOverlapMeasure {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measure.map (intervalSq 0) (shortOverlapMeasure M δ) =
      volume.withDensity (shortOverlapDensityENN M δ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hq : Measurable (intervalSq (0 : Spacetime)) :=
    (continuous_intervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hg : Measurable (fun z => f (intervalSq 0 z)) := hf.comp hq
  rw [lintegral_map hf hq, shortOverlapMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_translatedOverlap hm).ennreal_ofReal hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_shortOverlapDensityENN hm δ) hf]
  exact lintegral_shortOverlap hm δ f hf

/-- Absolute integrability is proved before inserting a signed continuous kernel. -/
theorem integrable_shortOverlapDensity_weight {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun σ => f σ * shortOverlapDensity M δ σ) := by
  have hq : Continuous (intervalSq (0 : Spacetime)) :=
    continuous_intervalSq.comp (continuous_const.prodMk continuous_id)
  have hi := integrableOn_short_overlap hm hb δ (fun z => f (intervalSq 0 z)) (hf.comp hq)
  have hfinite : ∀ᵐ z ∂volume.restrict (shortFuture δ), ENNReal.ofReal (translatedOverlap M z) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi' : Integrable (fun z => f (intervalSq 0 z)) (shortOverlapMeasure M δ) := by
    apply (integrable_withDensity_iff (measurable_translatedOverlap hm).ennreal_ofReal hfinite).mpr
    simpa only [ENNReal.toReal_ofReal (translatedOverlap_nonneg M _)] using hi
  have hif : Integrable f (Measure.map (intervalSq 0) (shortOverlapMeasure M δ)) :=
    (integrable_map_measure hf.measurable.aestronglyMeasurable hq.measurable.aemeasurable).mpr hi'
  rw [map_shortOverlapMeasure hm δ] at hif
  exact (integrable_withDensity_iff (measurable_shortOverlapDensityENN hm δ)
    (Filter.Eventually.of_forall (shortOverlapDensityENN_lt_top hm hb δ))).mp hif

/-- Exact signed finite-density identity for the actual original region. -/
theorem integral_shortOverlap {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in shortFuture δ, f (intervalSq 0 z) * translatedOverlap M z) =
      ∫ σ : ℝ, f σ * shortOverlapDensity M δ σ := by
  have hq : Measurable (intervalSq (0 : Spacetime)) :=
    (continuous_intervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have he : (∫ σ, f σ ∂Measure.map (intervalSq 0) (shortOverlapMeasure M δ)) =
      ∫ z in shortFuture δ, f (intervalSq 0 z) * translatedOverlap M z := by
    rw [integral_map hq.aemeasurable hf.measurable.aestronglyMeasurable, shortOverlapMeasure,
      integral_withDensity_eq_integral_toReal_smul₀
        (measurable_translatedOverlap hm).ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (translatedOverlap_nonneg M _), smul_eq_mul, mul_comm]
  rw [← he, map_shortOverlapMeasure hm δ,
    integral_withDensity_eq_integral_toReal_smul₀ (measurable_shortOverlapDensityENN hm δ).aemeasurable
      (Filter.Eventually.of_forall (shortOverlapDensityENN_lt_top hm hb δ))]
  simp only [shortOverlapDensity, smul_eq_mul, mul_comm]

/-- The entire signed BDG kernel, with its original normalization. -/
theorem integral_shortOverlap_bdg {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ ρ : ℝ) :
    (∫ z in shortFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap M z) =
      ∫ σ : ℝ, bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) * shortOverlapDensity M δ σ := by
  apply integral_shortOverlap hm hb δ (fun σ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))
  unfold bdgKernel bdgPolynomial
  fun_prop

theorem shortContinuumMean_eq_density {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ δ : ℝ) :
    shortContinuumMean ρ δ M = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real M - ρ * ∫ σ : ℝ,
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) * shortOverlapDensity M δ σ) := by
  rw [shortContinuumMean, integral_shortOverlap_bdg hm hb δ ρ]

/-- A difference of actual regions may be taken only after the separately
integrable nonnegative densities have been constructed. -/
theorem integral_shortOverlap_sub {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in shortFuture δ, f (intervalSq 0 z) *
      (translatedOverlap M z - translatedOverlap N z)) =
      ∫ σ : ℝ, f σ * (shortOverlapDensity M δ σ - shortOverlapDensity N δ σ) := by
  have hw : Continuous (fun z => f (intervalSq (0 : Spacetime) z)) :=
    hf.comp (continuous_intervalSq.comp (continuous_const.prodMk continuous_id))
  simp_rw [mul_sub]
  rw [integral_sub (integrableOn_short_overlap hm hb δ _ hw)
      (integrableOn_short_overlap hn hnb δ _ hw),
    integral_sub (integrable_shortOverlapDensity_weight hm hb δ f hf)
      (integrable_shortOverlapDensity_weight hn hnb δ f hf),
    integral_shortOverlap hm hb δ f hf, integral_shortOverlap hn hnb δ f hf]

/-- The real fibre formula for region differences, including the planar
comparison used downstream. No signed density is sent through `toReal`. -/
theorem shortOverlapDensity_sub_eq_average {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    shortOverlapDensity M δ σ - shortOverlapDensity N δ σ =
      ∫ ω, (∫ v in Ioo 0 δ, if σ ≤ v ^ 2 then (v - σ / v) ^ 2 / (8 * v) *
        (translatedOverlap M (properTimeDisplacement ω ![σ,v]) -
          translatedOverlap N (properTimeDisplacement ω ![σ,v])) else 0) ∂overlapSphereMeasure := by
  rw [shortOverlapDensity_eq_average hm hb δ hσ, shortOverlapDensity_eq_average hn hnb δ hσ]
  change (∫ ω, (∫ v in Ioo 0 δ, shortOverlapFibre M σ ω v) ∂overlapSphereMeasure) -
    (∫ ω, (∫ v in Ioo 0 δ, shortOverlapFibre N σ ω v) ∂overlapSphereMeasure) = _
  rw [← integral_sub (integrable_shortOverlapFibre hm hb δ hσ).integral_prod_left
    (integrable_shortOverlapFibre hn hnb δ hσ).integral_prod_left]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only
    rw [← integral_sub (integrableOn_shortOverlapFibre hm hb δ hσ ω)
      (integrableOn_shortOverlapFibre hn hnb δ hσ ω)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v _
    by_cases hs : σ ≤ v ^ 2 <;> simp [shortOverlapFibre, hs, mul_sub]

namespace AdmissibleTwoFace

/-- Specialization to the unchanged two-face region and signed BDG kernel. -/
theorem integral_shortOverlap_bdg {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (δ ρ : ℝ) :
    (∫ z in shortFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ, bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) *
        shortOverlapDensity (twoFaceRegion h f) δ σ :=
  BoundaryDraft.integral_shortOverlap_bdg hf.measurableSet_region hf.isBounded_region δ ρ

theorem shortContinuumMean_eq_density {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (ρ δ : ℝ) :
    shortContinuumMean ρ δ (twoFaceRegion h f) = (4 / Real.sqrt 6) * Real.sqrt ρ *
      (volume.real (twoFaceRegion h f) - ρ * ∫ σ : ℝ,
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) * shortOverlapDensity (twoFaceRegion h f) δ σ) :=
  BoundaryDraft.shortContinuumMean_eq_density hf.measurableSet_region hf.isBounded_region ρ δ

end AdmissibleTwoFace
end BoundaryDraft
