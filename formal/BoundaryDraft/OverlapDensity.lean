import BoundaryDraft.OverlapCoordinates

/-!
# The actual long-displacement overlap density

At a fixed positive cutoff this is the angular and long-coordinate average of
the geometric overlap, not an assumed Taylor polynomial. Nonnegative measure
transport is established before using any signed test kernel.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal Classical

noncomputable section
namespace BoundaryDraft

/-- The displacement corresponding to `(sigma,v,omega)`. -/
def properTimeDisplacement (ω : OverlapSphere) (p : Plane) : Spacetime :=
  Fin.cons ((p 1 + p 0 / p 1)/2) (spatialPolar ω ((p 1 - p 0 / p 1)/2))

theorem measurable_properTimeDisplacement :
    Measurable (fun p : OverlapSphere × Plane => properTimeDisplacement p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Measurable (fun p : OverlapSphere × Plane => (p.2 1 + p.2 0 / p.2 1)/2)
    fun_prop
  · change Measurable (fun p : OverlapSphere × Plane =>
      spatialPolar p.1 ((p.2 1 - p.2 0 / p.2 1)/2) j)
    exact (measurable_pi_apply j).comp (measurable_spatialPolar.comp
      (measurable_fst.prodMk (by fun_prop)))

theorem intervalSq_properTimeDisplacement (ω : OverlapSphere) (p : Plane) (hp : p 1 ≠ 0) :
    intervalSq 0 (properTimeDisplacement ω p) = p 0 := by
  have h := radialNull_intervalSq (p 0 / p 1) (p 1) ω
  simpa only [properTimeDisplacement, add_comm (p 0 / p 1), div_mul_cancel₀ _ hp] using h

/-- Nonnegative density in angular and `(sigma,v)` coordinates. -/
def properTimeOverlap (M : Set Spacetime) (δ : ℝ) (ω : OverlapSphere) (p : Plane) : ℝ≥0∞ :=
  (properTimeDomain δ).indicator (fun p =>
    ENNReal.ofReal ((p 1 - p 0 / p 1)^2 / (8 * p 1)) *
      ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω p))) p

/-- An extended nonnegative density permits measure transport to be proved
without assuming finiteness. Finiteness almost everywhere is derived below. -/
def longOverlapDensityENN (M : Set Spacetime) (δ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ v : ℝ, properTimeOverlap M δ ω ![σ,v]) ∂overlapSphereMeasure

/-- The real density used with signed kernels. -/
def longOverlapDensity (M : Set Spacetime) (δ σ : ℝ) : ℝ :=
  (longOverlapDensityENN M δ σ).toReal

theorem measurable_properTimeOverlap {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (fun p : OverlapSphere × Plane => properTimeOverlap M δ p.1 p.2) := by
  have hj : Measurable (fun p : OverlapSphere × Plane =>
      ENNReal.ofReal ((p.2 1 - p.2 0 / p.2 1)^2 / (8 * p.2 1)) *
        ENNReal.ofReal (translatedOverlap M (properTimeDisplacement p.1 p.2))) :=
    Measurable.mul (by fun_prop)
      ((measurable_translatedOverlap hm).comp measurable_properTimeDisplacement).ennreal_ofReal
  simpa only [properTimeOverlap, ← indicator_comp_right, Function.comp_def] using
    hj.indicator ((measurableSet_properTimeDomain δ).preimage measurable_snd)

private theorem measurable_planePair : Measurable (fun p : ℝ × ℝ => (![p.1,p.2] : Plane)) :=
  MeasurableEquiv.finTwoArrow.symm.measurable

private theorem measurable_densityIntegrand {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (fun p : (ℝ × OverlapSphere) × ℝ => properTimeOverlap M δ p.1.2 ![p.1.1,p.2]) := by
  apply (measurable_properTimeOverlap hm δ).comp
    (f := fun p : (ℝ × OverlapSphere) × ℝ => (p.1.2, (![p.1.1,p.2] : Plane)))
  exact (measurable_snd.comp measurable_fst).prodMk
    (measurable_planePair.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem measurable_longOverlapDensityENN {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (longOverlapDensityENN M δ) :=
  (measurable_densityIntegrand hm δ).lintegral_prod_right.lintegral_prod_right

theorem measurable_longOverlapDensity {M : Set Spacetime} (hm : MeasurableSet M) (δ : ℝ) :
    Measurable (longOverlapDensity M δ) :=
  (measurable_longOverlapDensityENN hm δ).ennreal_toReal

theorem longOverlapDensityENN_negative (M : Set Spacetime) (δ : ℝ) {σ : ℝ} (hσ : σ < 0) :
    longOverlapDensityENN M δ σ = 0 := by
  have he (ω : OverlapSphere) (v : ℝ) : properTimeOverlap M δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    exact (not_le_of_gt hσ) hp.1
  simp [longOverlapDensityENN, he]

private theorem lintegral_plane_fibres (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p) = ∫⁻ u : ℝ, ∫⁻ v : ℝ, f ![u,v] := by
  have he := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  rw [← he.lintegral_comp hf, Measure.volume_eq_prod]
  exact lintegral_prod _ (hf.comp he.measurable).aemeasurable

/-- Nonnegative transport proves that this particular averaged density is
actually the proper-time disintegration of the geometric long overlap. -/
theorem lintegral_longOverlap {M : Set Spacetime} (hm : MeasurableSet M)
    {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in longFuture δ, ENNReal.ofReal (translatedOverlap M z) * f (intervalSq 0 z)) =
      ∫⁻ σ : ℝ, longOverlapDensityENN M δ σ * f σ := by
  have hq : Measurable (intervalSq (0 : Spacetime)) :=
    (continuous_intervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hF : Measurable (fun z => ENNReal.ofReal (translatedOverlap M z) * f (intervalSq 0 z)) :=
    (measurable_translatedOverlap hm).ennreal_ofReal.mul (hf.comp hq)
  rw [lintegral_longFuture_properTime hδ _ hF]
  have he (ω : OverlapSphere) :
      (∫⁻ p in properTimeDomain δ,
        ENNReal.ofReal ((p 1-p 0/p 1)^2/(8*p 1)) *
          (ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω p)) *
            f (intervalSq 0 (properTimeDisplacement ω p)))) =
        ∫⁻ p : Plane, properTimeOverlap M δ ω p * f (p 0) := by
    rw [← lintegral_indicator (measurableSet_properTimeDomain δ)]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ properTimeDomain δ
    · simp [properTimeOverlap, hp, intervalSq_properTimeDisplacement ω p (hδ.trans_le hp.2.2).ne', mul_assoc]
    · simp [properTimeOverlap, hp]
  change (∫⁻ ω, (∫⁻ p in properTimeDomain δ,
    ENNReal.ofReal ((p 1-p 0/p 1)^2/(8*p 1)) *
      (ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω p)) *
        f (intervalSq 0 (properTimeDisplacement ω p)))) ∂overlapSphereMeasure) = _
  simp_rw [he]
  have hi := measurable_densityIntegrand hm δ
  have hw (ω : OverlapSphere) : Measurable (properTimeOverlap M δ ω) :=
    (measurable_properTimeOverlap hm δ).comp
      (f := fun p : Plane => (ω,p)) (measurable_const.prodMk measurable_id)
  have hplane (ω : OverlapSphere) := lintegral_plane_fibres
    (fun p => properTimeOverlap M δ ω p * f (p 0))
    ((hw ω).mul (hf.comp (measurable_pi_apply 0)))
  simp_rw [hplane]
  change (∫⁻ ω, (∫⁻ σ : ℝ, ∫⁻ v : ℝ, properTimeOverlap M δ ω ![σ,v] * f σ)
    ∂overlapSphereMeasure) = _
  have him : Measurable (fun p : (ℝ × OverlapSphere) × ℝ =>
      properTimeOverlap M δ p.1.2 ![p.1.1,p.2] * f p.1.1) :=
    hi.mul (hf.comp (measurable_fst.comp measurable_fst))
  rw [← lintegral_lintegral_swap him.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro σ
  have hv (ω : OverlapSphere) : Measurable (fun v : ℝ => properTimeOverlap M δ ω ![σ,v]) :=
    (hw ω).comp (measurable_planePair.comp (measurable_const.prodMk measurable_id))
  simp_rw [lintegral_mul_const (f σ) (hv _)]
  have hinner : Measurable (fun p : ℝ × OverlapSphere =>
      ∫⁻ v : ℝ, properTimeOverlap M δ p.2 ![p.1,v]) := hi.lintegral_prod_right
  exact lintegral_mul_const _
    (hinner.comp (f := fun ω : OverlapSphere => (σ,ω)) (measurable_const.prodMk measurable_id))

/-- The explicit averaged-overlap formula on nonnegative proper-time square.
The lower limit simultaneously enforces the cutoff and `u ≤ v`. -/
theorem longOverlapDensityENN_eq_average (M : Set Spacetime) {δ : ℝ} (hδ : 0 < δ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    longOverlapDensityENN M δ σ = ∫⁻ ω, (∫⁻ v in Ici (max δ (Real.sqrt σ)),
      ENNReal.ofReal ((v-σ/v)^2/(8*v)) *
        ENNReal.ofReal (translatedOverlap M (properTimeDisplacement ω ![σ,v])))
      ∂overlapSphereMeasure := by
  apply lintegral_congr
  intro ω
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro v
  have hm : (![σ,v] : Plane) ∈ properTimeDomain δ ↔ v ∈ Ici (max δ (Real.sqrt σ)) := by
    simp only [properTimeDomain, mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mem_Ici, max_le_iff]
    constructor
    · rintro ⟨_, hsv, hv⟩
      exact ⟨hv, (sq_le_sq₀ (Real.sqrt_nonneg σ) (hδ.le.trans hv)).mp
        (by simpa only [Real.sq_sqrt hσ] using hsv)⟩
    · rintro ⟨hv, hs⟩
      exact ⟨hσ, by nlinarith [Real.sq_sqrt hσ, Real.sqrt_nonneg σ], hv⟩
  by_cases hv : v ∈ Ici (max δ (Real.sqrt σ)) <;> simp [properTimeOverlap, hm, hv]

/-- Bounded spacetime support also bounds the effective long coordinate. -/
theorem properTimeOverlap_zero_of_long_lt {M : Set Spacetime} (hb : Bornology.IsBounded M)
    {δ : ℝ} (hδ : 0 < δ) (ω : OverlapSphere) (p : Plane)
    (hp : 2 * Metric.diam M < p 1) : properTimeOverlap M δ ω p = 0 := by
  by_cases hd : p ∈ properTimeDomain δ
  · have hv := hδ.trans_le hd.2.2
    have hq : 0 ≤ p 0 / p 1 := div_nonneg hd.1 hv.le
    have hn := norm_le_pi_norm (properTimeDisplacement ω p) 0
    have ht : (properTimeDisplacement ω p) 0 = (p 1 + p 0/p 1)/2 := rfl
    have hnorm : Metric.diam M < ‖properTimeDisplacement ω p‖ := by
      have hab := le_abs_self ((properTimeDisplacement ω p) 0)
      rw [Real.norm_eq_abs] at hn
      rw [ht] at hab hn
      linarith
    simp [properTimeOverlap, hd, translatedOverlap_eq_zero_of_diam_lt hb hnorm]
  · exact indicator_of_not_mem hd _

/-- A pointwise finite dominator on a fixed finite long-coordinate interval.
It is uniform in proper-time square and direction. -/
theorem properTimeOverlap_le {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) (ω : OverlapSphere) (σ v : ℝ) :
    properTimeOverlap M δ ω ![σ,v] ≤ (Icc δ (2 * Metric.diam M)).indicator
      (fun _ => ENNReal.ofReal (Metric.diam M / 4 * volume.real M)) v := by
  by_cases hd : (![σ,v] : Plane) ∈ properTimeDomain δ
  · have hvδ : δ ≤ v := hd.2.2
    have hv : 0 < v := hδ.trans_le hvδ
    have hs : 0 ≤ σ := hd.1
    have hsq : σ ≤ v^2 := hd.2.1
    have hsv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith [hsq])
    by_cases hbound : v ≤ 2 * Metric.diam M
    · rw [indicator_of_mem (show v ∈ Icc δ (2 * Metric.diam M) from ⟨hvδ,hbound⟩),
        properTimeOverlap, indicator_of_mem hd]
      have hj : (v-σ/v)^2/(8*v) ≤ Metric.diam M / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < 8*v)).mpr
        have hnonneg := div_nonneg hs hv.le
        nlinarith [sq_nonneg (σ/v), mul_nonneg (sub_nonneg.mpr hsv) hnonneg]
      have he := translatedOverlap_le_volume hm hb (properTimeDisplacement ω ![σ,v])
      calc
        _ ≤ ENNReal.ofReal (Metric.diam M / 4) * ENNReal.ofReal (volume.real M) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hj) (ENNReal.ofReal_le_ofReal he)
        _ = _ := (ENNReal.ofReal_mul (by positivity : 0 ≤ Metric.diam M / 4)).symm
    · rw [properTimeOverlap_zero_of_long_lt hb hδ ω _ (not_le.mp hbound)]
      exact bot_le
  · rw [properTimeOverlap, indicator_of_not_mem hd]
    exact bot_le

/-- The displayed angular/long-coordinate average is finite at every proper
 time, not only almost everywhere. The fixed positive cutoff keeps the
 coordinate transformation away from `v = 0`. -/
theorem longOverlapDensityENN_lt_top {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) :
    longOverlapDensityENN M δ σ < ⊤ := by
  have hle : longOverlapDensityENN M δ σ ≤
      ∫⁻ _ω : OverlapSphere, (∫⁻ v : ℝ, (Icc δ (2*Metric.diam M)).indicator
        (fun _ => ENNReal.ofReal (Metric.diam M / 4 * volume.real M)) v) ∂overlapSphereMeasure :=
    lintegral_mono fun ω => lintegral_mono (properTimeOverlap_le hm hb hδ ω σ)
  apply lt_of_le_of_lt hle
  rw [lintegral_indicator measurableSet_Icc, lintegral_const, lintegral_const]
  simp only [Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_Icc_lt_top))
    (measure_lt_top _ _)

/-- A derived global bound on the actual density; no continuity or Taylor
regularity is concluded. -/
theorem bounded_longOverlapDensity {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |longOverlapDensity M δ σ| ≤ C := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Metric.diam M / 4 * volume.real M) *
    volume (Icc δ (2 * Metric.diam M)) * overlapSphereMeasure univ
  have hC : C < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top)
      (measure_lt_top _ _)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun σ => ?_⟩
  have hle : longOverlapDensityENN M δ σ ≤ C := by
    calc
      _ ≤ ∫⁻ _ω : OverlapSphere, (∫⁻ v : ℝ, (Icc δ (2*Metric.diam M)).indicator
          (fun _ => ENNReal.ofReal (Metric.diam M / 4 * volume.real M)) v) ∂overlapSphereMeasure :=
        lintegral_mono fun ω => lintegral_mono (properTimeOverlap_le hm hb hδ ω σ)
      _ = C := by simp only [lintegral_indicator measurableSet_Icc, lintegral_const,
        Measure.restrict_apply_univ, C]
  rw [longOverlapDensity, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hC.ne hle

/-- Finite mass is derived from the bounded geometric overlap, not stipulated
as an admissibility assumption. -/
theorem lintegral_longOverlapDensityENN_lt_top {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ σ, longOverlapDensityENN M δ σ) < ⊤ := by
  have hi : IntegrableOn (translatedOverlap M) (longFuture δ) := by
    simpa only [one_mul] using (integrableOn_overlap_weight hm hb (fun _ => 1) continuous_const).mono_set
      (show longFuture δ ⊆ causalFuture 0 from fun _ hz => hz.1)
  have he := lintegral_longOverlap hm hδ (fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (translatedOverlap_nonneg M))]
  exact ENNReal.ofReal_lt_top

theorem ae_longOverlapDensityENN_lt_top {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ σ, longOverlapDensityENN M δ σ < ⊤ :=
  ae_lt_top (measurable_longOverlapDensityENN hm δ)
    (lintegral_longOverlapDensityENN_lt_top hm hb hδ).ne

theorem integrable_longOverlapDensity {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (longOverlapDensity M δ) :=
  integrable_toReal_of_lintegral_ne_top (measurable_longOverlapDensityENN hm δ).aemeasurable
    (lintegral_longOverlapDensityENN_lt_top hm hb hδ).ne

theorem longOverlapDensityENN_zero_of_large {M : Set Spacetime} (hb : Bornology.IsBounded M)
    {δ : ℝ} (hδ : 0 < δ) {σ : ℝ} (hσ : (2 * Metric.diam M)^2 < σ) :
    longOverlapDensityENN M δ σ = 0 := by
  have he (ω : OverlapSphere) (v : ℝ) : properTimeOverlap M δ ω ![σ,v] = 0 := by
    by_cases hp : (![σ,v] : Plane) ∈ properTimeDomain δ
    · have hv : 0 < v := hδ.trans_le hp.2.2
      have hs : σ ≤ v^2 := hp.2.1
      apply properTimeOverlap_zero_of_long_lt hb hδ
      change 2 * Metric.diam M < v
      exact (sq_lt_sq₀ (by positivity) hv.le).mp (hσ.trans_le hs)
    · exact indicator_of_not_mem hp _
  simp only [longOverlapDensityENN, he, lintegral_zero]

theorem hasCompactSupport_longOverlapDensity {M : Set Spacetime} (hb : Bornology.IsBounded M)
    {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (longOverlapDensity M δ) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc 0 ((2 * Metric.diam M)^2)))
  intro σ hσ
  by_cases hneg : σ < 0
  · simp [longOverlapDensity, longOverlapDensityENN_negative M δ hneg]
  · have hlarge : (2 * Metric.diam M)^2 < σ :=
      lt_of_not_ge (fun hle => hσ ⟨le_of_not_gt hneg, hle⟩)
    simp [longOverlapDensity, longOverlapDensityENN_zero_of_large hb hδ hlarge]

theorem longOverlapDensity_zero_of_volume_zero {M : Set Spacetime} (hM : volume M = 0)
    (δ σ : ℝ) : longOverlapDensity M δ σ = 0 := by
  simp [longOverlapDensity, longOverlapDensityENN, properTimeOverlap,
    translatedOverlap_zero_of_volume_zero hM]

/-- The independently defined geometric overlap measure, not a density-defined
replacement for the spacetime integral. -/
def longOverlapMeasure (M : Set Spacetime) (δ : ℝ) : Measure Spacetime :=
  (volume.restrict (longFuture δ)).withDensity (fun z => ENNReal.ofReal (translatedOverlap M z))

theorem map_longOverlapMeasure {M : Set Spacetime} (hm : MeasurableSet M)
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.map (intervalSq 0) (longOverlapMeasure M δ) =
      volume.withDensity (longOverlapDensityENN M δ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hq : Measurable (intervalSq (0 : Spacetime)) :=
    (continuous_intervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hg : Measurable (fun z => f (intervalSq 0 z)) := hf.comp hq
  rw [lintegral_map hf hq, longOverlapMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_translatedOverlap hm).ennreal_ofReal hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_longOverlapDensityENN hm δ) hf]
  exact lintegral_longOverlap hm hδ f hf

/-- Absolute integrability of every continuous proper-time test weight,
including the finite-density signed BDG kernel. -/
theorem integrable_longOverlapDensity_weight {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun σ => f σ * longOverlapDensity M δ σ) := by
  have hq : Continuous (intervalSq (0 : Spacetime)) :=
    continuous_intervalSq.comp (continuous_const.prodMk continuous_id)
  have hi := (integrableOn_overlap_weight hm hb (fun z => f (intervalSq 0 z))
    (hf.comp hq)).mono_set (show longFuture δ ⊆ causalFuture 0 from fun _ hz => hz.1)
  have hfinite : ∀ᵐ z ∂volume.restrict (longFuture δ), ENNReal.ofReal (translatedOverlap M z) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi' : Integrable (fun z => f (intervalSq 0 z)) (longOverlapMeasure M δ) := by
    apply (integrable_withDensity_iff (measurable_translatedOverlap hm).ennreal_ofReal hfinite).mpr
    simpa only [ENNReal.toReal_ofReal (translatedOverlap_nonneg M _)] using hi
  have hif : Integrable f (Measure.map (intervalSq 0) (longOverlapMeasure M δ)) :=
    (integrable_map_measure hf.measurable.aestronglyMeasurable hq.measurable.aemeasurable).mpr hi'
  rw [map_longOverlapMeasure hm hδ] at hif
  exact (integrable_withDensity_iff (measurable_longOverlapDensityENN hm δ)
    (ae_longOverlapDensityENN_lt_top hm hb hδ)).mp hif

/-- Signed finite-density-ready identity, with absolute integrability supplied
by the preceding theorem. No polynomial subtraction or limit is involved. -/
theorem integral_longOverlap {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in longFuture δ, f (intervalSq 0 z) * translatedOverlap M z) =
      ∫ σ : ℝ, f σ * longOverlapDensity M δ σ := by
  have hq : Measurable (intervalSq (0 : Spacetime)) :=
    (continuous_intervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have he : (∫ σ, f σ ∂Measure.map (intervalSq 0) (longOverlapMeasure M δ)) =
      ∫ z in longFuture δ, f (intervalSq 0 z) * translatedOverlap M z := by
    rw [integral_map hq.aemeasurable hf.measurable.aestronglyMeasurable, longOverlapMeasure,
      integral_withDensity_eq_integral_toReal_smul₀
        (measurable_translatedOverlap hm).ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (translatedOverlap_nonneg M _), smul_eq_mul, mul_comm]
  rw [← he, map_longOverlapMeasure hm hδ,
    integral_withDensity_eq_integral_toReal_smul₀ (measurable_longOverlapDensityENN hm δ).aemeasurable
      (ae_longOverlapDensityENN_lt_top hm hb hδ)]
  simp only [longOverlapDensity, smul_eq_mul, mul_comm]

/-- The long piece of the actual signed BDG pair term. -/
theorem integral_longOverlap_bdg {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi/24)*ρ*intervalSq 0 z^2) * translatedOverlap M z) =
      ∫ σ : ℝ, bdgKernel ((Real.pi/24)*ρ*σ^2) * longOverlapDensity M δ σ := by
  apply integral_longOverlap hm hb hδ (fun σ => bdgKernel ((Real.pi/24)*ρ*σ^2))
  unfold bdgKernel bdgPolynomial
  fun_prop

end BoundaryDraft
