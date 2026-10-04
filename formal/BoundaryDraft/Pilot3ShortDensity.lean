import BoundaryDraft.Pilot3ShortCoordinates

/-!
# The actual three-dimensional short overlap density

The upper long-coordinate cutoff is exactly that of `pilot3ShortFuture`. Nonnegative
transport precedes finite bounds and signed integration. All densities use the
original geometric `pilot3Overlap`; no alternative action or overlap jet
is introduced. The apparent Jacobian singularity at zero is controlled by the
proper-time domain itself.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal Classical
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

/-- Nonnegative overlap density in angular and short proper-time coordinates. -/
def pilot3ShortProperTimeOverlap (h g : Pilot3Space → ℝ) (δ : ℝ) (ω : Pilot3Circle)
    (p : Plane) : ℝ≥0∞ :=
  (shortProperTimeDomain δ).indicator (fun p =>
    ENNReal.ofReal (pilot3ShortNullJacobian (p 1) (p 0)) *
      ENNReal.ofReal (pilot3Overlap h g (pilot3ProperTimeDisplacement ω p))) p

/-- The extended density, defined before any finiteness conclusion. -/
def pilot3ShortOverlapDensityENN (h g : Pilot3Space → ℝ) (δ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ v : ℝ, pilot3ShortProperTimeOverlap h g δ ω ![σ,v]) ∂pilot3CircleMeasure

/-- The real density for the entire signed kernel. -/
def pilot3ShortOverlapDensity (h g : Pilot3Space → ℝ) (δ σ : ℝ) : ℝ :=
  (pilot3ShortOverlapDensityENN h g δ σ).toReal

theorem measurable_pilot3ShortProperTimeOverlap {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) :
    Measurable (fun p : Pilot3Circle × Plane => pilot3ShortProperTimeOverlap h g δ p.1 p.2) := by
  have hj : Measurable (fun p : Pilot3Circle × Plane =>
      ENNReal.ofReal (pilot3ShortNullJacobian (p.2 1) (p.2 0)) *
        ENNReal.ofReal (pilot3Overlap h g (pilot3ProperTimeDisplacement p.1 p.2))) :=
    Measurable.mul (by unfold pilot3ShortNullJacobian pilot3NullJacobian; fun_prop)
      ((H.measurable_overlap).comp measurable_pilot3ProperTimeDisplacement).ennreal_ofReal
  simpa only [pilot3ShortProperTimeOverlap, ← indicator_comp_right, Function.comp_def] using
    hj.indicator ((measurableSet_shortProperTimeDomain δ).preimage measurable_snd)

private theorem measurable_pilot3ShortPlanePair :
    Measurable (fun p : ℝ × ℝ => (![p.1,p.2] : Plane)) :=
  MeasurableEquiv.finTwoArrow.symm.measurable

private theorem measurable_pilot3ShortDensityIntegrand {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) :
    Measurable (fun p : (ℝ × Pilot3Circle) × ℝ =>
      pilot3ShortProperTimeOverlap h g δ p.1.2 ![p.1.1,p.2]) := by
  apply (measurable_pilot3ShortProperTimeOverlap H δ).comp
    (f := fun p : (ℝ × Pilot3Circle) × ℝ => (p.1.2, (![p.1.1,p.2] : Plane)))
  exact (measurable_snd.comp measurable_fst).prodMk
    (measurable_pilot3ShortPlanePair.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem measurable_pilot3ShortOverlapDensityENN {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) :
    Measurable (pilot3ShortOverlapDensityENN h g δ) :=
  (measurable_pilot3ShortDensityIntegrand H δ).lintegral_prod_right.lintegral_prod_right

theorem measurable_pilot3ShortOverlapDensity {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) :
    Measurable (pilot3ShortOverlapDensity h g δ) :=
  (measurable_pilot3ShortOverlapDensityENN H δ).ennreal_toReal

theorem pilot3ShortOverlapDensity_nonneg (h g : Pilot3Space → ℝ) (δ σ : ℝ) :
    0 ≤ pilot3ShortOverlapDensity h g δ σ := ENNReal.toReal_nonneg

private theorem lintegral_pilot3ShortPlane_fibres (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p) = ∫⁻ σ : ℝ, ∫⁻ v : ℝ, f ![σ,v] := by
  have he := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  rw [← he.lintegral_comp hf, Measure.volume_eq_prod]
  exact lintegral_prod _ (hf.comp he.measurable).aemeasurable

/-- Nonnegative disintegration of the original short geometric overlap. -/
theorem lintegral_pilot3ShortOverlap {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g)
    (δ : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in pilot3ShortFuture δ, ENNReal.ofReal (pilot3Overlap h g z) * f (dimensionIntervalSq 0 z)) =
      ∫⁻ σ : ℝ, pilot3ShortOverlapDensityENN h g δ σ * f σ := by
  have hq : Measurable (dimensionIntervalSq (0 : Pilot3Spacetime)) :=
    (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hF : Measurable (fun z => ENNReal.ofReal (pilot3Overlap h g z) * f (dimensionIntervalSq 0 z)) :=
    (H.measurable_overlap).ennreal_ofReal.mul (hf.comp hq)
  rw [lintegral_pilot3ShortFuture_properTime δ _ hF]
  have he (ω : Pilot3Circle) :
      (∫⁻ p in shortProperTimeDomain δ,
        ENNReal.ofReal (pilot3ShortNullJacobian (p 1) (p 0)) *
          (ENNReal.ofReal (pilot3Overlap h g (pilot3ProperTimeDisplacement ω p)) *
            f (dimensionIntervalSq 0 (pilot3ProperTimeDisplacement ω p)))) =
        ∫⁻ p : Plane, pilot3ShortProperTimeOverlap h g δ ω p * f (p 0) := by
    rw [← lintegral_indicator (measurableSet_shortProperTimeDomain δ)]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ shortProperTimeDomain δ
    · simp [pilot3ShortProperTimeOverlap, hp,
        pilot3_intervalSq_properTimeDisplacement ω p hp.2.2.1.ne', mul_assoc]
    · simp [pilot3ShortProperTimeOverlap, hp]
  change (∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
    ENNReal.ofReal (pilot3ShortNullJacobian (p 1) (p 0)) *
      (ENNReal.ofReal (pilot3Overlap h g (pilot3ProperTimeDisplacement ω p)) *
        f (dimensionIntervalSq 0 (pilot3ProperTimeDisplacement ω p)))) ∂pilot3CircleMeasure) = _
  simp_rw [he]
  have hi := measurable_pilot3ShortDensityIntegrand H δ
  have hw (ω : Pilot3Circle) : Measurable (pilot3ShortProperTimeOverlap h g δ ω) :=
    (measurable_pilot3ShortProperTimeOverlap H δ).comp
      (f := fun p : Plane => (ω,p)) (measurable_const.prodMk measurable_id)
  have hplane (ω : Pilot3Circle) := lintegral_pilot3ShortPlane_fibres
    (fun p => pilot3ShortProperTimeOverlap h g δ ω p * f (p 0))
    ((hw ω).mul (hf.comp (measurable_pi_apply 0)))
  simp_rw [hplane]
  change (∫⁻ ω, (∫⁻ σ : ℝ, ∫⁻ v : ℝ, pilot3ShortProperTimeOverlap h g δ ω ![σ,v] * f σ)
    ∂pilot3CircleMeasure) = _
  have him : Measurable (fun p : (ℝ × Pilot3Circle) × ℝ =>
      pilot3ShortProperTimeOverlap h g δ p.1.2 ![p.1.1,p.2] * f p.1.1) :=
    hi.mul (hf.comp (measurable_fst.comp measurable_fst))
  rw [← lintegral_lintegral_swap him.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro σ
  have hv (ω : Pilot3Circle) : Measurable (fun v : ℝ => pilot3ShortProperTimeOverlap h g δ ω ![σ,v]) :=
    (hw ω).comp (measurable_pilot3ShortPlanePair.comp (measurable_const.prodMk measurable_id))
  simp_rw [lintegral_mul_const (f σ) (hv _)]
  have hinner : Measurable (fun p : ℝ × Pilot3Circle =>
      ∫⁻ v : ℝ, pilot3ShortProperTimeOverlap h g δ p.2 ![p.1,v]) := hi.lintegral_prod_right
  exact lintegral_mul_const _
    (hinner.comp (f := fun ω : Pilot3Circle => (σ,ω)) (measurable_const.prodMk measurable_id))

/-- Pointwise finite domination on the fixed finite long-coordinate interval. -/
theorem pilot3ShortProperTimeOverlap_le {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) (ω : Pilot3Circle) (σ v : ℝ) :
    pilot3ShortProperTimeOverlap h g δ ω ![σ,v] ≤ (Ioo 0 δ).indicator
      (fun _ => ENNReal.ofReal ((1 / 4 : ℝ) * volume.real (pilot3Region h g))) v := by
  by_cases hd : (![σ,v] : Plane) ∈ shortProperTimeDomain δ
  · have hv : v ∈ Ioo 0 δ := hd.2.2
    rw [indicator_of_mem hv, pilot3ShortProperTimeOverlap, indicator_of_mem hd]
    have hj := (pilot3ShortNullJacobian_bounds hv.1 ⟨hd.1, hd.2.1⟩).2
    have he := H.overlap_le_volume (pilot3ProperTimeDisplacement ω ![σ,v])
    calc
      _ ≤ ENNReal.ofReal ((1 / 4 : ℝ)) * ENNReal.ofReal (volume.real (pilot3Region h g)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hj) (ENNReal.ofReal_le_ofReal he)
      _ = _ := (ENNReal.ofReal_mul (by linarith [hv.1, hv.2] : 0 ≤ (1 / 4 : ℝ))).symm
  · rw [pilot3ShortProperTimeOverlap, indicator_of_not_mem hd]
    exact bot_le

/-- An explicit uniform bound, without a lower positive long cutoff. -/
theorem pilot3ShortOverlapDensityENN_le {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ σ : ℝ) :
    pilot3ShortOverlapDensityENN h g δ σ ≤ ENNReal.ofReal ((1 / 4 : ℝ) * volume.real (pilot3Region h g)) *
      volume (Ioo 0 δ) * pilot3CircleMeasure univ := by
  calc
    _ ≤ ∫⁻ _ω : Pilot3Circle, (∫⁻ v : ℝ, (Ioo 0 δ).indicator
        (fun _ => ENNReal.ofReal ((1 / 4 : ℝ) * volume.real (pilot3Region h g))) v) ∂pilot3CircleMeasure :=
      lintegral_mono fun ω => lintegral_mono (pilot3ShortProperTimeOverlap_le H δ ω σ)
    _ = _ := by simp only [lintegral_indicator measurableSet_Ioo, lintegral_const,
      Measure.restrict_apply_univ]

theorem pilot3ShortOverlapDensityENN_lt_top {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ σ : ℝ) : pilot3ShortOverlapDensityENN h g δ σ < ⊤ :=
  (pilot3ShortOverlapDensityENN_le H δ σ).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top)
      (measure_lt_top _ _))

theorem bounded_pilot3ShortOverlapDensity {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |pilot3ShortOverlapDensity h g δ σ| ≤ C := by
  let C : ℝ≥0∞ := ENNReal.ofReal ((1 / 4 : ℝ) * volume.real (pilot3Region h g)) *
    volume (Ioo 0 δ) * pilot3CircleMeasure univ
  have hC : C < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioo_lt_top)
      (measure_lt_top _ _)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun σ => ?_⟩
  rw [pilot3ShortOverlapDensity, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hC.ne (pilot3ShortOverlapDensityENN_le H δ σ)

theorem pilot3ShortOverlapDensityENN_negative (h g : Pilot3Space → ℝ) (δ : ℝ) {σ : ℝ} (hσ : σ < 0) :
    pilot3ShortOverlapDensityENN h g δ σ = 0 := by
  have he (ω : Pilot3Circle) (v : ℝ) : pilot3ShortProperTimeOverlap h g δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    exact (not_le_of_gt hσ) hp.1
  simp [pilot3ShortOverlapDensityENN, he]

/-- The density even vanishes at the upper endpoint, since the cutoff is strict. -/
theorem pilot3ShortOverlapDensityENN_zero_of_le (h g : Pilot3Space → ℝ) (δ : ℝ)
    {σ : ℝ} (hσ : δ ^ 2 ≤ σ) : pilot3ShortOverlapDensityENN h g δ σ = 0 := by
  have he (ω : Pilot3Circle) (v : ℝ) : pilot3ShortProperTimeOverlap h g δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    have hv : 0 < v := hp.2.2.1
    have hvδ : v < δ := hp.2.2.2
    have hsq : σ ≤ v ^ 2 := hp.2.1
    have := (sq_lt_sq₀ hv.le (hv.trans hvδ).le).mpr hvδ
    linarith
  simp only [pilot3ShortOverlapDensityENN, he, lintegral_zero]

theorem support_pilot3ShortOverlapDensity_subset (h g : Pilot3Space → ℝ) (δ : ℝ) :
    Function.support (pilot3ShortOverlapDensity h g δ) ⊆ Icc 0 (δ ^ 2) := by
  intro σ hσ
  by_contra hn
  by_cases hneg : σ < 0
  · exact hσ (by simp [pilot3ShortOverlapDensity, pilot3ShortOverlapDensityENN_negative h g δ hneg])
  · have hlarge : δ ^ 2 < σ := lt_of_not_ge (fun hle => hn ⟨le_of_not_gt hneg, hle⟩)
    exact hσ (by simp [pilot3ShortOverlapDensity, pilot3ShortOverlapDensityENN_zero_of_le h g δ hlarge.le])

theorem hasCompactSupport_pilot3ShortOverlapDensity (h g : Pilot3Space → ℝ) (δ : ℝ) :
    HasCompactSupport (pilot3ShortOverlapDensity h g δ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    by_contra hs
    exact hx (support_pilot3ShortOverlapDensity_subset h g δ hs)

/-- The literal nonnegative average on nonnegative proper-time square. The
sharp upper cutoff is retained, including its omission at equality. -/
theorem pilot3ShortOverlapDensityENN_eq_average (h g : Pilot3Space → ℝ) (δ : ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    pilot3ShortOverlapDensityENN h g δ σ = ∫⁻ ω, (∫⁻ v in Ioo 0 δ,
      if σ ≤ v ^ 2 then ENNReal.ofReal (pilot3ShortNullJacobian v σ) *
        ENNReal.ofReal (pilot3Overlap h g (pilot3ProperTimeDisplacement ω ![σ,v])) else 0)
      ∂pilot3CircleMeasure := by
  apply lintegral_congr
  intro ω
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro v
  have hd : (![σ,v] : Plane) ∈ shortProperTimeDomain δ ↔ σ ≤ v ^ 2 ∧ v ∈ Ioo 0 δ := by
    simp only [shortProperTimeDomain, mem_setOf_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hσ, true_and, mem_Ioo]
  by_cases hv : v ∈ Ioo 0 δ <;> by_cases hs : σ ≤ v ^ 2 <;>
    simp [pilot3ShortProperTimeOverlap, hd, hv, hs]

/-- The real fibre. Its integration is only over `0 < v < δ`; the proper-time
condition then controls the apparent `1 / v` singularity. -/
def pilot3ShortOverlapFibre (h g : Pilot3Space → ℝ) (σ : ℝ) (ω : Pilot3Circle) (v : ℝ) : ℝ :=
  if σ ≤ v ^ 2 then pilot3ShortNullJacobian v σ *
    pilot3Overlap h g (pilot3ProperTimeDisplacement ω ![σ,v]) else 0

theorem measurable_pilot3ShortOverlapFibre {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (σ : ℝ) :
    Measurable (fun p : Pilot3Circle × ℝ => pilot3ShortOverlapFibre h g σ p.1 p.2) := by
  have hp : Measurable (fun p : Pilot3Circle × ℝ => pilot3ProperTimeDisplacement p.1 ![σ,p.2]) :=
    measurable_pilot3ProperTimeDisplacement.comp (measurable_fst.prodMk
      (measurable_pilot3ShortPlanePair.comp (measurable_const.prodMk measurable_snd)))
  exact Measurable.ite
    (isClosed_le continuous_const (continuous_snd.pow 2)).measurableSet
    ((by unfold pilot3ShortNullJacobian pilot3NullJacobian; fun_prop : Measurable (fun p : Pilot3Circle × ℝ => pilot3ShortNullJacobian p.2 σ)).mul
      ((H.measurable_overlap).comp hp)) measurable_const

/-- Signed integration will use this pointwise real dominator, not a formal
exchange of totalized integrals. -/
theorem pilot3ShortOverlapFibre_bounds {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (ω : Pilot3Circle) (v : ℝ) (hv : v ∈ Ioo 0 δ) :
    0 ≤ pilot3ShortOverlapFibre h g σ ω v ∧
      pilot3ShortOverlapFibre h g σ ω v ≤ (1 / 4 : ℝ) * volume.real (pilot3Region h g) := by
  have hδ : 0 ≤ (1 / 4 : ℝ) := by linarith [hv.1, hv.2]
  by_cases hs : σ ≤ v ^ 2
  · rw [pilot3ShortOverlapFibre, if_pos hs]
    have hj := pilot3ShortNullJacobian_bounds hv.1 ⟨hσ, hs⟩
    exact ⟨mul_nonneg hj.1 (SmoothPilot3.overlap_nonneg (h := h) (f := g) _),
      mul_le_mul hj.2 (H.overlap_le_volume _)
        (SmoothPilot3.overlap_nonneg (h := h) (f := g) _) hδ⟩
  · rw [pilot3ShortOverlapFibre, if_neg hs]
    exact ⟨le_rfl, mul_nonneg hδ ENNReal.toReal_nonneg⟩

/-- Every fibre, not merely almost every direction, is absolutely integrable. -/
theorem integrableOn_pilot3ShortOverlapFibre {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (ω : Pilot3Circle) :
    IntegrableOn (pilot3ShortOverlapFibre h g σ ω) (Ioo 0 δ) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  apply (integrable_const ((1 / 4 : ℝ) * volume.real (pilot3Region h g))).mono'
    (((measurable_pilot3ShortOverlapFibre H σ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hbnd := pilot3ShortOverlapFibre_bounds H δ hσ ω v hv
  change ‖pilot3ShortOverlapFibre h g σ ω v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg hbnd.1]
  exact hbnd.2

/-- Joint absolute integrability before the real angular/long-coordinate
Fubini interchange. This includes measurability for the actual overlap. -/
theorem integrable_pilot3ShortOverlapFibre {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (fun p : Pilot3Circle × ℝ => pilot3ShortOverlapFibre h g σ p.1 p.2)
      (pilot3CircleMeasure.prod (volume.restrict (Ioo 0 δ))) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hv : ∀ᵐ p : Pilot3Circle × ℝ
      ∂pilot3CircleMeasure.prod (volume.restrict (Ioo 0 δ)), p.2 ∈ Ioo 0 δ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)
  apply (integrable_const ((1 / 4 : ℝ) * volume.real (pilot3Region h g))).mono'
    (measurable_pilot3ShortOverlapFibre H σ).aestronglyMeasurable
  filter_upwards [hv] with p hp
  have hbnd := pilot3ShortOverlapFibre_bounds H δ hσ p.1 p.2 hp
  rw [Real.norm_eq_abs, abs_of_nonneg hbnd.1]
  exact hbnd.2

/-- The real fibre formula, after establishing both pointwise finiteness of
the ENNReal density and joint absolute integrability of the displayed fibre. -/
theorem pilot3ShortOverlapDensity_eq_average {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    pilot3ShortOverlapDensity h g δ σ = ∫ ω, (∫ v in Ioo 0 δ,
      if σ ≤ v ^ 2 then pilot3ShortNullJacobian v σ *
        pilot3Overlap h g (pilot3ProperTimeDisplacement ω ![σ,v]) else 0) ∂pilot3CircleMeasure := by
  let μ := pilot3CircleMeasure.prod (volume.restrict (Ioo 0 δ))
  have hi := integrable_pilot3ShortOverlapFibre H δ hσ
  have hn : ∀ᵐ p : Pilot3Circle × ℝ ∂μ, 0 ≤ pilot3ShortOverlapFibre h g σ p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const (measurable_pilot3ShortOverlapFibre H σ))).mpr
    exact Filter.Eventually.of_forall fun ω => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact (pilot3ShortOverlapFibre_bounds H δ hσ ω v hv).1
  have he : pilot3ShortOverlapDensityENN h g δ σ =
      ∫⁻ p : Pilot3Circle × ℝ, ENNReal.ofReal (pilot3ShortOverlapFibre h g σ p.1 p.2) ∂μ := by
    rw [pilot3ShortOverlapDensityENN_eq_average h g δ hσ,
      lintegral_prod _ (measurable_pilot3ShortOverlapFibre H σ).ennreal_ofReal.aemeasurable]
    apply lintegral_congr
    intro ω
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    by_cases hs : σ ≤ v ^ 2
    · simp only [hs, if_true, pilot3ShortOverlapFibre]
      exact (ENNReal.ofReal_mul (pilot3ShortNullJacobian_bounds hv.1 ⟨hσ, hs⟩).1).symm
    · simp only [hs, if_false, pilot3ShortOverlapFibre, ENNReal.ofReal_zero]
  change (pilot3ShortOverlapDensityENN h g δ σ).toReal = _
  rw [he, ← integral_eq_lintegral_of_nonneg_ae hn
    (measurable_pilot3ShortOverlapFibre H σ).aestronglyMeasurable]
  exact integral_prod _ hi

/-- Finite mass is inherited from the actual bounded geometric overlap. -/
theorem lintegral_pilot3ShortOverlapDensityENN_lt_top {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) : (∫⁻ σ, pilot3ShortOverlapDensityENN h g δ σ) < ⊤ := by
  have hi : IntegrableOn (pilot3Overlap h g) (pilot3ShortFuture δ) := by
    simpa only [one_mul] using (H.integrableOn_overlap_weight (fun _ => 1) continuous_const).mono_set diff_subset
  have he := lintegral_pilot3ShortOverlap H δ (fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (SmoothPilot3.overlap_nonneg (h := h) (f := g)))]
  exact ENNReal.ofReal_lt_top

theorem integrable_pilot3ShortOverlapDensity {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) : Integrable (pilot3ShortOverlapDensity h g δ) :=
  integrable_toReal_of_lintegral_ne_top (measurable_pilot3ShortOverlapDensityENN H δ).aemeasurable
    (lintegral_pilot3ShortOverlapDensityENN_lt_top H δ).ne

/-- Geometric short overlap measure on the original spacetime, independent of
its proper-time density. -/
def pilot3ShortOverlapMeasure (h g : Pilot3Space → ℝ) (δ : ℝ) : Measure Pilot3Spacetime :=
  (volume.restrict (pilot3ShortFuture δ)).withDensity (fun z => ENNReal.ofReal (pilot3Overlap h g z))

theorem map_pilot3ShortOverlapMeasure {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) :
    Measure.map (dimensionIntervalSq 0) (pilot3ShortOverlapMeasure h g δ) =
      volume.withDensity (pilot3ShortOverlapDensityENN h g δ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hq : Measurable (dimensionIntervalSq (0 : Pilot3Spacetime)) :=
    (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hg : Measurable (fun z => f (dimensionIntervalSq 0 z)) := hf.comp hq
  rw [lintegral_map hf hq, pilot3ShortOverlapMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (H.measurable_overlap).ennreal_ofReal hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_pilot3ShortOverlapDensityENN H δ) hf]
  exact lintegral_pilot3ShortOverlap H δ f hf

/-- Absolute integrability is proved before inserting a signed continuous kernel. -/
theorem integrable_pilot3ShortOverlapDensity_weight {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun σ => f σ * pilot3ShortOverlapDensity h g δ σ) := by
  have hq : Continuous (dimensionIntervalSq (0 : Pilot3Spacetime)) :=
    continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)
  have hi := (H.integrableOn_overlap_weight (fun z => f (dimensionIntervalSq 0 z)) (hf.comp hq)).mono_set
    (show pilot3ShortFuture δ ⊆ dimensionCausalFuture 0 from diff_subset)
  have hfinite : ∀ᵐ z ∂volume.restrict (pilot3ShortFuture δ), ENNReal.ofReal (pilot3Overlap h g z) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi' : Integrable (fun z => f (dimensionIntervalSq 0 z)) (pilot3ShortOverlapMeasure h g δ) := by
    apply (integrable_withDensity_iff (H.measurable_overlap).ennreal_ofReal hfinite).mpr
    simpa only [ENNReal.toReal_ofReal (SmoothPilot3.overlap_nonneg (h := h) (f := g) _)] using hi
  have hif : Integrable f (Measure.map (dimensionIntervalSq 0) (pilot3ShortOverlapMeasure h g δ)) :=
    (integrable_map_measure hf.measurable.aestronglyMeasurable hq.measurable.aemeasurable).mpr hi'
  rw [map_pilot3ShortOverlapMeasure H δ] at hif
  exact (integrable_withDensity_iff (measurable_pilot3ShortOverlapDensityENN H δ)
    (Filter.Eventually.of_forall (pilot3ShortOverlapDensityENN_lt_top H δ))).mp hif

/-- Exact signed finite-density identity for the actual original region. -/
theorem integral_pilot3ShortOverlap {h g : Pilot3Space → ℝ} (H : SmoothPilot3 h g) (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in pilot3ShortFuture δ, f (dimensionIntervalSq 0 z) * pilot3Overlap h g z) =
      ∫ σ : ℝ, f σ * pilot3ShortOverlapDensity h g δ σ := by
  have hq : Measurable (dimensionIntervalSq (0 : Pilot3Spacetime)) :=
    (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have he : (∫ σ, f σ ∂Measure.map (dimensionIntervalSq 0) (pilot3ShortOverlapMeasure h g δ)) =
      ∫ z in pilot3ShortFuture δ, f (dimensionIntervalSq 0 z) * pilot3Overlap h g z := by
    rw [integral_map hq.aemeasurable hf.measurable.aestronglyMeasurable, pilot3ShortOverlapMeasure,
      integral_withDensity_eq_integral_toReal_smul₀
        (H.measurable_overlap).ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (SmoothPilot3.overlap_nonneg (h := h) (f := g) _), smul_eq_mul, mul_comm]
  rw [← he, map_pilot3ShortOverlapMeasure H δ,
    integral_withDensity_eq_integral_toReal_smul₀ (measurable_pilot3ShortOverlapDensityENN H δ).aemeasurable
      (Filter.Eventually.of_forall (pilot3ShortOverlapDensityENN_lt_top H δ))]
  simp only [pilot3ShortOverlapDensity, smul_eq_mul, mul_comm]

/-- Only a proved null singleton separates the closed and open half-lines. -/
theorem integral_pilot3ShortOverlapDensity_eq_Ioi (h g : Pilot3Space → ℝ) (δ : ℝ) (w : ℝ → ℝ) :
    (∫ σ : ℝ, w σ * pilot3ShortOverlapDensity h g δ σ) =
      ∫ σ : ℝ in Ioi 0, w σ * pilot3ShortOverlapDensity h g δ σ := by
  rw [← integral_Ici_eq_integral_Ioi]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro σ hσ
  have hneg : σ < 0 := lt_of_not_ge hσ
  simp [pilot3ShortOverlapDensity, pilot3ShortOverlapDensityENN_negative h g δ hneg]

/-- Fully normalized density formula for the actual short observable. -/
theorem SmoothPilot3.shortAction_eq_density {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
    (ρ δ : ℝ) : pilot3ShortAction ρ δ h f =
      ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
        dimensionPairCoefficient 3 * ρ * ∫ σ : ℝ in Ioi 0,
          dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
            pilot3ShortOverlapDensity h f δ σ) := by
  have hc : Continuous (fun σ : ℝ => dimensionKernel 3
      (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) :=
    (continuous_dimensionKernel 3).comp
      (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num))))
  have he := integral_pilot3ShortOverlap hf δ _ hc
  change (∫ z in pilot3ShortFuture δ, pilot3DisplacementKernel ρ z * pilot3Overlap h f z) = _ at he
  rw [pilot3ShortAction, he, integral_pilot3ShortOverlapDensity_eq_Ioi]

end BoundaryDraft
