import BoundaryDraft.Pilot3LongCoordinates

/-!
# The actual 3D long overlap density

Nonnegative transport is proved before signed Fubini. The definition uses the
canonical causal overlap, not a supplied jet. Finiteness is pointwise, including
sigma zero. Constants may depend on the fixed positive cutoff.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
noncomputable section
namespace BoundaryDraft

set_option maxHeartbeats 1000000

/-- Nonnegative geometric integrand on the exact sharp long domain. -/
def pilot3ProperTimeOverlap (h f : Pilot3Space → ℝ) (δ : ℝ) (ω : Pilot3Circle) (p : Plane) : ℝ≥0∞ :=
  (properTimeDomain δ).indicator (fun p => ENNReal.ofReal (pilot3NullJacobian (p 0) (p 1)) *
    ENNReal.ofReal (pilot3Overlap h f (pilot3RayDisplacement ω.val (p 0) (p 1)))) p

def pilot3LongDensityENN (h f : Pilot3Space → ℝ) (δ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ v : ℝ, pilot3ProperTimeOverlap h f δ ω ![σ,v]) ∂pilot3CircleMeasure

/-- Real representative used with the entire signed dimension-three kernel. -/
def pilot3LongDensity (h f : Pilot3Space → ℝ) (δ σ : ℝ) : ℝ :=
  (pilot3LongDensityENN h f δ σ).toReal

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem measurable_properTimeOverlap (δ : ℝ) :
    Measurable (fun p : Pilot3Circle × Plane => pilot3ProperTimeOverlap h f δ p.1 p.2) := by
  have hj : Measurable (fun p : Pilot3Circle × Plane =>
      ENNReal.ofReal (pilot3NullJacobian (p.2 0) (p.2 1)) *
        ENNReal.ofReal (pilot3Overlap h f (pilot3RayDisplacement p.1.val (p.2 0) (p.2 1)))) := by
    apply Measurable.mul
    · unfold pilot3NullJacobian
      fun_prop
    · exact (hf.measurable_overlap.comp measurable_pilot3RayDisplacement).ennreal_ofReal
  simpa only [pilot3ProperTimeOverlap, ← indicator_comp_right, Function.comp_def] using
    hj.indicator ((measurableSet_properTimeDomain δ).preimage measurable_snd)

private theorem measurable_densityIntegrand (δ : ℝ) :
    Measurable (fun p : (ℝ × Pilot3Circle) × ℝ => pilot3ProperTimeOverlap h f δ p.1.2 ![p.1.1,p.2]) := by
  apply (hf.measurable_properTimeOverlap δ).comp
    (f := fun p : (ℝ × Pilot3Circle) × ℝ => (p.1.2, (![p.1.1,p.2] : Plane)))
  exact (measurable_snd.comp measurable_fst).prodMk (MeasurableEquiv.finTwoArrow.symm.measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem measurable_longDensityENN (δ : ℝ) : Measurable (pilot3LongDensityENN h f δ) :=
  (hf.measurable_densityIntegrand δ).lintegral_prod_right.lintegral_prod_right

theorem measurable_longDensity (δ : ℝ) : Measurable (pilot3LongDensity h f δ) :=
  (hf.measurable_longDensityENN δ).ennreal_toReal

omit hf in
theorem longDensityENN_negative (δ : ℝ) {σ : ℝ} (hσ : σ < 0) :
    pilot3LongDensityENN h f δ σ = 0 := by
  have he (ω : Pilot3Circle) (v : ℝ) : pilot3ProperTimeOverlap h f δ ω ![σ,v] = 0 :=
    indicator_of_not_mem (fun hp => (not_le_of_gt hσ) hp.1) _
  simp [pilot3LongDensityENN, he]

/-- Nonnegative measure transport, prior to any finiteness or cancellation. -/
theorem lintegral_longOverlap {δ : ℝ} (hδ : 0 < δ) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in pilot3LongFuture δ, ENNReal.ofReal (pilot3Overlap h f z) * w (dimensionIntervalSq 0 z)) =
      ∫⁻ σ : ℝ, pilot3LongDensityENN h f δ σ * w σ := by
  have hq : Measurable (dimensionIntervalSq (0 : Pilot3Spacetime)) := by
    unfold dimensionIntervalSq
    fun_prop
  have hF : Measurable (fun z => ENNReal.ofReal (pilot3Overlap h f z) * w (dimensionIntervalSq 0 z)) :=
    hf.measurable_overlap.ennreal_ofReal.mul (hw.comp hq)
  rw [lintegral_pilot3LongFuture_properTime hδ _ hF]
  have he (ω : Pilot3Circle) :
      (∫⁻ p in properTimeDomain δ, ENNReal.ofReal (pilot3NullJacobian (p 0) (p 1)) *
        (ENNReal.ofReal (pilot3Overlap h f (pilot3RayDisplacement ω.val (p 0) (p 1))) *
          w (dimensionIntervalSq 0 (pilot3RayDisplacement ω.val (p 0) (p 1))))) =
        ∫⁻ p : Plane, pilot3ProperTimeOverlap h f δ ω p * w (p 0) := by
    rw [← lintegral_indicator (measurableSet_properTimeDomain δ)]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ properTimeDomain δ
    · have hs : dimensionIntervalSq 0 (pilot3RayDisplacement ω.val (p 0) (p 1)) = p 0 := by
        simpa only [dimensionIntervalSq, Prod.fst_zero, Prod.snd_zero, sub_zero] using
          (pilot3RayDisplacement_parameters (mem_sphere_zero_iff_norm.mp ω.property)
            (hδ.trans_le hp.2.2) ⟨hp.1, hp.2.1⟩).2
      simp [pilot3ProperTimeOverlap, hp, hs, mul_assoc]
    · simp [pilot3ProperTimeOverlap, hp]
  simp_rw [he]
  have hi := hf.measurable_densityIntegrand δ
  have hm (ω : Pilot3Circle) : Measurable (pilot3ProperTimeOverlap h f δ ω) :=
    (hf.measurable_properTimeOverlap δ).comp
      (f := fun p : Plane => (ω, p)) (measurable_const.prodMk measurable_id)
  have hplane (ω : Pilot3Circle) :
      (∫⁻ p : Plane, pilot3ProperTimeOverlap h f δ ω p * w (p 0)) =
        ∫⁻ σ : ℝ, ∫⁻ v : ℝ, pilot3ProperTimeOverlap h f δ ω ![σ,v] * w σ := by
    have e := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
    have hw' : Measurable (fun p : Plane => pilot3ProperTimeOverlap h f δ ω p * w (p 0)) :=
      (hm ω).mul (hw.comp (measurable_pi_apply 0))
    rw [← e.lintegral_comp hw', Measure.volume_eq_prod]
    exact lintegral_prod _ (hw'.comp e.measurable).aemeasurable
  simp_rw [hplane]
  have him : Measurable (fun p : (ℝ × Pilot3Circle) × ℝ =>
      pilot3ProperTimeOverlap h f δ p.1.2 ![p.1.1,p.2] * w p.1.1) :=
    hi.mul (hw.comp (measurable_fst.comp measurable_fst))
  rw [← lintegral_lintegral_swap him.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro σ
  have hv (ω : Pilot3Circle) : Measurable (fun v : ℝ => pilot3ProperTimeOverlap h f δ ω ![σ,v]) :=
    (hm ω).comp (MeasurableEquiv.finTwoArrow.symm.measurable.comp (measurable_const.prodMk measurable_id))
  simp_rw [lintegral_mul_const (w σ) (hv _)]
  have hinner : Measurable (fun p : ℝ × Pilot3Circle =>
      ∫⁻ v : ℝ, pilot3ProperTimeOverlap h f δ p.2 ![p.1,v]) := hi.lintegral_prod_right
  exact lintegral_mul_const _ (hinner.comp
    (f := fun ω : Pilot3Circle => (σ, ω)) (measurable_const.prodMk measurable_id))

omit hf in
theorem longDensityENN_eq_average {δ : ℝ} (hδ : 0 < δ) {σ : ℝ} (hσ : 0 ≤ σ) :
    pilot3LongDensityENN h f δ σ = ∫⁻ ω, (∫⁻ v in Ici (max δ (Real.sqrt σ)),
      ENNReal.ofReal (pilot3NullJacobian σ v) *
        ENNReal.ofReal (pilot3Overlap h f (pilot3RayDisplacement ω.val σ v))) ∂pilot3CircleMeasure := by
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
  by_cases hv : v ∈ Ici (max δ (Real.sqrt σ)) <;> simp [pilot3ProperTimeOverlap, hm, hv]

theorem properTimeOverlap_zero_of_long_lt {δ : ℝ} (hδ : 0 < δ) (ω : Pilot3Circle) (p : Plane)
    (hp : 2 * Metric.diam (pilot3Region h f) < p 1) : pilot3ProperTimeOverlap h f δ ω p = 0 := by
  by_cases hd : p ∈ properTimeDomain δ
  · have hv := hδ.trans_le hd.2.2
    have hq : 0 ≤ p 0 / p 1 := div_nonneg hd.1 hv.le
    have hn := norm_fst_le (pilot3RayDisplacement ω.val (p 0) (p 1))
    have hnorm : Metric.diam (pilot3Region h f) < ‖pilot3RayDisplacement ω.val (p 0) (p 1)‖ := by
      have hab := le_abs_self ((p 1 + p 0 / p 1) / 2)
      simp only [pilot3RayDisplacement, Real.norm_eq_abs] at hn
      change Metric.diam (pilot3Region h f) < ‖((p 1 + p 0 / p 1) / 2, ((p 1 - p 0 / p 1) / 2) • ω.val)‖
      linarith
    simp [pilot3ProperTimeOverlap, hd, hf.overlap_eq_zero_of_diam_lt hnorm]
  · exact indicator_of_not_mem hd _

theorem properTimeOverlap_le {δ : ℝ} (hδ : 0 < δ) (ω : Pilot3Circle) (σ v : ℝ) :
    pilot3ProperTimeOverlap h f δ ω ![σ,v] ≤
      (Icc δ (2 * Metric.diam (pilot3Region h f))).indicator
        (fun _ => ENNReal.ofReal (volume.real (pilot3Region h f) / 4)) v := by
  by_cases hd : (![σ,v] : Plane) ∈ properTimeDomain δ
  · have hvδ : δ ≤ v := hd.2.2
    have hv : 0 < v := hδ.trans_le hvδ
    by_cases hb : v ≤ 2 * Metric.diam (pilot3Region h f)
    · rw [indicator_of_mem (show v ∈ Icc δ (2 * Metric.diam (pilot3Region h f)) from ⟨hvδ, hb⟩),
        pilot3ProperTimeOverlap, indicator_of_mem hd]
      have hj := (pilot3NullJacobian_bounds hv ⟨hd.1, hd.2.1⟩).2
      calc
        _ ≤ ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (volume.real (pilot3Region h f)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hj) (ENNReal.ofReal_le_ofReal (hf.overlap_le_volume _))
        _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]; congr 1; ring
    · rw [hf.properTimeOverlap_zero_of_long_lt hδ ω _ (not_le.mp hb)]
      exact bot_le
  · rw [pilot3ProperTimeOverlap, indicator_of_not_mem hd]
    exact bot_le

theorem longDensityENN_lt_top {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) : pilot3LongDensityENN h f δ σ < ⊤ := by
  have hle := lintegral_mono (μ := pilot3CircleMeasure)
    (fun ω : Pilot3Circle => lintegral_mono (μ := volume) (hf.properTimeOverlap_le hδ ω σ))
  apply lt_of_le_of_lt hle
  rw [lintegral_indicator measurableSet_Icc, lintegral_const, lintegral_const]
  simp only [Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top) (measure_lt_top _ _)

theorem bounded_longDensity {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |pilot3LongDensity h f δ σ| ≤ C := by
  let C : ℝ≥0∞ := ENNReal.ofReal (volume.real (pilot3Region h f) / 4) *
    volume (Icc δ (2 * Metric.diam (pilot3Region h f))) * pilot3CircleMeasure univ
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top) (measure_lt_top _ _)
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun σ => ?_⟩
  have hle : pilot3LongDensityENN h f δ σ ≤ C := by
    calc
      _ ≤ ∫⁻ _ω : Pilot3Circle, (∫⁻ v : ℝ, (Icc δ (2 * Metric.diam (pilot3Region h f))).indicator
          (fun _ => ENNReal.ofReal (volume.real (pilot3Region h f) / 4)) v) ∂pilot3CircleMeasure :=
        lintegral_mono fun ω => lintegral_mono (hf.properTimeOverlap_le hδ ω σ)
      _ = C := by simp only [lintegral_indicator measurableSet_Icc, lintegral_const, Measure.restrict_apply_univ, C]
  rw [pilot3LongDensity, abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hC.ne hle

theorem hasCompactSupport_longDensity {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (pilot3LongDensity h f δ) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc 0 ((2 * Metric.diam (pilot3Region h f)) ^ 2)))
  intro σ hσ
  by_cases hneg : σ < 0
  · simp [pilot3LongDensity, longDensityENN_negative δ hneg]
  · have hlarge : (2 * Metric.diam (pilot3Region h f)) ^ 2 < σ :=
      lt_of_not_ge (fun hle => hσ ⟨le_of_not_gt hneg, hle⟩)
    have he (ω : Pilot3Circle) (v : ℝ) : pilot3ProperTimeOverlap h f δ ω ![σ,v] = 0 := by
      by_cases hp : (![σ,v] : Plane) ∈ properTimeDomain δ
      · exact hf.properTimeOverlap_zero_of_long_lt hδ ω _
          ((sq_lt_sq₀ (by positivity) (hδ.le.trans hp.2.2)).mp (hlarge.trans_le hp.2.1))
      · exact indicator_of_not_mem hp _
    simp only [pilot3LongDensity, pilot3LongDensityENN, he, lintegral_zero, ENNReal.toReal_zero]

theorem lintegral_longDensityENN_lt_top {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ σ, pilot3LongDensityENN h f δ σ) < ⊤ := by
  have hi : IntegrableOn (pilot3Overlap h f) (pilot3LongFuture δ) := by
    simpa only [one_mul] using (hf.integrable_overlap_weight (fun _ => 1) continuous_const).integrableOn
      (s := pilot3LongFuture δ)
  have he := hf.lintegral_longOverlap hδ (fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (overlap_nonneg (h := h) (f := f)))]
  exact ENNReal.ofReal_lt_top

theorem integrable_longDensity {δ : ℝ} (hδ : 0 < δ) : Integrable (pilot3LongDensity h f δ) :=
  integrable_toReal_of_lintegral_ne_top (hf.measurable_longDensityENN δ).aemeasurable
    (hf.lintegral_longDensityENN_lt_top hδ).ne

theorem integrable_longDensity_weight {δ : ℝ} (hδ : 0 < δ) (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable (fun σ => w σ * pilot3LongDensity h f δ σ) := by
  have hs := hf.hasCompactSupport_longDensity hδ
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport _))).mp
  exact IntegrableOn.continuousOn_mul hw.continuousOn (hf.integrable_longDensity hδ).integrableOn hs

/-- The independently defined geometric overlap measure. -/
def longOverlapMeasure (δ : ℝ) : Measure Pilot3Spacetime :=
  (volume.restrict (pilot3LongFuture δ)).withDensity (fun z => ENNReal.ofReal (pilot3Overlap h f z))

theorem map_longOverlapMeasure {δ : ℝ} (hδ : 0 < δ) :
    Measure.map (dimensionIntervalSq 0) (longOverlapMeasure (h := h) (f := f) δ) =
      volume.withDensity (pilot3LongDensityENN h f δ) := by
  apply Measure.ext_of_lintegral
  intro w hw
  have hq : Measurable (dimensionIntervalSq (0 : Pilot3Spacetime)) := by
    unfold dimensionIntervalSq
    fun_prop
  have hg : Measurable (fun z => w (dimensionIntervalSq (0 : Pilot3Spacetime) z)) := hw.comp hq
  rw [lintegral_map hw hq, longOverlapMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hf.measurable_overlap.ennreal_ofReal hg,
    lintegral_withDensity_eq_lintegral_mul _ (hf.measurable_longDensityENN δ) hw]
  exact hf.lintegral_longOverlap hδ w hw

/-- Signed transport, with the absolute-integrability obligations available
separately above. No polynomial subtraction has been used. -/
theorem integral_longOverlap {δ : ℝ} (hδ : 0 < δ) (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ z in pilot3LongFuture δ, w (dimensionIntervalSq 0 z) * pilot3Overlap h f z) =
      ∫ σ : ℝ, w σ * pilot3LongDensity h f δ σ := by
  have hq : Measurable (dimensionIntervalSq (0 : Pilot3Spacetime)) := by
    unfold dimensionIntervalSq
    fun_prop
  have he : (∫ σ, w σ ∂Measure.map (dimensionIntervalSq 0) (longOverlapMeasure (h := h) (f := f) δ)) =
      ∫ z in pilot3LongFuture δ, w (dimensionIntervalSq 0 z) * pilot3Overlap h f z := by
    rw [integral_map hq.aemeasurable hw.measurable.aestronglyMeasurable, longOverlapMeasure,
      integral_withDensity_eq_integral_toReal_smul₀ hf.measurable_overlap.ennreal_ofReal.aemeasurable
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (overlap_nonneg (h := h) (f := f) _), smul_eq_mul, mul_comm]
  rw [← he, hf.map_longOverlapMeasure hδ,
    integral_withDensity_eq_integral_toReal_smul₀ (hf.measurable_longDensityENN δ).aemeasurable
      (Eventually.of_forall (hf.longDensityENN_lt_top hδ))]
  simp only [pilot3LongDensity, smul_eq_mul, mul_comm]

/-- Exact finite-density relation to the long causal-pair contribution. -/
theorem longAction_eq_density {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    pilot3LongAction ρ δ h f = -(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ *
      ∫ σ : ℝ, dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
        pilot3LongDensity h f δ σ := by
  unfold pilot3LongAction pilot3DisplacementKernel dimensionBilocalKernel
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
  have hw : Continuous (fun σ : ℝ => dimensionKernel 3
      (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) :=
    (continuous_dimensionKernel 3).comp
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num : 0 ≤ (3 / 2 : ℝ))))
  rw [hf.integral_longOverlap hδ _ hw]

end SmoothPilot3
end BoundaryDraft
