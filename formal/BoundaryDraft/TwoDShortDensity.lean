import BoundaryDraft.TwoDShortCoordinates

/-!
# Actual whole-region 2D short density and signed transport

Nonnegative transport precedes integrability and signed Fubini. The density
uses the canonical overlap via its proved displacement representation.
The `1/(2*v)` Jacobian is singular at the vertex: finiteness here is ALMOST
EVERYWHERE, derived from the finite total geometric mass. No false uniform
bound or finite zero-proper-time fibre is assumed.
-/

open MeasureTheory Set
open scoped BigOperators Topology ENNReal Classical
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

/-- Nonnegative overlap density in angular and short proper-time coordinates. -/
def twoDShortProperTimeOverlap (h g : TwoDSpace → ℝ) (δ : ℝ) (ω : TwoDDirection)
    (p : Plane) : ℝ≥0∞ :=
  (shortProperTimeDomain δ).indicator (fun p =>
    ENNReal.ofReal (twoDNullJacobian (p 0) (p 1)) *
      ENNReal.ofReal (twoDDisplacementOverlap h g (twoDProperTimeDisplacement ω p))) p

/-- The extended density, defined before any finiteness conclusion. -/
def twoDShortOverlapDensityENN (h g : TwoDSpace → ℝ) (δ σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ v : ℝ, twoDShortProperTimeOverlap h g δ ω ![σ,v]) ∂twoDDirectionMeasure

/-- The real density for the entire signed kernel. -/
def twoDShortOverlapDensity (h g : TwoDSpace → ℝ) (δ σ : ℝ) : ℝ :=
  (twoDShortOverlapDensityENN h g δ σ).toReal

theorem measurable_twoDShortProperTimeOverlap {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) :
    Measurable (fun p : TwoDDirection × Plane => twoDShortProperTimeOverlap h g δ p.1 p.2) := by
  have hj : Measurable (fun p : TwoDDirection × Plane =>
      ENNReal.ofReal (twoDNullJacobian (p.2 0) (p.2 1)) *
        ENNReal.ofReal (twoDDisplacementOverlap h g (twoDProperTimeDisplacement p.1 p.2))) :=
    Measurable.mul (by unfold twoDNullJacobian; fun_prop)
      ((H.measurable_overlap).comp measurable_twoDProperTimeDisplacement).ennreal_ofReal
  simpa only [twoDShortProperTimeOverlap, ← indicator_comp_right, Function.comp_def] using
    hj.indicator ((measurableSet_shortProperTimeDomain δ).preimage measurable_snd)

private theorem measurable_twoDShortPlanePair :
    Measurable (fun p : ℝ × ℝ => (![p.1,p.2] : Plane)) :=
  MeasurableEquiv.finTwoArrow.symm.measurable

private theorem measurable_twoDShortDensityIntegrand {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) :
    Measurable (fun p : (ℝ × TwoDDirection) × ℝ =>
      twoDShortProperTimeOverlap h g δ p.1.2 ![p.1.1,p.2]) := by
  apply (measurable_twoDShortProperTimeOverlap H δ).comp
    (f := fun p : (ℝ × TwoDDirection) × ℝ => (p.1.2, (![p.1.1,p.2] : Plane)))
  exact (measurable_snd.comp measurable_fst).prodMk
    (measurable_twoDShortPlanePair.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem measurable_twoDShortOverlapDensityENN {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) :
    Measurable (twoDShortOverlapDensityENN h g δ) :=
  (measurable_twoDShortDensityIntegrand H δ).lintegral_prod_right.lintegral_prod_right

theorem measurable_twoDShortOverlapDensity {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) :
    Measurable (twoDShortOverlapDensity h g δ) :=
  (measurable_twoDShortOverlapDensityENN H δ).ennreal_toReal

theorem twoDShortOverlapDensity_nonneg (h g : TwoDSpace → ℝ) (δ σ : ℝ) :
    0 ≤ twoDShortOverlapDensity h g δ σ := ENNReal.toReal_nonneg

private theorem lintegral_twoDShortPlane_fibres (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p) = ∫⁻ σ : ℝ, ∫⁻ v : ℝ, f ![σ,v] := by
  have he := (volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow
  rw [← he.lintegral_comp hf, Measure.volume_eq_prod]
  exact lintegral_prod _ (hf.comp he.measurable).aemeasurable

/-- Nonnegative disintegration of the original short geometric overlap. -/
theorem lintegral_twoDShortOverlap {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g)
    (δ : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in twoDShortFuture δ, ENNReal.ofReal (twoDDisplacementOverlap h g z) * f (dimensionIntervalSq 0 z)) =
      ∫⁻ σ : ℝ, twoDShortOverlapDensityENN h g δ σ * f σ := by
  have hq : Measurable (dimensionIntervalSq (0 : TwoDSpacetime)) :=
    (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hF : Measurable (fun z => ENNReal.ofReal (twoDDisplacementOverlap h g z) * f (dimensionIntervalSq 0 z)) :=
    (H.measurable_overlap).ennreal_ofReal.mul (hf.comp hq)
  rw [lintegral_twoDShortFuture_properTime δ _ hF]
  have he (ω : TwoDDirection) :
      (∫⁻ p in shortProperTimeDomain δ,
        ENNReal.ofReal (twoDNullJacobian (p 0) (p 1)) *
          (ENNReal.ofReal (twoDDisplacementOverlap h g (twoDProperTimeDisplacement ω p)) *
            f (dimensionIntervalSq 0 (twoDProperTimeDisplacement ω p)))) =
        ∫⁻ p : Plane, twoDShortProperTimeOverlap h g δ ω p * f (p 0) := by
    rw [← lintegral_indicator (measurableSet_shortProperTimeDomain δ)]
    apply lintegral_congr
    intro p
    by_cases hp : p ∈ shortProperTimeDomain δ
    · simp [twoDShortProperTimeOverlap, hp,
        twoD_intervalSq_properTimeDisplacement ω p hp.2.2.1.ne', mul_assoc]
    · simp [twoDShortProperTimeOverlap, hp]
  change (∫⁻ ω, (∫⁻ p in shortProperTimeDomain δ,
    ENNReal.ofReal (twoDNullJacobian (p 0) (p 1)) *
      (ENNReal.ofReal (twoDDisplacementOverlap h g (twoDProperTimeDisplacement ω p)) *
        f (dimensionIntervalSq 0 (twoDProperTimeDisplacement ω p)))) ∂twoDDirectionMeasure) = _
  simp_rw [he]
  have hi := measurable_twoDShortDensityIntegrand H δ
  have hw (ω : TwoDDirection) : Measurable (twoDShortProperTimeOverlap h g δ ω) :=
    (measurable_twoDShortProperTimeOverlap H δ).comp
      (f := fun p : Plane => (ω,p)) (measurable_const.prodMk measurable_id)
  have hplane (ω : TwoDDirection) := lintegral_twoDShortPlane_fibres
    (fun p => twoDShortProperTimeOverlap h g δ ω p * f (p 0))
    ((hw ω).mul (hf.comp (measurable_pi_apply 0)))
  simp_rw [hplane]
  change (∫⁻ ω, (∫⁻ σ : ℝ, ∫⁻ v : ℝ, twoDShortProperTimeOverlap h g δ ω ![σ,v] * f σ)
    ∂twoDDirectionMeasure) = _
  have him : Measurable (fun p : (ℝ × TwoDDirection) × ℝ =>
      twoDShortProperTimeOverlap h g δ p.1.2 ![p.1.1,p.2] * f p.1.1) :=
    hi.mul (hf.comp (measurable_fst.comp measurable_fst))
  rw [← lintegral_lintegral_swap him.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro σ
  have hv (ω : TwoDDirection) : Measurable (fun v : ℝ => twoDShortProperTimeOverlap h g δ ω ![σ,v]) :=
    (hw ω).comp (measurable_twoDShortPlanePair.comp (measurable_const.prodMk measurable_id))
  simp_rw [lintegral_mul_const (f σ) (hv _)]
  have hinner : Measurable (fun p : ℝ × TwoDDirection =>
      ∫⁻ v : ℝ, twoDShortProperTimeOverlap h g δ p.2 ![p.1,v]) := hi.lintegral_prod_right
  exact lintegral_mul_const _
    (hinner.comp (f := fun ω : TwoDDirection => (σ,ω)) (measurable_const.prodMk measurable_id))

theorem twoDShortOverlapDensityENN_negative (h g : TwoDSpace → ℝ) (δ : ℝ) {σ : ℝ} (hσ : σ < 0) :
    twoDShortOverlapDensityENN h g δ σ = 0 := by
  have he (ω : TwoDDirection) (v : ℝ) : twoDShortProperTimeOverlap h g δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    exact (not_le_of_gt hσ) hp.1
  simp [twoDShortOverlapDensityENN, he]

/-- The density even vanishes at the upper endpoint, since the cutoff is strict. -/
theorem twoDShortOverlapDensityENN_zero_of_le (h g : TwoDSpace → ℝ) (δ : ℝ)
    {σ : ℝ} (hσ : δ ^ 2 ≤ σ) : twoDShortOverlapDensityENN h g δ σ = 0 := by
  have he (ω : TwoDDirection) (v : ℝ) : twoDShortProperTimeOverlap h g δ ω ![σ,v] = 0 := by
    apply indicator_of_not_mem
    intro hp
    have hv : 0 < v := hp.2.2.1
    have hvδ : v < δ := hp.2.2.2
    have hsq : σ ≤ v ^ 2 := hp.2.1
    have := (sq_lt_sq₀ hv.le (hv.trans hvδ).le).mpr hvδ
    linarith
  simp only [twoDShortOverlapDensityENN, he, lintegral_zero]

theorem support_twoDShortOverlapDensity_subset (h g : TwoDSpace → ℝ) (δ : ℝ) :
    Function.support (twoDShortOverlapDensity h g δ) ⊆ Icc 0 (δ ^ 2) := by
  intro σ hσ
  by_contra hn
  by_cases hneg : σ < 0
  · exact hσ (by simp [twoDShortOverlapDensity, twoDShortOverlapDensityENN_negative h g δ hneg])
  · have hlarge : δ ^ 2 < σ := lt_of_not_ge (fun hle => hn ⟨le_of_not_gt hneg, hle⟩)
    exact hσ (by simp [twoDShortOverlapDensity, twoDShortOverlapDensityENN_zero_of_le h g δ hlarge.le])

theorem hasCompactSupport_twoDShortOverlapDensity (h g : TwoDSpace → ℝ) (δ : ℝ) :
    HasCompactSupport (twoDShortOverlapDensity h g δ) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => by
    by_contra hs
    exact hx (support_twoDShortOverlapDensity_subset h g δ hs)

/-- The literal nonnegative average on nonnegative proper-time square. The
sharp upper cutoff is retained, including its omission at equality. -/
theorem twoDShortOverlapDensityENN_eq_average (h g : TwoDSpace → ℝ) (δ : ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    twoDShortOverlapDensityENN h g δ σ = ∫⁻ ω, (∫⁻ v in Ioo 0 δ,
      if σ ≤ v ^ 2 then ENNReal.ofReal (twoDNullJacobian σ v) *
        ENNReal.ofReal (twoDDisplacementOverlap h g (twoDProperTimeDisplacement ω ![σ,v])) else 0)
      ∂twoDDirectionMeasure := by
  apply lintegral_congr
  intro ω
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro v
  have hd : (![σ,v] : Plane) ∈ shortProperTimeDomain δ ↔ σ ≤ v ^ 2 ∧ v ∈ Ioo 0 δ := by
    simp only [shortProperTimeDomain, mem_setOf_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hσ, true_and, mem_Ioo]
  by_cases hv : v ∈ Ioo 0 δ <;> by_cases hs : σ ≤ v ^ 2 <;>
    simp [twoDShortProperTimeOverlap, hd, hv, hs]

/-- Finite mass is inherited from the actual bounded geometric overlap. -/
theorem lintegral_twoDShortOverlapDensityENN_lt_top {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) : (∫⁻ σ, twoDShortOverlapDensityENN h g δ σ) < ⊤ := by
  have hi : IntegrableOn (twoDDisplacementOverlap h g) (twoDShortFuture δ) := by
    simpa only [one_mul] using (H.integrable_overlap_weight (fun _ => 1) continuous_const).integrableOn (s := twoDShortFuture δ)
  have he := lintegral_twoDShortOverlap H δ (fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← he, ← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (SmoothTwoD.overlap_nonneg (h := h) (f := g)))]
  exact ENNReal.ofReal_lt_top

theorem integrable_twoDShortOverlapDensity {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) : Integrable (twoDShortOverlapDensity h g δ) :=
  integrable_toReal_of_lintegral_ne_top (measurable_twoDShortOverlapDensityENN H δ).aemeasurable
    (lintegral_twoDShortOverlapDensityENN_lt_top H δ).ne

/-- Geometric short overlap measure on the original spacetime, independent of
its proper-time density. -/
def twoDShortOverlapMeasure (h g : TwoDSpace → ℝ) (δ : ℝ) : Measure TwoDSpacetime :=
  (volume.restrict (twoDShortFuture δ)).withDensity (fun z => ENNReal.ofReal (twoDDisplacementOverlap h g z))

theorem map_twoDShortOverlapMeasure {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) :
    Measure.map (dimensionIntervalSq 0) (twoDShortOverlapMeasure h g δ) =
      volume.withDensity (twoDShortOverlapDensityENN h g δ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hq : Measurable (dimensionIntervalSq (0 : TwoDSpacetime)) :=
    (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have hg : Measurable (fun z => f (dimensionIntervalSq 0 z)) := hf.comp hq
  rw [lintegral_map hf hq, twoDShortOverlapMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (H.measurable_overlap).ennreal_ofReal hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_twoDShortOverlapDensityENN H δ) hf]
  exact lintegral_twoDShortOverlap H δ f hf

/-- Absolute integrability is proved before inserting a signed continuous kernel. -/
theorem integrable_twoDShortOverlapDensity_weight {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun σ => f σ * twoDShortOverlapDensity h g δ σ) := by
  have hq : Continuous (dimensionIntervalSq (0 : TwoDSpacetime)) :=
    continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)
  have hi := (H.integrable_overlap_weight (fun z => f (dimensionIntervalSq 0 z)) (hf.comp hq)).integrableOn
    (s := twoDShortFuture δ)
  have hfinite : ∀ᵐ z ∂volume.restrict (twoDShortFuture δ), ENNReal.ofReal (twoDDisplacementOverlap h g z) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi' : Integrable (fun z => f (dimensionIntervalSq 0 z)) (twoDShortOverlapMeasure h g δ) := by
    apply (integrable_withDensity_iff (H.measurable_overlap).ennreal_ofReal hfinite).mpr
    simpa only [ENNReal.toReal_ofReal (SmoothTwoD.overlap_nonneg (h := h) (f := g) _)] using hi
  have hif : Integrable f (Measure.map (dimensionIntervalSq 0) (twoDShortOverlapMeasure h g δ)) :=
    (integrable_map_measure hf.measurable.aestronglyMeasurable hq.measurable.aemeasurable).mpr hi'
  rw [map_twoDShortOverlapMeasure H δ] at hif
  exact (integrable_withDensity_iff (measurable_twoDShortOverlapDensityENN H δ)
    (ae_lt_top (measurable_twoDShortOverlapDensityENN H δ)
      (lintegral_twoDShortOverlapDensityENN_lt_top H δ).ne)).mp hif

/-- Exact signed finite-density identity for the actual original region. -/
theorem integral_twoDShortOverlap {h g : TwoDSpace → ℝ} (H : SmoothTwoD h g) (δ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ z in twoDShortFuture δ, f (dimensionIntervalSq 0 z) * twoDDisplacementOverlap h g z) =
      ∫ σ : ℝ, f σ * twoDShortOverlapDensity h g δ σ := by
  have hq : Measurable (dimensionIntervalSq (0 : TwoDSpacetime)) :=
    (continuous_dimensionIntervalSq.comp (continuous_const.prodMk continuous_id)).measurable
  have he : (∫ σ, f σ ∂Measure.map (dimensionIntervalSq 0) (twoDShortOverlapMeasure h g δ)) =
      ∫ z in twoDShortFuture δ, f (dimensionIntervalSq 0 z) * twoDDisplacementOverlap h g z := by
    rw [integral_map hq.aemeasurable hf.measurable.aestronglyMeasurable, twoDShortOverlapMeasure,
      integral_withDensity_eq_integral_toReal_smul₀
        (H.measurable_overlap).ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (SmoothTwoD.overlap_nonneg (h := h) (f := g) _), smul_eq_mul, mul_comm]
  rw [← he, map_twoDShortOverlapMeasure H δ,
    integral_withDensity_eq_integral_toReal_smul₀ (measurable_twoDShortOverlapDensityENN H δ).aemeasurable
      (ae_lt_top (measurable_twoDShortOverlapDensityENN H δ)
      (lintegral_twoDShortOverlapDensityENN_lt_top H δ).ne)]
  simp only [twoDShortOverlapDensity, smul_eq_mul, mul_comm]

/-- Only a proved null singleton separates the closed and open half-lines. -/
theorem integral_twoDShortOverlapDensity_eq_Ioi (h g : TwoDSpace → ℝ) (δ : ℝ) (w : ℝ → ℝ) :
    (∫ σ : ℝ, w σ * twoDShortOverlapDensity h g δ σ) =
      ∫ σ : ℝ in Ioi 0, w σ * twoDShortOverlapDensity h g δ σ := by
  rw [← integral_Ici_eq_integral_Ioi]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro σ hσ
  have hneg : σ < 0 := lt_of_not_ge hσ
  simp [twoDShortOverlapDensity, twoDShortOverlapDensityENN_negative h g δ hneg]

/-- Fully normalized density formula for the actual short observable. -/
theorem SmoothTwoD.shortAction_eq_density {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    (ρ δ : ℝ) : twoDShortAction ρ δ h f =
      ρ ^ (2 / 2 : ℝ) * (dimensionPointCoefficient 2 * volume.real (twoDRegion h f) -
        dimensionPairCoefficient 2 * ρ * ∫ σ : ℝ in Ioi 0,
          dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ ^ (2 / 2 : ℝ)) *
            twoDShortOverlapDensity h f δ σ) := by
  have hc : Continuous (fun σ : ℝ => dimensionKernel 2
      (dimensionIntervalCoefficient 2 * ρ * σ ^ (2 / 2 : ℝ))) :=
    (continuous_dimensionKernel 2).comp
      (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num))))
  have he := integral_twoDShortOverlap hf δ _ hc
  change (∫ z in twoDShortFuture δ, twoDDisplacementKernel ρ z * twoDDisplacementOverlap h f z) = _ at he
  rw [twoDShortAction, he, integral_twoDShortOverlapDensity_eq_Ioi]

end BoundaryDraft
