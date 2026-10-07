import BoundaryDraft.TwoDLongDensity
import BoundaryDraft.TwoDLongGeometry

/-!
# Pointwise disintegration into actual 2D hinge fibres

Tonelli precedes real transport and gives absolute integrability on the full
direction/source product. No measurable selection of contact roots is used.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
noncomputable section
namespace BoundaryDraft
namespace TwoDLongFibre

set_option maxHeartbeats 1000000

abbrev Parameter := TwoDDirection × TwoDSpace

/-- The unsigned gap product, before the finite length truncation. -/
def gapIntegrand (h f : TwoDSpace → ℝ) (σ : ℝ) (p : Parameter × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (twoDNullJacobian σ p.2) * ENNReal.ofReal (max 0 (twoDRayGap h f p.1.2 p.1.1.val σ p.2))

def integrandENN (h f : TwoDSpace → ℝ) (δ V σ : ℝ) (p : Parameter × ℝ) : ℝ≥0∞ :=
  (Icc δ V).indicator (fun v => gapIntegrand h f σ (p.1, v)) p.2

def fibreENN (h f : TwoDSpace → ℝ) (δ V σ : ℝ) (p : Parameter) : ℝ≥0∞ :=
  ∫⁻ v, integrandENN h f δ V σ (p, v)

theorem measurable_gapIntegrand {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (σ : ℝ) :
    Measurable (gapIntegrand h f σ) := by
  have hg : Measurable (fun p : Parameter × ℝ => twoDRayGap h f p.1.2 p.1.1.val σ p.2) := by
    unfold twoDRayGap twoDOverlapGap twoDRayDisplacement
    exact (((hf.continuous_positivePart.measurable.comp (measurable_snd.comp measurable_fst)).add
      (hf.continuous_future.measurable.comp
        ((measurable_snd.comp measurable_fst).add
          ((by fun_prop : Measurable (fun p : Parameter × ℝ => (p.2 - σ / p.2) / 2)).smul
            (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)))))).sub
      (hf.continuous_future.measurable.comp (measurable_snd.comp measurable_fst))).sub (by fun_prop)
  unfold gapIntegrand
  apply Measurable.mul
  · unfold twoDNullJacobian
    fun_prop
  · exact (measurable_const.max hg).ennreal_ofReal

theorem measurable_integrandENN {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (δ V σ : ℝ) :
    Measurable (integrandENN h f δ V σ) := by
  simpa only [integrandENN, ← indicator_comp_right, Function.comp_def] using
    (measurable_gapIntegrand hf σ).indicator (measurableSet_Icc.preimage measurable_snd)

theorem measurable_fibreENN {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f) (δ V σ : ℝ) :
    Measurable (fibreENN h f δ V σ) := (measurable_integrandENN hf δ V σ).lintegral_prod_right'

theorem ray_causal {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) (hv : δ ≤ v)
    (ω : TwoDDirection) : ‖(twoDRayDisplacement ω.val σ v).2‖ ≤ (twoDRayDisplacement ω.val σ v).1 :=
  twoDRayDisplacement_causal (mem_sphere_zero_iff_norm.mp ω.property) (hδ.trans_le hv)
    ⟨hσ, hs.le.trans (pow_le_pow_left₀ hδ.le hv 2)⟩

theorem weight_nonneg {δ σ v : ℝ} (hδ : 0 < δ) (_hσ : 0 ≤ σ) (_hs : σ < δ ^ 2) (hv : δ ≤ v) :
    0 ≤ twoDNullJacobian σ v :=
  (twoDNullJacobian_pos σ (hδ.trans_le hv)).le

/-- Insert the independently proved actual overlap identity into the density,
then swap the nonnegative spatial and length integrals. Valid also at zero. -/
theorem densityENN_eq_gap_fibres {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) :
    twoDLongDensityENN h f δ σ = ∫⁻ ω, (∫⁻ x : TwoDSpace,
      ∫⁻ v in Ici δ, gapIntegrand h f σ ((ω, x), v)) ∂twoDDirectionMeasure := by
  have hlower : max δ (Real.sqrt σ) = δ := by
    apply max_eq_left
    exact (sq_le_sq₀ (Real.sqrt_nonneg σ) hδ.le).mp (by simpa only [Real.sq_sqrt hσ] using hs.le)
  rw [SmoothTwoD.longDensityENN_eq_average hδ hσ, hlower]
  apply lintegral_congr
  intro ω
  calc
    _ = ∫⁻ v in Ici δ, ∫⁻ x : TwoDSpace, gapIntegrand h f σ ((ω, x), v) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
      have hc := ray_causal hδ hσ hs hv ω
      have hi : Integrable (fun x => max 0 (twoDOverlapGap h f (twoDRayDisplacement ω.val σ v) x)) := by
        simpa only [one_mul] using hf.integrable_weighted_overlapGap (fun _ => 1) continuousOn_const
          (twoDRayDisplacement ω.val σ v) hc
      rw [hf.overlap_eq_gap _ hc, ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun _ => le_max_left _ _)]
      exact (lintegral_const_mul _
        (continuous_const.max (hf.continuous_overlapGap (twoDRayDisplacement ω.val σ v))).measurable.ennreal_ofReal).symm
    _ = _ := by
      have hm : Measurable (fun p : ℝ × TwoDSpace => gapIntegrand h f σ ((ω, p.2), p.1)) :=
        (measurable_gapIntegrand hf σ).comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
      exact lintegral_lintegral_swap hm.aemeasurable

/-- Finite oriented fibres are the real values of their nonnegative versions.
The range on sigma is needed for the sign of the 2D Jacobian. -/
theorem fibre_eq_toReal {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    {δ V σ : ℝ} (hδ : 0 < δ) (hV : δ ≤ V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) (p : Parameter) :
    MonotoneHinge.fibre (twoDRayGap h f p.2 p.1.val) twoDNullJacobian δ V σ =
      (fibreENN h f δ V σ p).toReal := by
  have hm := (measurable_integrandENN hf δ V σ).comp
    ((measurable_const (a := p)).prodMk measurable_id)
  have hp (v : ℝ) : (integrandENN h f δ V σ (p, v)).toReal =
      (Icc δ V).indicator (fun v => twoDNullJacobian σ v * max 0 (twoDRayGap h f p.2 p.1.val σ v)) v := by
    by_cases hv : v ∈ Icc δ V
    · have hw := weight_nonneg hδ hσ hs hv.1
      simp only [integrandENN, gapIntegrand, indicator_of_mem hv, ← ENNReal.ofReal_mul hw,
        ENNReal.toReal_ofReal (mul_nonneg hw (le_max_left _ _))]
    · simp [integrandENN, hv]
  rw [MonotoneHinge.fibre_eq_setIntegral _ _ hV, ← integral_indicator measurableSet_Icc]
  simp_rw [← hp]
  exact integral_toReal hm.aemeasurable (Eventually.of_forall fun v => by
    by_cases hv : v ∈ Icc δ V
    · simp only [integrandENN, gapIntegrand, indicator_of_mem hv]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    · simp [integrandENN, hv])

theorem lintegral_fibreENN_lt_top {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) (V : ℝ) :
    (∫⁻ p, fibreENN h f δ V σ p ∂(twoDDirectionMeasure.prod volume)) < ⊤ := by
  rw [lintegral_prod _ (measurable_fibreENN hf δ V σ).aemeasurable]
  apply lt_of_le_of_lt _ (hf.longDensityENN_lt_top hδ σ)
  rw [densityENN_eq_gap_fibres hf hδ hσ hs]
  apply lintegral_mono
  intro ω
  apply lintegral_mono
  intro x
  change (∫⁻ v, integrandENN h f δ V σ ((ω, x), v)) ≤ _
  simp only [integrandENN, lintegral_indicator measurableSet_Icc]
  exact lintegral_mono_set Icc_subset_Ici_self

theorem measurable_integrable_fibre {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    {δ V σ : ℝ} (hδ : 0 < δ) (hV : δ ≤ V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2) :
    Measurable (fun p : Parameter => MonotoneHinge.fibre
      (twoDRayGap h f p.2 p.1.val) twoDNullJacobian δ V σ) ∧
    Integrable (fun p : Parameter => MonotoneHinge.fibre
      (twoDRayGap h f p.2 p.1.val) twoDNullJacobian δ V σ) (twoDDirectionMeasure.prod volume) := by
  simp_rw [fibre_eq_toReal hf hδ hV hσ hs]
  exact ⟨(measurable_fibreENN hf δ V σ).ennreal_toReal,
    integrable_toReal_of_lintegral_ne_top (measurable_fibreENN hf δ V σ).aemeasurable
      (lintegral_fibreENN_lt_top hf hδ hσ hs V).ne⟩

theorem densityENN_eq_parameterFibre {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    {δ V σ : ℝ} (hδ : 0 < δ) (hV : δ < V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ (x : TwoDSpace) (ω : TwoDDirection), twoDRayGap h f x ω.val 0 V ≤ 0) :
    twoDLongDensityENN h f δ σ = ∫⁻ p, fibreENN h f δ V σ p ∂(twoDDirectionMeasure.prod volume) := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  rw [densityENN_eq_gap_fibres hf hδ hσ hs,
    lintegral_prod _ (measurable_fibreENN hf δ V σ).aemeasurable]
  apply lintegral_congr
  intro ω
  apply lintegral_congr
  intro x
  rw [fibreENN, ← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro v
  by_cases hlo : δ ≤ v
  · by_cases hhi : v ≤ V
    · simp [integrandENN, hlo, hhi]
    · have hg := C.rayGap_nonpos_of_cutoff_nonpos (hδ.trans hV) (not_le.mp hhi).le hσ
        x ω.val (mem_sphere_zero_iff_norm.mp ω.property) (hclear x ω)
      simp [integrandENN, gapIntegrand, hlo, hhi, max_eq_left hg]
  · simp [integrandENN, hlo]

/-- Real product-space identity follows pointwise finite nonnegative transport,
not an unjustified signed interchange. -/
theorem density_eq_parameterFibre {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
    {δ V σ : ℝ} (hδ : 0 < δ) (hV : δ < V) (hσ : 0 ≤ σ) (hs : σ < δ ^ 2)
    (hclear : ∀ (x : TwoDSpace) (ω : TwoDDirection), twoDRayGap h f x ω.val 0 V ≤ 0) :
    twoDLongDensity h f δ σ = ∫ p : Parameter, MonotoneHinge.fibre
      (twoDRayGap h f p.2 p.1.val) twoDNullJacobian δ V σ ∂(twoDDirectionMeasure.prod volume) := by
  simp_rw [fibre_eq_toReal hf hδ hV.le hσ hs]
  rw [twoDLongDensity, densityENN_eq_parameterFibre hf hδ hV hσ hs hclear]
  exact (integral_toReal (measurable_fibreENN hf δ V σ).aemeasurable
    (ae_lt_top (measurable_fibreENN hf δ V σ) (lintegral_fibreENN_lt_top hf hδ hσ hs V).ne)).symm

end TwoDLongFibre
end BoundaryDraft
