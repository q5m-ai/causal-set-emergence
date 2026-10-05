import BoundaryDraft.TwoDShortBasis
import BoundaryDraft.TwoDShortDensity
import BoundaryDraft.TwoDRemainderDensity

/-!
# Positive proper-time fibres of the actual short density

Finiteness is proved away from zero, where the inverse-length Jacobian has a
positive lower length bound. Nothing here asserts a finite zero-proper-time
fibre of the original overlap. Endpoint changes are justified by null sets.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft
namespace TwoDShortFibre

private theorem domain_eq (δ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Ioo 0 δ ∩ {v : ℝ | σ ≤ v ^ 2} = Ico (Real.sqrt σ) δ := by
  ext v
  constructor
  · rintro ⟨⟨hv, hvδ⟩, hs⟩
    exact ⟨Real.sqrt_le_iff.mpr ⟨hv.le, hs⟩, hvδ⟩
  · rintro ⟨hv, hvδ⟩
    exact ⟨⟨(Real.sqrt_pos.mpr hσ).trans_le hv, hvδ⟩, (Real.sqrt_le_iff.mp hv).2⟩

theorem integral_truncate {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hσδ : σ ≤ δ ^ 2) (G : ℝ → ℝ) :
    (∫ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then G v else 0) = ∫ v in Real.sqrt σ..δ, G v := by
  change (∫ v in Ioo (0 : ℝ) δ, ({v : ℝ | σ ≤ v ^ 2}.indicator G) v) = _
  have hm : MeasurableSet {v : ℝ | σ ≤ v ^ 2} := measurableSet_le measurable_const (by fun_prop)
  rw [setIntegral_indicator hm, domain_eq δ hσ, Measure.restrict_congr_set Ico_ae_eq_Ioc,
    intervalIntegral.integral_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hσδ⟩)]

theorem lintegral_truncate (δ : ℝ) {σ : ℝ} (hσ : 0 < σ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then G v else 0) =
      ∫⁻ v in Ioc (Real.sqrt σ) δ, G v := by
  change (∫⁻ v in Ioo (0 : ℝ) δ, ({v : ℝ | σ ≤ v ^ 2}.indicator G) v) = _
  have hm : MeasurableSet {v : ℝ | σ ≤ v ^ 2} := measurableSet_le measurable_const (by fun_prop)
  rw [setLIntegral_indicator hm, inter_comm, domain_eq δ hσ, Measure.restrict_congr_set Ico_ae_eq_Ioc]

end TwoDShortFibre
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- Each positive-sigma original-overlap fibre is absolutely integrable. -/
theorem integrableOn_shortOverlap_fibre (δ : ℝ) {σ : ℝ} (hσ : 0 < σ) (ω : TwoDDirection) :
    IntegrableOn (fun v => twoDNullJacobian σ v *
      twoDDisplacementOverlap h f (TwoDShortRemainder.point ω v σ)) (Ioc (Real.sqrt σ) δ) := by
  have hsm : Measurable (fun v => twoDNullJacobian σ v *
      twoDDisplacementOverlap h f (TwoDShortRemainder.point ω v σ)) :=
    (show Measurable (twoDNullJacobian σ) by unfold twoDNullJacobian; fun_prop).mul
      (hf.measurable_overlap.comp (by unfold TwoDShortRemainder.point; fun_prop))
  apply (integrable_const (1 / (2 * Real.sqrt σ) * volume.real (twoDRegion h f))).mono'
    hsm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hsv := Real.sqrt_pos.mpr hσ
  have hv0 := hsv.trans hv.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (twoDNullJacobian_pos σ hv0).le,
    abs_of_nonneg (overlap_nonneg _)]
  exact mul_le_mul (twoDNullJacobian_le σ hsv hv.1.le) (hf.overlap_le_volume _)
    (overlap_nonneg _) (by positivity)

/-- The real density agrees with the ordinary two-direction interval average
at EVERY positive sigma below the fixed cutoff, not just almost everywhere. -/
theorem shortDensity_eq_interval {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hσδ : σ ≤ δ ^ 2) :
    twoDShortOverlapDensity h f δ σ = ∫ ω : TwoDDirection,
      (∫ v in Real.sqrt σ..δ, twoDNullJacobian σ v *
        twoDDisplacementOverlap h f (TwoDShortRemainder.point ω v σ)) ∂twoDDirectionMeasure := by
  let G := fun (ω : TwoDDirection) v => twoDNullJacobian σ v *
    twoDDisplacementOverlap h f (TwoDShortRemainder.point ω v σ)
  have hnon (ω : TwoDDirection) : 0 ≤ᶠ[ae (volume.restrict (Ioc (Real.sqrt σ) δ))] G ω := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (twoDNullJacobian_pos σ ((Real.sqrt_pos.mpr hσ).trans hv.1)).le (overlap_nonneg _)
  have he (ω : TwoDDirection) :
      (∫⁻ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then ENNReal.ofReal (twoDNullJacobian σ v) *
        ENNReal.ofReal (twoDDisplacementOverlap h f (twoDProperTimeDisplacement ω ![σ,v])) else 0) =
      ENNReal.ofReal (∫ v in Ioc (Real.sqrt σ) δ, G ω v) := by
    rw [TwoDShortFibre.lintegral_truncate δ hσ,
      ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_shortOverlap_fibre δ hσ ω) (hnon ω)]
    apply setLIntegral_congr_fun measurableSet_Ioc
    filter_upwards with v
    intro hv
    exact (ENNReal.ofReal_mul (twoDNullJacobian_pos σ ((Real.sqrt_pos.mpr hσ).trans hv.1)).le).symm
  rw [twoDShortOverlapDensity, twoDShortOverlapDensityENN_eq_average h f δ hσ.le]
  simp only [he, twoDDirectionMeasure_eq_dirac, lintegral_add_measure, lintegral_dirac]
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (hnon twoDRight)),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (hnon twoDLeft)),
    integral_add_measure integrable_dirac integrable_dirac, integral_dirac, integral_dirac]
  simp only [intervalIntegral.integral_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hσδ⟩)]
  rfl

end SmoothTwoD
end BoundaryDraft
