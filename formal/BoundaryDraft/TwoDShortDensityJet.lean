import BoundaryDraft.TwoDShortFibre

/-!
# Produced logarithmic expansion of the actual whole-region 2D short density

The measurable cubic remainder, its compensated closing-fibre jet, the exact
polynomial logarithms, and the independent endpoint target are all derived.
This file does not yet claim cancellation against the signed action kernel.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem continuous_absoluteShortPolynomial : Continuous (twoDAbsoluteShortPolynomial h f) := by
  obtain ⟨_, _, F, _, hP, _⟩ := hf.exists_absoluteOverlap_taylorPolynomial
  rw [funext hP]
  exact (continuous_const.add (fderiv ℝ F 0).continuous).add
    (continuous_const.mul ((fderiv ℝ (fderiv ℝ F) 0).continuous.clm_apply continuous_id))

theorem intervalIntegrable_shortPolynomial_fibre {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hσδ : σ ≤ δ ^ 2) (ω : TwoDDirection) :
    IntervalIntegrable (fun v => twoDNullJacobian σ v *
      twoDAbsoluteShortPolynomial h f (TwoDShortRemainder.point ω v σ)) volume (Real.sqrt σ) δ := by
  apply ContinuousOn.intervalIntegrable
  intro v hv
  rw [uIcc_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hσδ⟩)] at hv
  have hv0 : v ≠ 0 := ((Real.sqrt_pos.mpr hσ).trans_le hv.1).ne'
  have hv2 : 2 * v ≠ 0 := mul_ne_zero (by norm_num) hv0
  have hJ : ContinuousAt (twoDNullJacobian σ) v := by unfold twoDNullJacobian; fun_prop (disch := assumption)
  have hP : ContinuousAt (fun v => TwoDShortRemainder.point ω v σ) v := by
    unfold TwoDShortRemainder.point
    fun_prop (disch := assumption)
  exact (hJ.mul (hf.continuous_absoluteShortPolynomial.continuousAt.comp hP)).continuousWithinAt

/-- Signed polynomial Fubini is a finite two-atom sum, with each interval
integral absolutely integrable before its signed splitting. -/
theorem shortPolynomialDensity_eq_angular_interval {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hσδ : σ ≤ δ ^ 2) :
    twoDShortPolynomialDensity h f δ σ = ∫ ω : TwoDDirection,
      (∫ v in Real.sqrt σ..δ, twoDNullJacobian σ v *
        twoDAbsoluteShortPolynomial h f (TwoDShortRemainder.point ω v σ)) ∂twoDDirectionMeasure := by
  simp only [twoDShortPolynomialDensity, integral_twoDDirection, mul_add]
  exact intervalIntegral.integral_add (hf.intervalIntegrable_shortPolynomial_fibre hδ hσ hσδ twoDRight)
    (hf.intervalIntegrable_shortPolynomial_fibre hδ hσ hσδ twoDLeft)

omit hf in
private theorem intervalIntegrable_remainder_fibre {R : TwoDSpacetime → ℝ} {δ T σ : ℝ}
    (hB : TwoDShortRemainder.CubicBounds R δ T) (hR : Measurable R)
    (hδ : 0 < δ) (hσ : 0 < σ) (hσδ : σ ≤ δ ^ 2) (ω : TwoDDirection) :
    IntervalIntegrable (TwoDShortRemainder.fibre R ω · σ) volume (Real.sqrt σ) δ := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hσδ⟩)]
  apply (integrable_const (T * δ ^ 2)).mono'
    (show Measurable (fun v => TwoDShortRemainder.fibre R ω v σ) by
      unfold TwoDShortRemainder.fibre twoDNullJacobian TwoDShortRemainder.point
      fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hv0 := (Real.sqrt_pos.mpr hσ).trans hv.1
  exact ((hB.bounds ω ⟨hv0, hv.2⟩ ⟨hσ.le, (Real.sqrt_le_iff.mp hv.1.le).2⟩).1).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0.le hv.2.le 2) hB.nonneg)

/-- Exact splitting of the ORIGINAL short density. It includes the cutoff
contact and has no original-overlap zero-sigma finiteness premise. -/
theorem shortDensity_eq_polynomial_add_remainder {R : TwoDSpacetime → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hR : Measurable R) (hB : TwoDShortRemainder.CubicBounds R δ T)
    (he : ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
      twoDOverlap h f z.1 z.2 = twoDAbsoluteShortPolynomial h f z + R z)
    {σ : ℝ} (hσ : 0 < σ) (hσδ : σ ≤ δ ^ 2) :
    twoDShortOverlapDensity h f δ σ =
      twoDShortPolynomialDensity h f δ σ + TwoDShortRemainder.density R δ σ := by
  have hsplit (ω : TwoDDirection) :
      (∫ v in Real.sqrt σ..δ, twoDNullJacobian σ v *
        twoDDisplacementOverlap h f (TwoDShortRemainder.point ω v σ)) =
      (∫ v in Real.sqrt σ..δ, twoDNullJacobian σ v *
        twoDAbsoluteShortPolynomial h f (TwoDShortRemainder.point ω v σ)) +
      ∫ v in Real.sqrt σ..δ, TwoDShortRemainder.fibre R ω v σ := by
    rw [← intervalIntegral.integral_add (hf.intervalIntegrable_shortPolynomial_fibre hδ hσ hσδ ω)
      (intervalIntegrable_remainder_fibre hB hR hδ hσ hσδ ω)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ v : ℝ, v ≠ δ by simp [ae_iff]] with v hvne hv
    rw [uIoc_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hσδ⟩)] at hv
    have hv0 := (Real.sqrt_pos.mpr hσ).trans hv.1
    have hvδ : v < δ := lt_of_le_of_ne hv.2 hvne
    have hsq : σ ∈ Icc 0 (v ^ 2) := ⟨hσ.le, (Real.sqrt_le_iff.mp hv.1.le).2⟩
    rw [hf.displacementOverlap_eq_actual _, he _ (TwoDShortRemainder.CubicBounds.point_mem ω ⟨hv0, hvδ⟩ hsq)
      (TwoDShortRemainder.point_causal ω hv0 hsq)]
    exact mul_add _ _ _
  rw [hf.shortDensity_eq_interval hδ hσ hσδ,
    hf.shortPolynomialDensity_eq_angular_interval hδ hσ hσδ,
    hB.density_eq_iterated hR hσ.le]
  simp only [TwoDShortFibre.integral_truncate hδ hσ hσδ, integral_twoDDirection, hsplit]
  dsimp only [TwoDShortRemainder.fibre]
  ring

/-- Unconditional geometric producer of BOTH logarithmic sectors of the
actual short density. The right remainder is signed first-order little-o. -/
theorem shortDensity_logarithmic_jet :
    ∃ δ : ℝ, 0 < δ ∧ ∃ a₀ a₁ : ℝ,
      (fun σ => twoDShortOverlapDensity h f δ σ -
        (a₀ + a₁ * σ - (volume.real (twoDRegion h f) / 2) * Real.log σ -
          (twoDBoundaryIntegral h f / 8) * σ * Real.log σ)) =o[𝓝[>] 0] (fun σ => σ) := by
  obtain ⟨δ, hδ, R, T, hR, hB, he⟩ := hf.exists_absoluteOverlap_remainder
  obtain ⟨b₀, b₁, hb⟩ := hB.density_right_affine_jet hR
  let c₀ := volume.real (twoDRegion h f) * Real.log δ - volume.real {x | 0 < h x} * δ / 2 +
    (twoDShortTimeCoefficient h + twoDShortSpaceCoefficient h f) * δ ^ 2 / 16
  let c₁ := volume.real {x | 0 < h x} / (2 * δ) + twoDBoundaryIntegral h f * Real.log δ / 4
  let c₂ := (twoDShortTimeCoefficient h + twoDShortSpaceCoefficient h f) / (16 * δ ^ 2)
  have hsq : (fun σ : ℝ => σ ^ 2) =o[𝓝[>] 0] (fun σ => σ) :=
    (isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2)).mono nhdsWithin_le_nhds
  refine ⟨δ, hδ, c₀ + b₀, c₁ + b₁, (hb.sub (hsq.const_mul_left c₂)).congr' ?_ EventuallyEq.rfl⟩
  filter_upwards [MonotoneHinge.eventually_right (sq_pos_of_pos hδ)] with σ hσ
  rw [hf.shortDensity_eq_polynomial_add_remainder hδ hR hB he hσ.1 hσ.2,
    hf.shortPolynomialDensity_eq hδ hσ.1 hσ.2]
  dsimp only [c₀, c₁, c₂]
  ring

end SmoothTwoD
end BoundaryDraft
