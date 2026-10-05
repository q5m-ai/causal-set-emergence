import BoundaryDraft.TwoDLogScaling

/-! # Quadratically bounded errors have zero physical 2D signed response -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDQuadraticResponse

def absoluteSecondMoment : ℝ := ∫ u : ℝ in Ioi 0, u ^ 2 * |dimensionKernel 2 u|

theorem integrable_absolute_second {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun σ : ℝ => σ ^ 2 * |dimensionKernel 2 (k * σ)|) (Ioi 0) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs] using
    (TwoDLogMoments.integrable_scaled_power 2 hk).norm

/-- Unit-to-density scaling of an ABSOLUTE moment, not a replacement for the
signed logarithmic cancellations. The power is genuinely minus three. -/
theorem absolute_second_scaling {k : ℝ} (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, σ ^ 2 * |dimensionKernel 2 (k * σ)|) = absoluteSecondMoment / k ^ 3 := by
  have hs := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ 2 * |dimensionKernel 2 u|) 0 hk
  simp only [mul_zero, smul_eq_mul, mul_pow, mul_assoc, integral_const_mul] at hs
  apply (eq_div_iff (pow_ne_zero 3 hk.ne')).mpr
  calc
    _ = k * (k ^ 2 * (∫ σ : ℝ in Ioi 0, σ ^ 2 * |dimensionKernel 2 (k * σ)|)) := by ring
    _ = _ := by rw [hs]; unfold absoluteSecondMoment; field_simp

theorem integrable_of_bound (E : ℝ → ℝ) (hm : Measurable E) (C : ℝ)
    (hb : ∀ σ, 0 < σ → ‖E σ‖ ≤ C * σ ^ 2) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun σ : ℝ => E σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
  apply ((integrable_absolute_second hk).const_mul C).mono'
    (hm.mul ((continuous_dimensionKernel 2).measurable.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  dsimp only [Function.comp_apply]
  rw [norm_mul, Real.norm_eq_abs (dimensionKernel _ _)]
  exact (mul_le_mul_of_nonneg_right (hb σ hσ) (abs_nonneg _)).trans_eq (by ring)

/-- At normalization rho squared the absolute quadratic response is order
rho inverse. The bound may depend on the one fixed geometric cutoff. -/
theorem limit_of_bound (E : ℝ → ℝ) (hm : Measurable E) (C : ℝ)
    (hb : ∀ σ, 0 < σ → ‖E σ‖ ≤ C * σ ^ 2) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ 2 * ∫ σ : ℝ in Ioi 0, E σ * dimensionKernel 2 (c * ρ * σ))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun ρ : ℝ => (C * absoluteSecondMoment / c ^ 3) * ρ⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    have hk := mul_pos hc hρ
    have hi := integrable_of_bound E hm C hb hk
    have hbI : ‖∫ σ : ℝ in Ioi 0, E σ * dimensionKernel 2 (c * ρ * σ)‖ ≤
        C * (∫ σ : ℝ in Ioi 0, σ ^ 2 * |dimensionKernel 2 (c * ρ * σ)|) := by
      calc
        _ ≤ ∫ σ : ℝ in Ioi 0, ‖E σ * dimensionKernel 2 (c * ρ * σ)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ σ : ℝ in Ioi 0, C * (σ ^ 2 * |dimensionKernel 2 (c * ρ * σ)|) := by
          apply integral_mono_ae hi.norm ((integrable_absolute_second hk).const_mul C)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
          rw [norm_mul, Real.norm_eq_abs (dimensionKernel _ _)]
          exact (mul_le_mul_of_nonneg_right (hb σ hσ) (abs_nonneg _)).trans_eq (by ring)
        _ = _ := integral_const_mul _ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ)]
    apply (mul_le_mul_of_nonneg_left hbI (sq_nonneg ρ)).trans_eq
    rw [absolute_second_scaling hk]
    field_simp [hc.ne', hρ.ne']
    ring
  · simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (C * absoluteSecondMoment / c ^ 3)

end TwoDQuadraticResponse
end BoundaryDraft
