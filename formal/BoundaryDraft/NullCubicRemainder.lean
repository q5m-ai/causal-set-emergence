import BoundaryDraft.NullTransverseCancellation

/-!
# Normalized decay of a globally cubic proper-time remainder

Polynomial/logarithmic short models need not be bounded after their Taylor
polynomial is subtracted. A global cubic bound suffices, using the finite third
absolute signed-kernel moment. This also controls fixed-cutoff tails without
claiming uniformity as the cutoff shrinks.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Exact positive rescaling of the third absolute moment. -/
theorem integral_bdgKernel_scaled_abs_three {k : ℝ} (hk : 0 < k) :
    (∫ s : ℝ in Ioi 0, s ^ 3 * |bdgKernel ((k * s) ^ 2)|) =
      k⁻¹ ^ 4 * ∫ z : ℝ in Ioi 0, z ^ 3 * |bdgKernel (z ^ 2)| := by
  have hs := integral_comp_mul_left_Ioi
    (fun z : ℝ => (k⁻¹ * z) ^ 3 * |bdgKernel (z ^ 2)|) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  rw [hs]
  simp_rw [mul_pow, mul_assoc]
  rw [integral_const_mul]
  ring

/-- Integrability of the absolute moment at every positive scale. -/
theorem integrableOn_bdgKernel_scaled_abs_three {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => s ^ 3 * |bdgKernel ((k * s) ^ 2)|) (Ioi 0) := by
  apply (integrableOn_bdgKernel_transverse_scaled_moment 3 k hk).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hs 3)]

/-- A cubic envelope establishes integrability before any signed subtraction. -/
theorem integrableOn_bdgKernel_mul_cubic_bound (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C * s ^ 3)
    {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s => B s * bdgKernel (c * ρ * s ^ 2)) (Ioi 0) := by
  let k := Real.sqrt (c * ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have he (s : ℝ) : c * ρ * s ^ 2 = (k * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he]
  apply ((integrableOn_bdgKernel_scaled_abs_three hk).const_mul C).mono'
    (hB.mul (by unfold bdgKernel bdgPolynomial; fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [norm_mul, Real.norm_eq_abs (bdgKernel ((k * s) ^ 2))]
  exact (mul_le_mul_of_nonneg_right (hbound s hs) (abs_nonneg _)).trans_eq (by ring)

/-- The physical density normalization leaves one vanishing inverse-square-root
width. The constant may depend on the fixed cutoff used to derive `hbound`. -/
theorem bdgKernel_normalized_cubic_bound (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C * s ^ 3)
    {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ‖Real.sqrt ρ * ρ * ∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)‖ ≤
      (C * (Real.sqrt c)⁻¹ ^ 3 *
        ∫ z : ℝ in Ioi 0, z ^ 3 * |bdgKernel (z ^ 2)|) * (Real.sqrt (c * ρ))⁻¹ := by
  let k := Real.sqrt (c * ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have he (s : ℝ) : c * ρ * s ^ 2 = (k * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  have hi := integrableOn_bdgKernel_mul_cubic_bound B hB C hbound hc hρ
  have hen := (integrableOn_bdgKernel_scaled_abs_three hk).const_mul C
  have hnorm : ‖∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)‖ ≤
      C * k⁻¹ ^ 4 * ∫ z : ℝ in Ioi 0, z ^ 3 * |bdgKernel (z ^ 2)| := by
    calc
      _ ≤ ∫ s : ℝ in Ioi 0, ‖B s * bdgKernel (c * ρ * s ^ 2)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ in Ioi 0, C * (s ^ 3 * |bdgKernel ((k * s) ^ 2)|) := by
        apply integral_mono_ae hi.norm hen
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [norm_mul, Real.norm_eq_abs (bdgKernel _), he]
        exact (mul_le_mul_of_nonneg_right (hbound s hs) (abs_nonneg _)).trans_eq (by ring)
      _ = _ := by rw [integral_const_mul, integral_bdgKernel_scaled_abs_three hk]; ring
  rw [norm_mul, norm_mul, Real.norm_eq_abs (Real.sqrt ρ), Real.norm_eq_abs ρ,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hρ]
  apply (mul_le_mul_of_nonneg_left hnorm (mul_nonneg (Real.sqrt_nonneg _) hρ.le)).trans_eq
  have hsp : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hr : Real.sqrt ρ * ρ = Real.sqrt ρ ^ 3 := by
    nlinarith only [congrArg (fun t : ℝ => Real.sqrt ρ * t) (Real.sq_sqrt hρ.le)]
  dsimp only [k]
  rw [Real.sqrt_mul hc.le, hr]
  field_simp [hsp.ne', hsc.ne']
  ring

/-- Global cubic control implies normalized signed decay, with all density
powers retained. -/
theorem bdgKernel_cubic_cancellation (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ s, 0 < s → ‖B s‖ ≤ C * s ^ 3)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ *
      ∫ s : ℝ in Ioi 0, B s * bdgKernel (c * ρ * s ^ 2)) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact bdgKernel_normalized_cubic_bound B hB C hbound hc hρ
  · simpa only [mul_zero] using
      ((tendsto_bdgKernel_transverse_width c hc).mono_right nhdsWithin_le_nhds).const_mul
        (C * (Real.sqrt c)⁻¹ ^ 3 * ∫ z : ℝ in Ioi 0, z ^ 3 * |bdgKernel (z ^ 2)|)

end BoundaryDraft
