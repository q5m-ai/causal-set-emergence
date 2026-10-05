import BoundaryDraft.TwoDLogMoments

/-! # Actual signed logarithmic responses under positive 2D density scaling -/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft
namespace TwoDLogMoments

theorem integrable_scaled_power (n : ℕ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun σ : ℝ => σ ^ n * dimensionKernel 2 (k * σ)) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast] using integrableOn_dimensionKernel_scaled_rpow 2
    (q := 1) (j := n) (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hk

theorem scaled_power_zero (n : ℕ) (hn : n ≤ 1) {k : ℝ} (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, σ ^ n * dimensionKernel 2 (k * σ)) = 0 := by
  have hm := integral_dimensionKernel_transverse_zero 2 n (by norm_num)
    (show n < dimensionFactorCount 2 by norm_num [dimensionFactorCount]; omega)
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] at hm
  have hs := integral_dimensionKernel_scaled_rpow 2 1 n k hk
  simp only [Real.rpow_one, Real.rpow_natCast, hm, mul_zero] at hs
  exact hs

theorem integrable_scaled_log (n : ℕ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun σ : ℝ => σ ^ n * Real.log σ * dimensionKernel 2 (k * σ)) (Ioi 0) := by
  have hi : IntegrableOn (fun σ : ℝ => (k * σ) ^ n * Real.log (k * σ) * dimensionKernel 2 (k * σ)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => u ^ n * Real.log u * dimensionKernel 2 u) 0 hk).mpr
      (by simpa only [mul_zero] using integrable_log n)
  apply ((hi.const_mul ((k ^ n)⁻¹)).sub ((integrable_scaled_power n hk).const_mul (Real.log k))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  simp only [Pi.sub_apply, Real.log_mul hk.ne' hσ.ne', mul_pow]
  field_simp [hk.ne']
  ring

/-- Scaling retains the entire signed kernel. The logarithm of the density
scale cancels against a proved zero ordinary moment. -/
theorem scaled_log (n : ℕ) (hn : n ≤ 1) {k : ℝ} (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, σ ^ n * Real.log σ * dimensionKernel 2 (k * σ)) =
      (∫ u : ℝ in Ioi 0, u ^ n * Real.log u * dimensionKernel 2 u) / k ^ (n + 1) := by
  have hs := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ n * Real.log u * dimensionKernel 2 u) 0 hk
  simp only [mul_zero, smul_eq_mul] at hs
  have he : (∫ σ : ℝ in Ioi 0, (k * σ) ^ n * Real.log (k * σ) * dimensionKernel 2 (k * σ)) =
      k ^ n * (∫ σ : ℝ in Ioi 0, σ ^ n * Real.log σ * dimensionKernel 2 (k * σ)) := by
    calc
      _ = ∫ σ : ℝ in Ioi 0, k ^ n * (Real.log k * (σ ^ n * dimensionKernel 2 (k * σ)) +
          σ ^ n * Real.log σ * dimensionKernel 2 (k * σ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro σ hσ
        dsimp only
        rw [mul_pow, Real.log_mul hk.ne' hσ.ne']
        ring
      _ = _ := by
        rw [integral_const_mul, integral_add ((integrable_scaled_power n hk).const_mul _)
          (integrable_scaled_log n hk), integral_const_mul, scaled_power_zero n hn hk, mul_zero, zero_add]
  rw [he] at hs
  apply (eq_div_iff (pow_ne_zero (n + 1) hk.ne')).mpr
  rw [pow_succ]
  calc
    _ = k * (k ^ n * (∫ σ : ℝ in Ioi 0, σ ^ n * Real.log σ * dimensionKernel 2 (k * σ))) := by ring
    _ = _ := by rw [hs]; field_simp

/-- The volume sector cancels the point term after the physical coefficients
are inserted. This identity is exact at every positive scale. -/
theorem scaled_log_zero {k : ℝ} (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, Real.log σ * dimensionKernel 2 (k * σ)) = -(1 / (2 * k)) := by
  have hh := scaled_log 0 (by norm_num) hk
  simp only [pow_zero, one_mul, zero_add, pow_one, integral_log_zero] at hh
  rw [hh]
  field_simp

/-- Positive first logarithmic response, with the required inverse-square scale. -/
theorem scaled_log_one {k : ℝ} (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, σ * Real.log σ * dimensionKernel 2 (k * σ)) = 1 / (2 * k ^ 2) := by
  have hh := scaled_log 1 (by norm_num) hk
  simp only [pow_one, integral_log_one] at hh
  rw [hh]
  norm_num
  ring

end TwoDLogMoments
end BoundaryDraft
