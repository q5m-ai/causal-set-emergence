import BoundaryDraft.DimensionActionConstants
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Signed logarithmic moments of the ORIGINAL physical-dimension-two kernel

Absolute integrability is proved first. Integration by parts has explicit
vanishing endpoint products. The two signs are minus one-half and plus one-half;
no 3D or 4D logarithmic moment is used.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDLogMoments

theorem kernel_eq (u : ℝ) : dimensionKernel 2 u = (1 - 2 * u + u ^ 2 / 2) * Real.exp (-u) := by
  norm_num [dimensionKernel, dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    Polynomial.derivative_mul]
  ring

theorem integrable_rpow {j : ℝ} (hj : -1 < j) :
    IntegrableOn (fun u : ℝ => u ^ j * dimensionKernel 2 u) (Ioi 0) := by
  simpa only [Real.rpow_one] using integrableOn_dimensionKernel_rpow 2 (q := 1) (by norm_num) hj

private theorem abs_log_bound {u : ℝ} (hu : 0 < u) :
    |Real.log u| ≤ u + 2 * u ^ (-(1 / 2 : ℝ)) := by
  have hs := Real.neg_inv_le_log (Real.sqrt_nonneg u)
  rw [Real.log_sqrt hu.le] at hs
  rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have hn : 0 ≤ (Real.sqrt u)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg u)
  exact abs_le.mpr ⟨by linarith, by linarith [Real.log_le_self hu.le]⟩

/-- Covers both logarithmic orders and establishes absolute convergence first. -/
theorem integrable_log (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.log u * dimensionKernel 2 u) (Ioi 0) := by
  have hi₁ := (integrable_rpow (j := (n : ℝ) + 1) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm
  have hi₂ := ((integrable_rpow (j := (n : ℝ) - 1 / 2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).norm).const_mul 2
  have hm : Measurable (fun u : ℝ => u ^ n * Real.log u * dimensionKernel 2 u) :=
    ((measurable_id.pow_const n).mul Real.measurable_log).mul (continuous_dimensionKernel 2).measurable
  apply (hi₁.add hi₂).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := hu.le
  have hun : 0 ≤ u ^ n := pow_nonneg hu0 n
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hun,
    abs_of_nonneg (Real.rpow_nonneg hu0 _)]
  calc
    _ ≤ (u ^ n * (u + 2 * u ^ (-(1 / 2 : ℝ)))) * |dimensionKernel 2 u| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_log_bound hu) (pow_nonneg hu.le n)) (abs_nonneg _)
    _ = _ := by
      rw [← Real.rpow_natCast, Real.rpow_add hu, Real.rpow_one,
        show (n : ℝ) - 1 / 2 = (n : ℝ) + (-(1 / 2 : ℝ)) by ring, Real.rpow_add hu]
      ring

private theorem integrable_pow_exp (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-u)) (Ioi 0) := by
  simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using
    Real.GammaIntegral_convergent (show 0 < (n : ℝ) + 1 by positivity)

private theorem integral_pow_exp (n : ℕ) :
    (∫ u : ℝ in Ioi 0, u ^ n * Real.exp (-u)) = n.factorial := by
  have hh := Real.Gamma_eq_integral (show 0 < (n : ℝ) + 1 by positivity)
  rw [Real.Gamma_nat_eq_factorial] at hh
  simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using hh.symm

private def primitive (n : ℕ) (a b u : ℝ) : ℝ :=
  u ^ (n + 1) * (a + b * u) * Real.exp (-u)

private theorem primitive_div (n : ℕ) (a b u : ℝ) (hu : u ≠ 0) :
    u⁻¹ * primitive n a b u =
      a * (u ^ n * Real.exp (-u)) + b * (u ^ (n + 1) * Real.exp (-u)) := by
  unfold primitive
  rw [pow_succ]
  field_simp [hu]
  ring

private theorem primitive_log_zero (n : ℕ) (a b : ℝ) :
    Tendsto (fun u => Real.log u * primitive n a b u) (𝓝[>] 0) (𝓝 0) := by
  have he : (fun u => Real.log u * primitive n a b u) =
      (fun u => (u * Real.log u) * u ^ n * (a + b * u) * Real.exp (-u)) := by
    funext u
    unfold primitive
    rw [pow_succ]
    ring
  rw [he]
  have hc : Continuous (fun u : ℝ => (u * Real.log u) * u ^ n * (a + b * u) * Real.exp (-u)) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

private theorem log_pow_exp_atTop (n : ℕ) :
    Tendsto (fun u : ℝ => u ^ n * Real.log u * Real.exp (-u)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n + 1))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u := by linarith
    exact mul_nonneg (mul_nonneg (pow_nonneg hu0 n) (Real.log_nonneg hu)) (Real.exp_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u := by linarith
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_self hu0) (pow_nonneg hu0 n)) (Real.exp_nonneg _)

private theorem primitive_log_atTop (n : ℕ) (a b : ℝ) :
    Tendsto (fun u => Real.log u * primitive n a b u) atTop (𝓝 0) := by
  have hh := ((log_pow_exp_atTop (n + 1)).const_mul a).add ((log_pow_exp_atTop (n + 2)).const_mul b)
  convert hh using 1
  · funext u
    unfold primitive
    simp only [pow_add]
    ring
  · simp

private theorem integral_log_from_primitive (n : ℕ) (a b : ℝ)
    (hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (primitive n a b) (u ^ n * dimensionKernel 2 u) u) :
    (∫ u : ℝ in Ioi 0, u ^ n * Real.log u * dimensionKernel 2 u) =
      -(a * n.factorial + b * (n + 1).factorial) := by
  have hi := ((integrable_pow_exp n).const_mul a).add ((integrable_pow_exp (n + 1)).const_mul b)
  have hid : IntegrableOn (fun u => u⁻¹ * primitive n a b u) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (primitive_div n a b u hu.ne').symm
  have hil : IntegrableOn (fun u => Real.log u * (u ^ n * dimensionKernel 2 u)) (Ioi 0) := by
    simpa only [mul_left_comm, mul_assoc, mul_comm] using integrable_log n
  have hp := integral_Ioi_mul_deriv_eq_deriv_mul (fun u hu => Real.hasDerivAt_log hu.ne') hd hil hid
    (primitive_log_zero n a b) (primitive_log_atTop n a b)
  have heval : (∫ u : ℝ in Ioi 0, u⁻¹ * primitive n a b u) = a * n.factorial + b * (n + 1).factorial := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => primitive_div n a b u hu.ne'),
      integral_add ((integrable_pow_exp n).const_mul a) ((integrable_pow_exp (n + 1)).const_mul b),
      integral_const_mul, integral_const_mul, integral_pow_exp, integral_pow_exp]
  rw [heval] at hp
  simpa only [zero_sub, sub_zero, mul_left_comm, mul_assoc] using hp

/-- The volume-log sector has the negative signed logarithmic moment. -/
theorem integral_log_zero :
    (∫ u : ℝ in Ioi 0, Real.log u * dimensionKernel 2 u) = -(1 / 2 : ℝ) := by
  have hd (u : ℝ) : HasDerivAt (primitive 0 1 (-(1 / 2))) (u ^ 0 * dimensionKernel 2 u) u := by
    convert (((hasDerivAt_pow 1 u).mul
      ((hasDerivAt_const u 1).add ((hasDerivAt_id u).const_mul (-(1 / 2))))).mul
        ((hasDerivAt_id u).neg.exp)) using 1
    simp only [primitive, kernel_eq, id_eq]
    ring
  have hh := integral_log_from_primitive 0 1 (-(1 / 2)) (fun u _ => hd u)
  norm_num at hh ⊢
  exact hh

/-- The endpoint-log sector has the positive signed logarithmic moment. -/
theorem integral_log_one :
    (∫ u : ℝ in Ioi 0, u * Real.log u * dimensionKernel 2 u) = (1 / 2 : ℝ) := by
  have hd (u : ℝ) : HasDerivAt (primitive 1 (1 / 2) (-(1 / 2))) (u ^ 1 * dimensionKernel 2 u) u := by
    convert (((hasDerivAt_pow 2 u).mul
      ((hasDerivAt_const u (1 / 2)).add ((hasDerivAt_id u).const_mul (-(1 / 2))))).mul
        ((hasDerivAt_id u).neg.exp)) using 1
    simp only [primitive, kernel_eq, id_eq]
    ring
  have hh := integral_log_from_primitive 1 (1 / 2) (-(1 / 2)) (fun u _ => hd u)
  norm_num at hh ⊢
  exact hh

end TwoDLogMoments
end BoundaryDraft
