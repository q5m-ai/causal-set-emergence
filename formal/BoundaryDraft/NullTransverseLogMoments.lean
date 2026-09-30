import BoundaryDraft.NullTransverseMoments
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Signed logarithmic transverse moments of the original BDG kernel

Absolute integrability precedes integration by parts with explicit polynomial
Gaussian primitives. Both endpoint products vanish; the remaining integrals
are ordinary Gaussian moments. These identities are analytic components, not
short-displacement asymptotics or a general two-face limit.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft

private theorem abs_mul_log_le {z : ℝ} (hz : 0 < z) :
    |z * Real.log z| ≤ 1 + z ^ 2 := by
  have hlo : -1 ≤ z * Real.log z := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log hz.le) hz.le
    simpa [mul_neg, mul_inv_cancel₀ hz.ne'] using h
  have hhi : z * Real.log z ≤ z ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left (Real.log_le_self hz.le) hz.le
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg z], by linarith⟩

private theorem integrableOn_transverse_log (n : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ (n + 1) * Real.log z * bdgKernel (z ^ 2))
      (Ioi 0) := by
  have hK : Continuous (fun z : ℝ => bdgKernel (z ^ 2)) := by
    unfold bdgKernel bdgPolynomial
    fun_prop
  refine ((integrableOn_abs_bdgKernel_transverse_moment n).add
    (integrableOn_abs_bdgKernel_transverse_moment (n + 2))).mono'
      (((measurable_id.pow_const (n + 1)).mul Real.measurable_log).mul
        hK.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  calc
    ‖z ^ (n + 1) * Real.log z * bdgKernel (z ^ 2)‖ =
        z ^ n * |z * Real.log z| * |bdgKernel (z ^ 2)| := by
      rw [show z ^ (n + 1) * Real.log z * bdgKernel (z ^ 2) =
        z ^ n * (z * Real.log z) * bdgKernel (z ^ 2) by ring]
      simp only [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg (show 0 ≤ z from hz.le) n)]
    _ ≤ z ^ n * (1 + z ^ 2) * |bdgKernel (z ^ 2)| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_mul_log_le hz) (pow_nonneg hz.le n)) (abs_nonneg _)
    _ = z ^ n * |bdgKernel (z ^ 2)| + z ^ (n + 2) * |bdgKernel (z ^ 2)| := by ring

/-- Absolute integrability of the first signed logarithmic transverse moment. -/
theorem integrableOn_bdgKernel_transverse_log_one :
    IntegrableOn (fun z : ℝ => z * Real.log z * bdgKernel (z ^ 2)) (Ioi 0) := by
  simpa using integrableOn_transverse_log 0

/-- Absolute integrability of the second signed logarithmic transverse moment. -/
theorem integrableOn_bdgKernel_transverse_log_two :
    IntegrableOn (fun z : ℝ => z ^ 2 * Real.log z * bdgKernel (z ^ 2)) (Ioi 0) := by
  simpa using integrableOn_transverse_log 1

private theorem tendsto_pow_gaussian_atTop (n : ℕ) :
    Tendsto (fun z : ℝ => z ^ n * Real.exp (-(z ^ 2))) atTop (𝓝 0) := by
  have he : Tendsto (fun z : ℝ => Real.exp (-(1 / 2) * z)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
  simpa using (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1)
    (n : ℝ)).trans_tendsto he

private theorem tendsto_log_pow_gaussian_atTop (n : ℕ) :
    Tendsto (fun z : ℝ => z ^ n * Real.log z * Real.exp (-(z ^ 2))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_pow_gaussian_atTop (n + 1))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have hz0 : 0 ≤ z := by linarith
    exact mul_nonneg (mul_nonneg (pow_nonneg hz0 n) (Real.log_nonneg hz))
      (Real.exp_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    have hz0 : 0 ≤ z := by linarith
    change z ^ n * Real.log z * Real.exp (-(z ^ 2)) ≤
      z ^ (n + 1) * Real.exp (-(z ^ 2))
    rw [pow_succ z n]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_self hz0) (pow_nonneg hz0 n))
      (Real.exp_nonneg (-(z ^ 2)))

/-- The parameter `n` corresponds to transverse moment order `n + 1`. -/
private def logMomentPrimitive (n : ℕ) (a b z : ℝ) : ℝ :=
  z ^ (n + 2) * (a + b * z ^ 2 + (2 / 3) * z ^ 4) * Real.exp (-(z ^ 2))

private theorem logMomentPrimitive_div (n : ℕ) (a b z : ℝ) (hz : z ≠ 0) :
    z⁻¹ * logMomentPrimitive n a b z =
      a * (z ^ (n + 1) * Real.exp (-(z ^ 2))) +
        b * (z ^ (n + 3) * Real.exp (-(z ^ 2))) +
          (2 / 3) * (z ^ (n + 5) * Real.exp (-(z ^ 2))) := by
  simp only [logMomentPrimitive, pow_add]
  field_simp [hz]
  ring

private theorem logMomentPrimitive_zero (n : ℕ) (a b : ℝ) :
    Tendsto (fun z => Real.log z * logMomentPrimitive n a b z) (𝓝[>] 0) (𝓝 0) := by
  have heq : (fun z => Real.log z * logMomentPrimitive n a b z) =
      (fun z => (z * Real.log z) * z ^ (n + 1) *
        (a + b * z ^ 2 + (2 / 3) * z ^ 4) * Real.exp (-(z ^ 2))) := by
    funext z
    dsimp [logMomentPrimitive]
    ring
  rw [heq]
  have hc : Continuous (fun z : ℝ => (z * Real.log z) * z ^ (n + 1) *
      (a + b * z ^ 2 + (2 / 3) * z ^ 4) * Real.exp (-(z ^ 2))) := by
    fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

private theorem logMomentPrimitive_atTop (n : ℕ) (a b : ℝ) :
    Tendsto (fun z => Real.log z * logMomentPrimitive n a b z) atTop (𝓝 0) := by
  have h := (((tendsto_log_pow_gaussian_atTop (n + 2)).const_mul a).add
    ((tendsto_log_pow_gaussian_atTop (n + 4)).const_mul b)).add
      ((tendsto_log_pow_gaussian_atTop (n + 6)).const_mul (2 / 3))
  convert h using 1
  · funext z
    dsimp [logMomentPrimitive]
    ring
  · simp

private theorem integral_transverse_log_eq (n : ℕ) (a b : ℝ)
    (hd : ∀ z ∈ Ioi (0 : ℝ), HasDerivAt (logMomentPrimitive n a b)
      (z ^ (n + 1) * bdgKernel (z ^ 2)) z) :
    (∫ z : ℝ in Ioi 0, z ^ (n + 1) * Real.log z * bdgKernel (z ^ 2)) =
      -(a * (Real.Gamma (((n : ℝ) + 2) / 2) / 2) +
        b * (Real.Gamma (((n : ℝ) + 4) / 2) / 2) +
          (2 / 3) * (Real.Gamma (((n : ℝ) + 6) / 2) / 2)) := by
  have hi := (((integrableOn_pow_mul_gaussian (n + 1)).const_mul a).add
    ((integrableOn_pow_mul_gaussian (n + 3)).const_mul b)).add
      ((integrableOn_pow_mul_gaussian (n + 5)).const_mul (2 / 3))
  have hi' : IntegrableOn (fun z => z⁻¹ * logMomentPrimitive n a b z) (Ioi 0) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (logMomentPrimitive_div n a b z hz.ne').symm
  have hlog : IntegrableOn
      (fun z => Real.log z * (z ^ (n + 1) * bdgKernel (z ^ 2))) (Ioi 0) := by
    convert integrableOn_transverse_log n using 1
    funext z
    ring
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun z hz => Real.hasDerivAt_log (ne_of_gt hz)) hd hlog hi'
    (logMomentPrimitive_zero n a b) (logMomentPrimitive_atTop n a b)
  have heval : (∫ z : ℝ in Ioi 0, z⁻¹ * logMomentPrimitive n a b z) =
      a * (Real.Gamma (((n : ℝ) + 2) / 2) / 2) +
        b * (Real.Gamma (((n : ℝ) + 4) / 2) / 2) +
          (2 / 3) * (Real.Gamma (((n : ℝ) + 6) / 2) / 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun z hz => logMomentPrimitive_div n a b z hz.ne')]
    have hi13 : IntegrableOn (fun z : ℝ =>
        a * (z ^ (n + 1) * Real.exp (-(z ^ 2))) +
          b * (z ^ (n + 3) * Real.exp (-(z ^ 2)))) (Ioi 0) :=
      ((integrableOn_pow_mul_gaussian (n + 1)).const_mul a).add
        ((integrableOn_pow_mul_gaussian (n + 3)).const_mul b)
    rw [integral_add hi13 ((integrableOn_pow_mul_gaussian (n + 5)).const_mul (2 / 3)),
      integral_add ((integrableOn_pow_mul_gaussian (n + 1)).const_mul a)
        ((integrableOn_pow_mul_gaussian (n + 3)).const_mul b)]
    simp only [integral_const_mul, integral_pow_mul_gaussian, Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [heval] at hibp
  simpa only [zero_sub, sub_zero, mul_left_comm, mul_assoc] using hibp

/-- Exact signed first logarithmic moment of the original kernel. -/
theorem integral_bdgKernel_transverse_log_one :
    (∫ z : ℝ in Ioi 0, z * Real.log z * bdgKernel (z ^ 2)) = 1 / 12 := by
  have hd (z : ℝ) : HasDerivAt (logMomentPrimitive 0 (1 / 2) (-2))
      (z * bdgKernel (z ^ 2)) z := by
    convert ((hasDerivAt_pow 2 z).mul
      (((hasDerivAt_const z (1 / 2)).add ((hasDerivAt_pow 2 z).const_mul (-2))).add
        ((hasDerivAt_pow 4 z).const_mul (2 / 3)))).mul
          ((hasDerivAt_pow 2 z).neg.exp) using 1
    dsimp [logMomentPrimitive, bdgKernel, bdgPolynomial]
    ring
  have h := integral_transverse_log_eq 0 (1 / 2) (-2) (fun z _ => by simpa using hd z)
  norm_num at h
  exact h

/-- Exact signed second logarithmic moment; its sign is negative. -/
theorem integral_bdgKernel_transverse_log_two :
    (∫ z : ℝ in Ioi 0, z ^ 2 * Real.log z * bdgKernel (z ^ 2)) =
      -Real.sqrt Real.pi / 12 := by
  have hd (z : ℝ) : HasDerivAt (logMomentPrimitive 1 (1 / 3) (-5 / 3))
      (z ^ 2 * bdgKernel (z ^ 2)) z := by
    convert ((hasDerivAt_pow 3 z).mul
      (((hasDerivAt_const z (1 / 3)).add ((hasDerivAt_pow 2 z).const_mul (-5 / 3))).add
        ((hasDerivAt_pow 4 z).const_mul (2 / 3)))).mul
          ((hasDerivAt_pow 2 z).neg.exp) using 1
    dsimp [logMomentPrimitive, bdgKernel, bdgPolynomial]
    ring
  have h := integral_transverse_log_eq 1 (1 / 3) (-5 / 3) (fun z _ => by simpa using hd z)
  have hg3 := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hg5 := Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)
  have hg7 := Real.Gamma_add_one (by norm_num : (5 / 2 : ℝ) ≠ 0)
  norm_num [Real.Gamma_one_half_eq] at hg3 hg5 hg7
  norm_num at h
  rw [hg7, hg5, hg3] at h
  convert h using 1
  ring

end BoundaryDraft
