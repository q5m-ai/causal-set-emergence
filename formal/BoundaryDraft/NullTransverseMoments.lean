import BoundaryDraft.Specification
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Signed transverse moments of the original BDG kernel

These are moments of `bdgKernel (z^2)`, not the mass-one reduced `planeKernel`.
Absolute integrability is proved before splitting the signed polynomial. The
Gamma recurrence gives three zero moments and the nonzero third moment.
No geometric localization or regularity of an overlap density is asserted.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

theorem integrableOn_pow_mul_gaussian (n : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ n * Real.exp (-(z ^ 2))) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n) : (-1 : ℝ) < (n : ℝ))

theorem integral_pow_mul_gaussian (n : ℕ) :
    (∫ z : ℝ in Ioi 0, z ^ n * Real.exp (-(z ^ 2))) =
      Real.Gamma (((n : ℝ) + 1) / 2) / 2 := by
  have hg := Real.Gamma_eq_integral (by positivity : 0 < ((n : ℝ) + 1) / 2)
  rw [← integral_comp_rpow_Ioi_of_pos (by norm_num : (0 : ℝ) < 2)] at hg
  have he : (∫ z : ℝ in Ioi 0,
      (2 * z ^ ((2 : ℝ) - 1)) •
        (Real.exp (-(z ^ (2 : ℝ))) * (z ^ (2 : ℝ)) ^ (((n : ℝ) + 1) / 2 - 1))) =
      2 * ∫ z : ℝ in Ioi 0, z ^ n * Real.exp (-(z ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    dsimp only
    rw [smul_eq_mul, ← Real.rpow_mul hz.le]
    have hp : 2 * (((n : ℝ) + 1) / 2 - 1) = (n : ℝ) - 1 := by ring
    rw [hp]
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [Real.rpow_sub_one hz.ne', Real.rpow_natCast, Real.rpow_two]
    field_simp [ne_of_gt (show 0 < z from hz)]
    ring
  rw [he] at hg
  linarith

private theorem transverse_moment_expand (n : ℕ) (z : ℝ) :
    z ^ n * bdgKernel (z ^ 2) =
      z ^ n * Real.exp (-(z ^ 2)) - 9 * (z ^ (n + 2) * Real.exp (-(z ^ 2))) +
        8 * (z ^ (n + 4) * Real.exp (-(z ^ 2))) -
          (4 / 3) * (z ^ (n + 6) * Real.exp (-(z ^ 2))) := by
  unfold bdgKernel bdgPolynomial
  ring

/-- All natural-order transverse moments are absolutely integrable. -/
theorem integrableOn_bdgKernel_transverse_moment (n : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ n * bdgKernel (z ^ 2)) (Ioi 0) := by
  simp_rw [transverse_moment_expand]
  exact (((integrableOn_pow_mul_gaussian n).sub
    ((integrableOn_pow_mul_gaussian (n + 2)).const_mul 9)).add
      ((integrableOn_pow_mul_gaussian (n + 4)).const_mul 8)).sub
        ((integrableOn_pow_mul_gaussian (n + 6)).const_mul (4 / 3))

/-- Explicit absolute integrability of the domination used in cancellation. -/
theorem integrableOn_abs_bdgKernel_transverse_moment (n : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ n * |bdgKernel (z ^ 2)|) (Ioi 0) := by
  apply (integrableOn_bdgKernel_transverse_moment n).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hz.le _)]

/-- The concrete coefficients give the factor `-n(n-1)(n-2)/12`.
The subtractions in this formula are real, not truncated natural subtraction. -/
theorem integral_bdgKernel_transverse_moment (n : ℕ) :
    (∫ z : ℝ in Ioi 0, z ^ n * bdgKernel (z ^ 2)) =
      -((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) / 12 *
        Real.Gamma (((n : ℝ) + 1) / 2) := by
  simp_rw [transverse_moment_expand]
  have hi2 : IntegrableOn (fun z : ℝ => z ^ n * Real.exp (-(z ^ 2)) -
      9 * (z ^ (n + 2) * Real.exp (-(z ^ 2)))) (Ioi 0) :=
    (integrableOn_pow_mul_gaussian n).sub ((integrableOn_pow_mul_gaussian (n + 2)).const_mul 9)
  have hi4 : IntegrableOn (fun z : ℝ => z ^ n * Real.exp (-(z ^ 2)) -
      9 * (z ^ (n + 2) * Real.exp (-(z ^ 2))) +
        8 * (z ^ (n + 4) * Real.exp (-(z ^ 2)))) (Ioi 0) :=
    hi2.add ((integrableOn_pow_mul_gaussian (n + 4)).const_mul 8)
  rw [integral_sub hi4 ((integrableOn_pow_mul_gaussian (n + 6)).const_mul (4 / 3)),
    integral_add hi2 ((integrableOn_pow_mul_gaussian (n + 4)).const_mul 8),
    integral_sub (integrableOn_pow_mul_gaussian n)
      ((integrableOn_pow_mul_gaussian (n + 2)).const_mul 9)]
  simp_rw [integral_const_mul, integral_pow_mul_gaussian]
  let a : ℝ := ((n : ℝ) + 1) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have h2 : ((↑(n + 2) : ℝ) + 1) / 2 = a + 1 := by dsimp [a]; push_cast; ring
  have h4 : ((↑(n + 4) : ℝ) + 1) / 2 = (a + 1) + 1 := by dsimp [a]; push_cast; ring
  have h6 : ((↑(n + 6) : ℝ) + 1) / 2 = ((a + 1) + 1) + 1 := by
    dsimp [a]; push_cast; ring
  rw [h2, h4, h6, Real.Gamma_add_one (by positivity : (a + 1) + 1 ≠ 0),
    Real.Gamma_add_one (by positivity : a + 1 ≠ 0), Real.Gamma_add_one ha.ne']
  dsimp [a]
  ring

theorem integral_bdgKernel_transverse_zero :
    (∫ z : ℝ in Ioi 0, bdgKernel (z ^ 2)) = 0 := by
  simpa using integral_bdgKernel_transverse_moment 0

theorem integral_bdgKernel_transverse_one :
    (∫ z : ℝ in Ioi 0, z * bdgKernel (z ^ 2)) = 0 := by
  simpa using integral_bdgKernel_transverse_moment 1

theorem integral_bdgKernel_transverse_two :
    (∫ z : ℝ in Ioi 0, z ^ 2 * bdgKernel (z ^ 2)) = 0 := by
  simpa using integral_bdgKernel_transverse_moment 2

/-- Sign/coefficient regression: cancellation stops at order three. -/
theorem integral_bdgKernel_transverse_three :
    (∫ z : ℝ in Ioi 0, z ^ 3 * bdgKernel (z ^ 2)) = -(1 / 2) := by
  convert integral_bdgKernel_transverse_moment 3 using 1
  norm_num

end BoundaryDraft
