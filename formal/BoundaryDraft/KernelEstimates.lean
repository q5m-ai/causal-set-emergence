import BoundaryDraft.KernelDerivatives
import BoundaryDraft.GaussianCancellation

/-!
# Absolute bounds for the concrete plane kernel

Apply `t = 1 - v²` to the already justified derivatives. Two exact Gaussian
cancellations give `|F''(u)| ≤ 2832/u³` and `|uF'(u)-F(u)| ≤ 240/u`.
These estimates use neither an assumed asymptotic expansion nor positivity of G.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

namespace BoundaryDraft

/-- A square-root integral on a fixed interval for the auxiliary function. -/
theorem planeAuxiliary_eq_sqrt_integral (u : ℝ) :
    planeAuxiliary 1 u = 2 * Real.pi * u ^ 3 *
      ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) * Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2) := by
  have h := planeAuxiliary_scaling 1 u 1
  simp only [mul_one, one_mul] at h
  rw [h, planeAuxiliary]
  simp only [one_pow]
  rw [integral_sq_comp_one_sub_sq
    (fun t => Real.exp (-(Real.pi / 24) * u ^ 4 * t ^ 2)) (by fun_prop)]
  have he : -(Real.pi / 24) * u ^ 4 = -(Real.pi / 24 * u ^ 4) := by ring
  simp_rw [he]
  ring

/-- The first derivative in the same coordinates; differentiation was already
proved on the original fixed radial interval. -/
theorem planeAuxiliaryFirst_eq_sqrt_integral (u : ℝ) :
    planeAuxiliaryFirst 1 u = 2 * Real.pi * u ^ 2 *
      ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) *
        (3 - 4 * (Real.pi / 24 * u ^ 4) * t ^ 2) *
          Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2) := by
  change 4 * Real.pi * (∫ v in (0 : ℝ)..1,
    v ^ 2 * (3 * u ^ 2 + 4 * (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 6) *
      Real.exp ((-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 4)) = _
  have he (v : ℝ) :
      v ^ 2 * (3 * u ^ 2 + 4 * (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 6) *
        Real.exp ((-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 4) =
      u ^ 2 * (v ^ 2 * ((3 - 4 * (Real.pi / 24 * u ^ 4) * (1 - v ^ 2) ^ 2) *
        Real.exp (-(Real.pi / 24 * u ^ 4) * (1 - v ^ 2) ^ 2))) := by
    rw [show (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 4 =
      -(Real.pi / 24 * u ^ 4) * (1 - v ^ 2) ^ 2 by ring]
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [integral_sq_comp_one_sub_sq
    (fun t => (3 - 4 * (Real.pi / 24 * u ^ 4) * t ^ 2) *
      Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2)) (by fun_prop)]
  simp_rw [mul_assoc]
  ring

/-- The second derivative, with its leading Gaussian cancellation explicit. -/
theorem planeAuxiliarySecond_eq_sqrt_integral (u : ℝ) :
    planeAuxiliarySecond 1 u = 2 * Real.pi * u *
      ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) *
        gaussianCancellationPolynomial 6 8 (Real.pi / 24 * u ^ 4) t *
          Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2) := by
  change 4 * Real.pi * (∫ v in (0 : ℝ)..1,
    v ^ 2 * (6 * u + 36 * (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 5 +
      16 * (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) ^ 2 * u ^ 9) *
      Real.exp ((-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 4)) = _
  have he (v : ℝ) :
      v ^ 2 * (6 * u + 36 * (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 5 +
        16 * (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) ^ 2 * u ^ 9) *
        Real.exp ((-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 4) =
      u * (v ^ 2 * (gaussianCancellationPolynomial 6 8 (Real.pi / 24 * u ^ 4) (1 - v ^ 2) *
        Real.exp (-(Real.pi / 24 * u ^ 4) * (1 - v ^ 2) ^ 2))) := by
    rw [show (-(Real.pi / 24) * 1 * (1 - v ^ 2) ^ 2) * u ^ 4 =
      -(Real.pi / 24 * u ^ 4) * (1 - v ^ 2) ^ 2 by ring]
    unfold gaussianCancellationPolynomial
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [integral_sq_comp_one_sub_sq
    (fun t => gaussianCancellationPolynomial 6 8 (Real.pi / 24 * u ^ 4) t *
      Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2))
    (by unfold gaussianCancellationPolynomial; fun_prop)]
  simp_rw [mul_assoc]
  ring

/-- A cancellation for the finite signed first moment. -/
theorem mul_planeAuxiliaryFirst_sub_eq (u : ℝ) :
    u * planeAuxiliaryFirst 1 u - planeAuxiliary 1 u = 2 * Real.pi * u ^ 3 *
      ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) *
        gaussianCancellationPolynomial 2 0 (Real.pi / 24 * u ^ 4) t *
          Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2) := by
  rw [planeAuxiliaryFirst_eq_sqrt_integral, planeAuxiliary_eq_sqrt_integral]
  have hm (x : ℝ) : u * (2 * Real.pi * u ^ 2 * x) = 2 * Real.pi * u ^ 3 * x := by ring
  rw [hm, ← mul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub
    (show IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t) *
      (3 - 4 * (Real.pi / 24 * u ^ 4) * t ^ 2) *
        Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2)) volume 0 1 from
          (by fun_prop : Continuous _).intervalIntegrable 0 1)
    (show IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t) *
      Real.exp (-(Real.pi / 24 * u ^ 4) * t ^ 2)) volume 0 1 from
        (by fun_prop : Continuous _).intervalIntegrable 0 1)]
  congr 1
  funext t
  unfold gaussianCancellationPolynomial
  ring

/-- Absolute decay of the second derivative, valid at every positive height. -/
theorem abs_planeAuxiliarySecond_le {u : ℝ} (hu : 0 < u) :
    |planeAuxiliarySecond 1 u| ≤ 2832 / u ^ 3 := by
  rw [planeAuxiliarySecond_eq_sqrt_integral, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * u)]
  have h := gaussianCancellation_bound (Real.pi / 24 * u ^ 4) 6 8
    (by positivity) (by norm_num) (by norm_num)
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi * u)).trans_eq
  field_simp
  ring

/-- This controls the boundary term in the signed first-moment identity. -/
theorem abs_mul_planeAuxiliaryFirst_sub_le {u : ℝ} (hu : 0 < u) :
    |u * planeAuxiliaryFirst 1 u - planeAuxiliary 1 u| ≤ 240 / u := by
  rw [mul_planeAuxiliaryFirst_sub_eq, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * u ^ 3)]
  have h := gaussianCancellation_bound (Real.pi / 24 * u ^ 4) 2 0
    (by positivity) (by norm_num) (by norm_num)
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * Real.pi * u ^ 3)).trans_eq
  field_simp
  ring

/-- An explicit bound for the signed kernel; it bounds its absolute value. -/
theorem abs_planeKernel_le {u : ℝ} (hu : 0 < u) :
    |planeKernel 1 u| ≤ (1416 / (Real.pi * Real.sqrt 6)) / u ^ 3 := by
  rw [planeKernel_eq_second, Real.sqrt_one, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi * Real.sqrt 6))]
  apply (mul_le_mul_of_nonneg_left (abs_planeAuxiliarySecond_le hu)
    (by positivity : 0 ≤ 1 / (2 * Real.pi * Real.sqrt 6))).trans_eq
  ring

/-- The unchanged concrete tail target, with explicit constants. -/
theorem kernelTailGoal : KernelTailGoal := by
  refine ⟨1416 / (Real.pi * Real.sqrt 6), 1, by positivity, zero_lt_one, ?_⟩
  intro u hu
  exact abs_planeKernel_le (lt_of_lt_of_le zero_lt_one hu)

end BoundaryDraft
