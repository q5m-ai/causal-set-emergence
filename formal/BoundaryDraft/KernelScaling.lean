import BoundaryDraft.Specification
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact scaling of the concrete plane kernel

These identities use the auxiliary integral in `Specification`, not a kernel
postulated to have the desired scaling. The mass, moment, and tail proofs
are in `KernelEstimates` and `KernelHalfLine`; the four-dimensional reduction
remains open.
-/

open MeasureTheory

noncomputable section

namespace BoundaryDraft

/-- Rescale the radial integration variable, including the oriented case
`H < 0`. No differentiating under the integral is needed for this identity. -/
theorem planeAuxiliary_scaling (ρ s H : ℝ) :
    planeAuxiliary ρ (s * H) = s ^ 3 * planeAuxiliary (ρ * s ^ 4) H := by
  unfold planeAuxiliary
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun r : ℝ => r ^ 2 * Real.exp (-(Real.pi / 24) * ρ * ((s * H) ^ 2 - r ^ 2) ^ 2))
    (a := 0) (b := H) s
  simp only [smul_eq_mul, mul_zero] at h
  rw [← h]
  have hexp (r : ℝ) :
      -(Real.pi / 24) * ρ * ((s * H) ^ 2 - (s * r) ^ 2) ^ 2 =
        -(Real.pi / 24) * (ρ * s ^ 4) * (H ^ 2 - r ^ 2) ^ 2 := by ring
  simp_rw [hexp, mul_pow, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Chain rule for a nonzero linear change of variable, also when `f` is
not differentiable (both total derivatives then vanish). This is not an
assumption of differentiability of the concrete auxiliary integral. -/
private theorem deriv_comp_scale (f : ℝ → ℝ) (s x : ℝ) (hs : s ≠ 0) :
    deriv (fun y => f (s * y)) x = s * deriv f (s * x) := by
  by_cases hf : DifferentiableAt ℝ f (s * x)
  · simpa [mul_comm] using
      (hf.hasDerivAt.comp x ((hasDerivAt_id x).const_mul s)).deriv
  · have hcomp : ¬ DifferentiableAt ℝ (fun y => f (s * y)) x := by
      intro hc
      have hc' : DifferentiableAt ℝ (fun y => f (s * y)) (s⁻¹ * (s * x)) := by
        simpa only [inv_mul_cancel_left₀ hs] using hc
      have hi := hc'.comp (s * x)
        (((hasDerivAt_id (s * x)).const_mul s⁻¹).differentiableAt)
      apply hf
      convert hi using 1
      simp [Function.comp_def, hs]
    rw [deriv_zero_of_not_differentiableAt hcomp,
      deriv_zero_of_not_differentiableAt hf, mul_zero]

/-- A fourth-power density parametrization of the actual kernel. -/
theorem planeKernel_fourth_power (s H : ℝ) (hs : 0 < s) :
    planeKernel (s ^ 4) H = s * planeKernel 1 (s * H) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hF : planeAuxiliary (s ^ 4) =
      fun x => (s ^ 3)⁻¹ * planeAuxiliary 1 (s * x) := by
    funext x
    have h := planeAuxiliary_scaling 1 s x
    simp only [one_mul] at h
    rw [h]
    field_simp
  have hF' : deriv (planeAuxiliary (s ^ 4)) =
      fun x => (s ^ 2)⁻¹ * deriv (planeAuxiliary 1) (s * x) := by
    funext x
    rw [hF, deriv_const_mul_field, deriv_comp_scale _ _ _ hs0]
    field_simp
    ring
  have hF'' : deriv (deriv (planeAuxiliary (s ^ 4))) H =
      s⁻¹ * deriv (deriv (planeAuxiliary 1)) (s * H) := by
    rw [hF', deriv_const_mul_field, deriv_comp_scale _ _ _ hs0]
    field_simp
    ring
  have hsqrt : Real.sqrt (s ^ 4) = s ^ 2 := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg s)]
  simp only [planeKernel, hF'', hsqrt, Real.sqrt_one]
  field_simp
  ring

/-- Equation (14) of the draft, with the inverse collar width expressed as
the positive fourth root `sqrt (sqrt ρ)`. -/
theorem planeKernel_density_scaling (ρ H : ℝ) (hρ : 0 < ρ) :
    planeKernel ρ H =
      Real.sqrt (Real.sqrt ρ) * planeKernel 1 (Real.sqrt (Real.sqrt ρ) * H) := by
  have hs : 0 < Real.sqrt (Real.sqrt ρ) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hρ)
  have hpow : Real.sqrt (Real.sqrt ρ) ^ 4 = ρ := by
    rw [show Real.sqrt (Real.sqrt ρ) ^ 4 =
      (Real.sqrt (Real.sqrt ρ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg ρ), Real.sq_sqrt hρ.le]
  simpa only [hpow] using planeKernel_fourth_power (Real.sqrt (Real.sqrt ρ)) H hs

end BoundaryDraft
