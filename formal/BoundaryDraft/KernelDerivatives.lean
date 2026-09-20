import BoundaryDraft.KernelScaling
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differentiating the plane auxiliary integral

A fixed-interval representation makes differentiation under the integral
legitimate: the integrands and their parameter derivatives are jointly
continuous, hence uniformly bounded on every compact parameter rectangle.
This establishes the derivatives through order three, not the large-argument
estimates or the reduction of the four-dimensional action to this integral.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

namespace BoundaryDraft

/-- A compact-rectangle specialization of dominated differentiation. -/
theorem hasDerivAt_integral_unitInterval
    (F F' : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x v, HasDerivAt (fun y => F y v) (F' x v) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ v in (0 : ℝ)..1, F y v)
      (∫ v in (0 : ℝ)..1, F' x v) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := Function.uncurry F') (s := Icc (x - 1) (x + 1) ×ˢ Icc (0 : ℝ) 1)
    hF'.continuousOn
  have hc (y : ℝ) : Continuous (F y) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hc' (y : ℝ) : Continuous (F' y) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (ε := 1) zero_lt_one
    (Eventually.of_forall fun y => (hc y).aestronglyMeasurable)
    ((hc x).intervalIntegrable 0 1)
    (hc' x).aestronglyMeasurable
    (Eventually.of_forall fun v hv y hy => by
      apply hC (y, v)
      have hy' : |y - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
      rcases abs_lt.mp hy' with ⟨hyl, hyr⟩
      have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa using hv
      exact ⟨⟨by linarith, by linarith⟩, hv'.1.le, hv'.2⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 1)
    (Eventually.of_forall fun v _ y _ => hd y v)).2

-- Expand powers of H instead of dividing by H, so the formulas and their
-- derivative proofs apply at the origin as well as at positive heights.
private def q (ρ v : ℝ) : ℝ := -(Real.pi / 24) * ρ * (1 - v ^ 2) ^ 2

private def f0 (ρ H v : ℝ) : ℝ :=
  v ^ 2 * H ^ 3 * Real.exp (q ρ v * H ^ 4)

private def f1 (ρ H v : ℝ) : ℝ :=
  v ^ 2 * (3 * H ^ 2 + 4 * q ρ v * H ^ 6) * Real.exp (q ρ v * H ^ 4)

private def f2 (ρ H v : ℝ) : ℝ :=
  v ^ 2 * (6 * H + 36 * q ρ v * H ^ 5 + 16 * (q ρ v) ^ 2 * H ^ 9) *
    Real.exp (q ρ v * H ^ 4)

private def f3 (ρ H v : ℝ) : ℝ :=
  v ^ 2 * (6 + 204 * q ρ v * H ^ 4 + 288 * (q ρ v) ^ 2 * H ^ 8 +
    64 * (q ρ v) ^ 3 * H ^ 12) * Real.exp (q ρ v * H ^ 4)

private theorem hasDerivAt_exp_quartic (Q H : ℝ) :
    HasDerivAt (fun y => Real.exp (Q * y ^ 4))
      (4 * Q * H ^ 3 * Real.exp (Q * H ^ 4)) H := by
  convert (((hasDerivAt_id H).pow 4).const_mul Q).exp using 1
  dsimp
  ring

private theorem hasDerivAt_f0 (ρ H v : ℝ) :
    HasDerivAt (fun y => f0 ρ y v) (f1 ρ H v) H := by
  convert ((((hasDerivAt_id H).pow 3).const_mul (v ^ 2)).mul
    (hasDerivAt_exp_quartic (q ρ v) H)) using 1
  dsimp [f0, f1]
  ring

private theorem hasDerivAt_f1 (ρ H v : ℝ) :
    HasDerivAt (fun y => f1 ρ y v) (f2 ρ H v) H := by
  convert (((((hasDerivAt_id H).pow 2).const_mul 3).add
    (((hasDerivAt_id H).pow 6).const_mul (4 * q ρ v))).const_mul (v ^ 2)).mul
    (hasDerivAt_exp_quartic (q ρ v) H) using 1
  dsimp [f1, f2]
  ring

private theorem hasDerivAt_f2 (ρ H v : ℝ) :
    HasDerivAt (fun y => f2 ρ y v) (f3 ρ H v) H := by
  convert (((((hasDerivAt_id H).const_mul 6).add
    (((hasDerivAt_id H).pow 5).const_mul (36 * q ρ v))).add
    (((hasDerivAt_id H).pow 9).const_mul (16 * (q ρ v) ^ 2))).const_mul (v ^ 2)).mul
    (hasDerivAt_exp_quartic (q ρ v) H) using 1
  dsimp [f2, f3]
  ring

private theorem planeAuxiliary_eq_integral (ρ H : ℝ) :
    planeAuxiliary ρ H = 4 * Real.pi * ∫ v in (0 : ℝ)..1, f0 ρ H v := by
  have h := planeAuxiliary_scaling ρ H 1
  simp only [mul_one] at h
  rw [h, planeAuxiliary]
  simp only [one_pow]
  have hf (v : ℝ) : f0 ρ H v = H ^ 3 *
      (v ^ 2 * Real.exp (-(Real.pi / 24) * (ρ * H ^ 4) * (1 - v ^ 2) ^ 2)) := by
    unfold f0 q
    rw [show -(Real.pi / 24) * ρ * (1 - v ^ 2) ^ 2 * H ^ 4 =
      -(Real.pi / 24) * (ρ * H ^ 4) * (1 - v ^ 2) ^ 2 by ring]
    ring
  simp_rw [hf, intervalIntegral.integral_const_mul]
  ring

/-- Explicit first derivative of the auxiliary integral. -/
def planeAuxiliaryFirst (ρ H : ℝ) : ℝ :=
  4 * Real.pi * ∫ v in (0 : ℝ)..1, f1 ρ H v

/-- Explicit second derivative of the auxiliary integral. -/
def planeAuxiliarySecond (ρ H : ℝ) : ℝ :=
  4 * Real.pi * ∫ v in (0 : ℝ)..1, f2 ρ H v

/-- Explicit third derivative, retaining the boundary constant. -/
def planeAuxiliaryThird (ρ H : ℝ) : ℝ :=
  4 * Real.pi * ∫ v in (0 : ℝ)..1, f3 ρ H v

/-- The first differentiated integral is justified by compact domination. -/
theorem hasDerivAt_planeAuxiliary (ρ H : ℝ) :
    HasDerivAt (planeAuxiliary ρ) (planeAuxiliaryFirst ρ H) H := by
  have h := (hasDerivAt_integral_unitInterval (f0 ρ) (f1 ρ)
    (by unfold Function.uncurry f0 q; fun_prop)
    (by unfold Function.uncurry f1 q; fun_prop) (hasDerivAt_f0 ρ) H).const_mul
      (4 * Real.pi)
  simpa only [← planeAuxiliary_eq_integral, planeAuxiliaryFirst] using h

/-- A second differentiation under the integral, with no unproved interchange. -/
theorem hasDerivAt_planeAuxiliaryFirst (ρ H : ℝ) :
    HasDerivAt (planeAuxiliaryFirst ρ) (planeAuxiliarySecond ρ H) H := by
  exact (hasDerivAt_integral_unitInterval (f1 ρ) (f2 ρ)
    (by unfold Function.uncurry f1 q; fun_prop)
    (by unfold Function.uncurry f2 q; fun_prop) (hasDerivAt_f1 ρ) H).const_mul
      (4 * Real.pi)

/-- A third differentiation under the integral. -/
theorem hasDerivAt_planeAuxiliarySecond (ρ H : ℝ) :
    HasDerivAt (planeAuxiliarySecond ρ) (planeAuxiliaryThird ρ H) H := by
  exact (hasDerivAt_integral_unitInterval (f2 ρ) (f3 ρ)
    (by unfold Function.uncurry f2 q; fun_prop)
    (by unfold Function.uncurry f3 q; fun_prop) (hasDerivAt_f2 ρ) H).const_mul
      (4 * Real.pi)

/-- The total derivative agrees with the proved first derivative. -/
theorem deriv_planeAuxiliary (ρ : ℝ) :
    deriv (planeAuxiliary ρ) = planeAuxiliaryFirst ρ :=
  funext fun H => (hasDerivAt_planeAuxiliary ρ H).deriv

/-- The total derivative agrees with the proved second derivative. -/
theorem deriv_planeAuxiliaryFirst (ρ : ℝ) :
    deriv (planeAuxiliaryFirst ρ) = planeAuxiliarySecond ρ :=
  funext fun H => (hasDerivAt_planeAuxiliaryFirst ρ H).deriv

/-- The total derivative agrees with the proved third derivative. -/
theorem deriv_planeAuxiliarySecond (ρ : ℝ) :
    deriv (planeAuxiliarySecond ρ) = planeAuxiliaryThird ρ :=
  funext fun H => (hasDerivAt_planeAuxiliarySecond ρ H).deriv

/-- The derivative-based kernel has this genuine differentiated-integral
representation; no regularity is being assumed through `deriv`. -/
theorem planeKernel_eq_second (ρ H : ℝ) :
    planeKernel ρ H = Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6) *
      planeAuxiliarySecond ρ H := by
  rw [planeKernel, deriv_planeAuxiliary, deriv_planeAuxiliaryFirst]

/-- The concrete kernel is differentiable at every finite argument. -/
theorem hasDerivAt_planeKernel (ρ H : ℝ) :
    HasDerivAt (planeKernel ρ)
      (Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6) * planeAuxiliaryThird ρ H) H := by
  simpa only [← planeKernel_eq_second] using
    (hasDerivAt_planeAuxiliarySecond ρ H).const_mul
      (Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6))

/-- In particular the kernel is integrable on every compact interval. -/
theorem continuous_planeKernel (ρ : ℝ) : Continuous (planeKernel ρ) :=
  continuous_iff_continuousAt.2 fun H => (hasDerivAt_planeKernel ρ H).continuousAt

theorem planeAuxiliaryFirst_zero (ρ : ℝ) : planeAuxiliaryFirst ρ 0 = 0 := by
  simp [planeAuxiliaryFirst, f1]

theorem planeAuxiliarySecond_zero (ρ : ℝ) : planeAuxiliarySecond ρ 0 = 0 := by
  simp [planeAuxiliarySecond, f2]

/-- The boundary constant in the draft is `8π`, not zero. -/
theorem planeAuxiliaryThird_zero (ρ : ℝ) : planeAuxiliaryThird ρ 0 = 8 * Real.pi := by
  have hd (v : ℝ) : HasDerivAt (fun y : ℝ => 2 * y ^ 3) (v ^ 2 * 6) v := by
    convert ((hasDerivAt_id v).pow 3).const_mul 2 using 1
    dsimp
    ring
  have hi : (∫ v in (0 : ℝ)..1, v ^ 2 * 6) = 2 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
      ((continuous_pow 2).mul continuous_const |>.intervalIntegrable 0 1)
  simp [planeAuxiliaryThird, f3, hi]
  ring

theorem planeKernel_zero (ρ : ℝ) : planeKernel ρ 0 = 0 := by
  rw [planeKernel_eq_second, planeAuxiliarySecond_zero, mul_zero]

/-- Exact finite-interval mass. Passing to infinity still requires the tail
and the limiting value of the first derivative. -/
theorem integral_planeKernel (ρ H : ℝ) :
    (∫ u in (0 : ℝ)..H, planeKernel ρ u) =
      Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6) * planeAuxiliaryFirst ρ H := by
  simp_rw [planeKernel_eq_second]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_planeAuxiliaryFirst ρ u)
      ((continuous_iff_continuousAt.2 fun u =>
        (hasDerivAt_planeAuxiliarySecond ρ u).continuousAt).intervalIntegrable 0 H),
    planeAuxiliaryFirst_zero, sub_zero]

/-- Exact finite-interval signed first moment. This does not assert absolute
integrability of the first moment on the half-line. -/
theorem integral_mul_planeKernel (ρ H : ℝ) :
    (∫ u in (0 : ℝ)..H, u * planeKernel ρ u) =
      Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6) *
        (H * planeAuxiliaryFirst ρ H - planeAuxiliary ρ H) := by
  have hd (u : ℝ) :
      HasDerivAt (fun y => y * planeAuxiliaryFirst ρ y - planeAuxiliary ρ y)
        (u * planeAuxiliarySecond ρ u) u := by
    convert ((hasDerivAt_id u).mul (hasDerivAt_planeAuxiliaryFirst ρ u)).sub
      (hasDerivAt_planeAuxiliary ρ u) using 1
    dsimp
    ring
  have hc : Continuous (fun u => u * planeAuxiliarySecond ρ u) :=
    continuous_id.mul (continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_planeAuxiliarySecond ρ u).continuousAt)
  simp_rw [planeKernel_eq_second, mul_left_comm _ (Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      (hc.intervalIntegrable 0 H)]
  simp [planeAuxiliary]

end BoundaryDraft
