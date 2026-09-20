import BoundaryDraft.Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# A finite-interval Gaussian cancellation estimate

The weight `sqrt (1 - t)` differs from one by at most `t` on `[0,1]`.
An exact primitive cancels the constant-weight term. This proves the decay
needed for the plane kernel without differentiating an asymptotic remainder.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace BoundaryDraft

/-- The two cancellations used below are `(b,d) = (6,8)` and `(2,0)`. -/
def gaussianCancellationPolynomial (b d a t : ℝ) : ℝ :=
  b - (2 * b + 3 * d) * a * t ^ 2 + 2 * d * a ^ 2 * t ^ 4

private theorem hasDerivAt_gaussian (a t : ℝ) :
    HasDerivAt (fun x => Real.exp (-a * x ^ 2))
      (-2 * a * t * Real.exp (-a * t ^ 2)) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul (-a)).exp using 1
  dsimp
  ring

private theorem sqrt_weight_error {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |Real.sqrt (1 - t) - 1| ≤ t := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr ht.2)
  have h0 := Real.sqrt_nonneg (1 - t)
  have h1 : Real.sqrt (1 - t) ≤ 1 := by
    nlinarith [ht.1]
  rw [abs_of_nonpos (sub_nonpos.mpr h1)]
  nlinarith [sq_nonneg (Real.sqrt (1 - t) - (1 - t)), mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

private theorem exp_boundary_bounds {a : ℝ} (ha : 0 < a) :
    Real.exp (-a) ≤ 1 / a ∧ a * Real.exp (-a) ≤ 2 / a := by
  have h1 := Real.pow_div_factorial_le_exp a ha.le 1
  have h2 := Real.pow_div_factorial_le_exp a ha.le 2
  norm_num at h1 h2
  have he : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add]; simp
  have h1' := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (-a))
  have h2' := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg (-a))
  rw [he] at h1' h2'
  constructor
  · apply (le_div_iff₀ ha).2
    nlinarith
  · apply (le_div_iff₀ ha).2
    nlinarith

/-- An absolute estimate, not just a signed cancellation. The constant is
intentionally loose, and the estimate holds for every positive `a`. -/
theorem gaussianCancellation_bound (a b d : ℝ) (ha : 0 < a)
    (hb : 0 ≤ b) (hd : 0 ≤ d) :
    |∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) *
      gaussianCancellationPolynomial b d a t * Real.exp (-a * t ^ 2)| ≤
        (5 * b + 11 * d) / (2 * a) := by
  let P := gaussianCancellationPolynomial b d a
  let E := fun t : ℝ => Real.exp (-a * t ^ 2)
  let Q := fun t : ℝ => b + (2 * b + 3 * d) * a * t ^ 2 + 2 * d * a ^ 2 * t ^ 4
  have hP : Continuous P := by unfold P gaussianCancellationPolynomial; fun_prop
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hR : Continuous (fun t : ℝ => (Real.sqrt (1 - t) - 1) * P t * E t) := by
    fun_prop
  have hprim (t : ℝ) : HasDerivAt (fun x => (b * x - d * a * x ^ 3) * E x)
      (P t * E t) t := by
    convert (((hasDerivAt_id t).const_mul b).sub
      (((hasDerivAt_id t).pow 3).const_mul (d * a))).mul
      (hasDerivAt_gaussian a t) using 1
    dsimp [P, E, gaussianCancellationPolynomial]
    ring
  have hmass : (∫ t in (0 : ℝ)..1, P t * E t) = (b - d * a) * Real.exp (-a) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
      ((hP.mul hE).intervalIntegrable 0 1)]
    simp [E]
  have habsprim (t : ℝ) : HasDerivAt
      (fun x => -((3 * b + 7 * d) / 2 + ((2 * b + 7 * d) / 2) * a * x ^ 2 +
        d * a ^ 2 * x ^ 4) / a * E x) (t * Q t * E t) t := by
    have hp := (((hasDerivAt_const t ((3 * b + 7 * d) / 2)).add
      (((hasDerivAt_id t).pow 2).const_mul (((2 * b + 7 * d) / 2) * a))).add
      (((hasDerivAt_id t).pow 4).const_mul (d * a ^ 2)))
    convert (hp.neg.div_const a).mul (hasDerivAt_gaussian a t) using 1
    dsimp [Q, E]
    field_simp
    ring
  have hweight : (∫ t in (0 : ℝ)..1, t * Q t * E t) ≤ (3 * b + 7 * d) / (2 * a) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => habsprim t)
      ((continuous_id.mul hQ |>.mul hE).intervalIntegrable 0 1)]
    dsimp [E]
    simp only [one_pow, mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, add_zero, Real.exp_zero]
    have hn : 0 ≤ ((3 * b + 7 * d) / 2 + ((2 * b + 7 * d) / 2) * a + d * a ^ 2) / a *
        Real.exp (-a) := by positivity
    calc
      _ = (3 * b + 7 * d) / (2 * a) -
          ((3 * b + 7 * d) / 2 + ((2 * b + 7 * d) / 2) * a + d * a ^ 2) / a *
            Real.exp (-a) := by ring
      _ ≤ _ := sub_le_self _ hn
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |(Real.sqrt (1 - t) - 1) * P t * E t| ≤ t * Q t * E t := by
    have hPQ : |P t| ≤ Q t := by
      dsimp [P, Q, gaussianCancellationPolynomial]
      apply abs_le.2
      constructor <;> nlinarith [sq_nonneg t, sq_nonneg (t ^ 2),
        mul_nonneg (by positivity : 0 ≤ (2 * b + 3 * d) * a) (sq_nonneg t),
        mul_nonneg (by positivity : 0 ≤ 2 * d * a ^ 2) (by positivity : 0 ≤ t ^ 4)]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (sqrt_weight_error ht) hPQ (abs_nonneg _) ht.1) (Real.exp_nonneg _)
  have herr : |∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t) - 1) * P t * E t| ≤
      (3 * b + 7 * d) / (2 * a) := by
    apply (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
    apply le_trans (intervalIntegral.integral_mono_on zero_le_one
      (hR.abs.intervalIntegrable 0 1)
      ((continuous_id.mul hQ |>.mul hE).intervalIntegrable 0 1) hpoint) hweight
  have hsplit : (∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) * P t * E t) =
      (∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t) - 1) * P t * E t) +
        (b - d * a) * Real.exp (-a) := by
    rw [← hmass, ← intervalIntegral.integral_add (hR.intervalIntegrable 0 1)
      ((hP.mul hE).intervalIntegrable 0 1)]
    congr 1
    funext t
    ring
  have hbnd : |(b - d * a) * Real.exp (-a)| ≤ (b + 2 * d) / a := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      |b - d * a| * Real.exp (-a) ≤ (b + d * a) * Real.exp (-a) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hb, abs_of_nonneg (mul_nonneg hd ha.le)])
      _ ≤ (b + 2 * d) / a := by
        have h := exp_boundary_bounds ha
        have h₁ := mul_le_mul_of_nonneg_left h.1 hb
        have h₂ := mul_le_mul_of_nonneg_left h.2 hd
        calc
          _ = b * Real.exp (-a) + d * (a * Real.exp (-a)) := by ring
          _ ≤ b * (1 / a) + d * (2 / a) := add_le_add h₁ h₂
          _ = _ := by ring
  change |∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) * P t * E t| ≤ _
  rw [hsplit]
  exact (abs_add _ _).trans ((add_le_add herr hbnd).trans_eq (by ring))

/-- The substitution `t = 1 - v²` is smooth in the direction used here;
no derivative of `sqrt` at zero is taken. -/
theorem integral_sq_comp_one_sub_sq (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ v in (0 : ℝ)..1, v ^ 2 * f (1 - v ^ 2)) =
      (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, Real.sqrt (1 - t) * f t := by
  have hd (v : ℝ) : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * v) v := by
    convert ((hasDerivAt_id v).pow 2).const_sub 1 using 1
    dsimp
    ring
  have h := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 1) (g := fun t => Real.sqrt (1 - t) * f t)
    (fun v _ => hd v) (by fun_prop) (by fun_prop)
  have heq : (∫ v in (0 : ℝ)..1,
      (fun t => Real.sqrt (1 - t) * f t) (1 - v ^ 2) * (-2 * v)) =
      -2 * ∫ v in (0 : ℝ)..1, v ^ 2 * f (1 - v ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv0 : 0 ≤ v := (show v ∈ Icc (0 : ℝ) 1 by simpa using hv).1
    dsimp
    rw [show 1 - (1 - v ^ 2) = v ^ 2 by ring, Real.sqrt_sq hv0]
    ring
  simp only [Function.comp_def] at h
  rw [heq] at h
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, sub_zero, sub_self] at h
  rw [intervalIntegral.integral_symm 0 1] at h
  linarith

end BoundaryDraft
