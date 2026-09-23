import BoundaryDraft.CausalInterval

open MeasureTheory Set
open scoped Interval
noncomputable section
namespace BoundaryDraft

private theorem integral_polynomial_moment (n : ℕ) (v : ℝ) :
    (∫ u in (0 : ℝ)..v, (v-u)^2 * u^n) =
      2 * v^(n+3) / (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)) := by
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n:ℝ)+2 ≠ 0 := by positivity
  have hn3 : (n:ℝ)+3 ≠ 0 := by positivity
  let F := fun u : ℝ => v^2 * u^(n+1)/((n:ℝ)+1) -
    2*v*u^(n+2)/((n:ℝ)+2) + u^(n+3)/((n:ℝ)+3)
  have hd (u : ℝ) : HasDerivAt F ((v-u)^2*u^n) u := by
    have h1 := (((hasDerivAt_id u).pow (n+1)).const_mul (v^2)).div_const ((n:ℝ)+1)
    have h2 := (((hasDerivAt_id u).pow (n+2)).const_mul (2*v)).div_const ((n:ℝ)+2)
    have h3 := ((hasDerivAt_id u).pow (n+3)).div_const ((n:ℝ)+3)
    convert (h1.sub h2).add h3 using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      mul_one, show n+2-1=n+1 by omega, show n+3-1=n+2 by omega]
    field_simp
    simp only [pow_add, pow_one, pow_two]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => (v-u)^2*u^n)).intervalIntegrable 0 v)
  simp only [F, zero_pow (by omega : n+1 ≠ 0), zero_pow (by omega : n+2 ≠ 0),
    zero_pow (by omega : n+3 ≠ 0), mul_zero, zero_div, sub_zero, zero_add] at h
  rw [h]
  field_simp
  simp only [pow_add, pow_one, pow_two]
  ring

/-- The actual four-dimensional causal-interval moment, derived using the
proved null-coordinate Jacobian and two finite polynomial integrals. -/
theorem standard_causalInterval_moment (T : ℝ) (hT : 0 < T) (n : ℕ) :
    (∫ y in causalInterval 0 (timeAxis T), intervalSq 0 y ^ (2*n)) =
      Real.pi * T^(4*n+4) /
        ((2*(n:ℝ)+1)*(2*(n:ℝ)+2)*(2*(n:ℝ)+3)*(4*(n:ℝ)+4)) := by
  rw [integral_standard_causalInterval_eq_timeRadial T hT (fun s => s^(2*n))
    (by fun_prop), integral_timeRadial_eq_nullTriangle T hT (fun s => s^(2*n)) (by fun_prop)]
  have inner (v : ℝ) :
      (∫ u in (0:ℝ)..v, (v-u)^2*(2*u*v)^(2*n)) =
        (2:ℝ)^(2*n)*2 / ((2*(n:ℝ)+1)*(2*(n:ℝ)+2)*(2*(n:ℝ)+3)) * v^(4*n+3) := by
    have he (u : ℝ) : (v-u)^2*(2*u*v)^(2*n) =
        (2:ℝ)^(2*n)*v^(2*n)*((v-u)^2*u^(2*n)) := by ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul, integral_polynomial_moment]
    push_cast
    have hn1 : 2*(n:ℝ)+1 ≠ 0 := by positivity
    have hn2 : 2*(n:ℝ)+2 ≠ 0 := by positivity
    have hn3 : 2*(n:ℝ)+3 ≠ 0 := by positivity
    field_simp
    ring_nf
  simp_rw [inner]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 4*n+3+1 ≠ 0), sub_zero]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hn1 : 2*(n:ℝ)+1 ≠ 0 := by positivity
  have hn2 : 2*(n:ℝ)+2 ≠ 0 := by positivity
  have hn3 : 2*(n:ℝ)+3 ≠ 0 := by positivity
  have hn4 : 4*(n:ℝ)+4 ≠ 0 := by positivity
  have hexp : 4*n+3+1 = 2*(2*n+2) := by omega
  rw [div_pow, hexp, pow_mul (Real.sqrt 2), hs]
  push_cast
  field_simp
  ring_nf

end BoundaryDraft
