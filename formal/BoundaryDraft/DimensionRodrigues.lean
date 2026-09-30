import BoundaryDraft.DimensionKernel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Rodrigues identity and one-sided endpoint jets

All differential identities are proved on the open positive half-line. In
particular, no arbitrary-order smoothness at zero is assumed for fractional
powers in odd dimensions. The auxiliary derivative polynomials give explicit
positive-power factors for the lower endpoint jets.
-/

open Set Filter Polynomial
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Polynomial factor in the `k`th derivative of a power times the exponential.
The initial power `r` is real; the dimension only fixes the exponential power. -/
def dimensionDerivativePolynomial (d : ℕ) (r : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 =>
    let p := dimensionDerivativePolynomial d r k
    C (r - k) * p + C ((d : ℝ) / 2) * X * (derivative p - p)

/-- Differentiate a power times an arbitrary polynomial-exponential factor,
strictly away from zero. Neither the dimension nor the scale needs a sign
assumption for this local identity. -/
theorem hasDerivAt_rpow_polynomial_exp (p : Polynomial ℝ) (r q c : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s : ℝ => s ^ r * p.eval (c * s ^ q) * Real.exp (-(c * s ^ q)))
      (σ ^ (r - 1) *
        (r * p.eval (c * σ ^ q) + q * (c * σ ^ q) *
          (p.derivative.eval (c * σ ^ q) - p.eval (c * σ ^ q))) *
        Real.exp (-(c * σ ^ q))) σ := by
  have hr := Real.hasDerivAt_rpow_const (p := r) (Or.inl hσ.ne')
  have hz := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hσ.ne')).const_mul c
  convert (hr.mul ((p.hasDerivAt _).comp σ hz)).mul hz.neg.exp using 1
  rw [Real.rpow_sub_one hσ.ne' r, Real.rpow_sub_one hσ.ne' q]
  field_simp
  ring

/-- Explicit derivative formula, valid for every order on the positive domain.
Negative powers in this formula are only evaluated at strictly positive points. -/
theorem iteratedDeriv_rpow_exp (d k : ℕ) (r c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv k (fun s : ℝ => s ^ r * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ =
      σ ^ (r - k) * (dimensionDerivativePolynomial d r k).eval
        (c * σ ^ ((d : ℝ) / 2)) * Real.exp (-(c * σ ^ ((d : ℝ) / 2))) := by
  induction k generalizing σ with
  | zero => simp [dimensionDerivativePolynomial]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s : ℝ => s ^ r *
        Real.exp (-(c * s ^ ((d : ℝ) / 2)))) =ᶠ[𝓝 σ]
        (fun s : ℝ => s ^ (r - k) *
          (dimensionDerivativePolynomial d r k).eval (c * s ^ ((d : ℝ) / 2)) *
          Real.exp (-(c * s ^ ((d : ℝ) / 2)))) := by
      filter_upwards [Ioi_mem_nhds hσ] with s hs
      exact ih hs
    rw [he.deriv_eq]
    rw [(hasDerivAt_rpow_polynomial_exp (dimensionDerivativePolynomial d r k)
      (r - k) ((d : ℝ) / 2) c hσ).deriv]
    simp only [dimensionDerivativePolynomial, eval_add, eval_mul, eval_C, eval_X,
      eval_sub, Nat.cast_add, Nat.cast_one]
    congr 2
    congr 1
    ring

/-- Natural-power version of the explicit derivative formula. -/
theorem iteratedDeriv_pow_exp (d m k : ℕ) (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv k (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ =
      σ ^ ((m : ℝ) - k) * (dimensionDerivativePolynomial d m k).eval
        (c * σ ^ ((d : ℝ) / 2)) * Real.exp (-(c * σ ^ ((d : ℝ) / 2))) := by
  simpa only [Real.rpow_natCast] using iteratedDeriv_rpow_exp d k m c hσ

/-- Smoothness is asserted only on the positive half-line, including when the
dimension is odd and the exponential involves a nonintegral power. -/
theorem contDiffOn_pow_exp (d m : ℕ) (c : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n
      (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) (Ioi 0) := by
  intro σ hσ
  exact ((contDiffAt_id.pow m).mul
    ((contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hσ.ne')).neg.exp)).contDiffWithinAt

/-- All iterated derivatives are differentiable at positive points, with no
regularity assertion at zero. -/
theorem differentiableAt_iteratedDeriv_pow_exp (d m k : ℕ) (c : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    DifferentiableAt ℝ (iteratedDeriv k
      (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2))))) σ := by
  apply (hasDerivAt_rpow_polynomial_exp (dimensionDerivativePolynomial d m k)
    ((m : ℝ) - k) ((d : ℝ) / 2) c hσ).differentiableAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hσ] with s hs
  exact iteratedDeriv_pow_exp d m k c hs

/-- The local Leibniz identity underlying the Euler-factor recurrence. The
hypothesis concerns derivatives only on the open set, not across its boundary. -/
theorem iteratedDeriv_succ_id_mul_on {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ k : ℕ, ∀ x ∈ s, DifferentiableAt ℝ (iteratedDeriv k f) x)
    (n : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDeriv (n + 1) (fun y => y * f y) x =
      x * iteratedDeriv (n + 1) f x + ((n : ℝ) + 1) * iteratedDeriv n f x := by
  induction n generalizing x with
  | zero =>
    simpa [iteratedDeriv_zero, iteratedDeriv_one, add_comm] using
      ((hasDerivAt_id x).mul (hf 0 x hx).hasDerivAt).deriv
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (n + 1) (fun y => y * f y) =ᶠ[𝓝 x]
        (fun y => y * iteratedDeriv (n + 1) f y +
          ((n : ℝ) + 1) * iteratedDeriv n f y) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact ih hy
    have hd := (((hasDerivAt_id x).mul (hf (n + 1) x hx).hasDerivAt).add
      ((hf n x hx).hasDerivAt.const_mul ((n : ℝ) + 1))).deriv
    simp only [id_eq] at hd
    rw [he.deriv_eq, hd]
    simp only [iteratedDeriv_succ, Nat.cast_add, Nat.cast_one]
    ring

/-- Rodrigues' formula for the actual polynomial recurrence, at every stage.
This holds for arbitrary real scale and every natural dimension on the positive
half-line, hence in particular for positive scale and dimension at least two. -/
theorem dimensionPolynomialStage_rodrigues (d m : ℕ) (c : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv m (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ =
      (m.factorial : ℝ) * (dimensionPolynomialStage d m).eval
        (c * σ ^ ((d : ℝ) / 2)) * Real.exp (-(c * σ ^ ((d : ℝ) / 2))) := by
  induction m generalizing σ with
  | zero => simp [dimensionPolynomialStage]
  | succ m ih =>
    have he : (fun s : ℝ => s ^ (m + 1) * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) =
        (fun s : ℝ => s * (s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2))))) := by
      funext s
      rw [pow_succ]
      ring
    rw [he, iteratedDeriv_succ_id_mul_on isOpen_Ioi
      (fun k s hs => differentiableAt_iteratedDeriv_pow_exp d m k c hs) m hσ,
      ih hσ, iteratedDeriv_succ]
    have hloc : iteratedDeriv m
        (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) =ᶠ[𝓝 σ]
        (fun s : ℝ => (m.factorial : ℝ) *
          (s ^ (0 : ℝ) * (dimensionPolynomialStage d m).eval
            (c * s ^ ((d : ℝ) / 2)) * Real.exp (-(c * s ^ ((d : ℝ) / 2))))) := by
      filter_upwards [Ioi_mem_nhds hσ] with s hs
      simpa only [Real.rpow_zero, one_mul, mul_assoc] using ih hs
    rw [hloc.deriv_eq,
      ((hasDerivAt_rpow_polynomial_exp (dimensionPolynomialStage d m) 0
        ((d : ℝ) / 2) c hσ).const_mul (m.factorial : ℝ)).deriv]
    simp only [zero_sub, Real.rpow_neg_one, zero_mul, zero_add,
      dimensionPolynomialStage, eval_add, eval_mul, eval_C, eval_X, eval_sub,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- At the diagonal order, the auxiliary derivative polynomial is exactly the
factorial multiple of the original Euler-recurrence polynomial. -/
theorem dimensionDerivativePolynomial_diagonal (d m : ℕ) :
    dimensionDerivativePolynomial d m m = C (m.factorial : ℝ) *
      dimensionPolynomialStage d m := by
  apply Polynomial.funext
  intro z
  have h := iteratedDeriv_pow_exp d m m z (σ := 1) zero_lt_one
  have hr := dimensionPolynomialStage_rodrigues d m z (σ := 1) zero_lt_one
  rw [hr] at h
  simp only [Real.one_rpow, mul_one, sub_self, one_mul] at h
  simp only [eval_mul, eval_C]
  exact (mul_right_cancel₀ (Real.exp_ne_zero _) h).symm

/-- The kernel specialization retains the original, independently defined
`dimensionKernel`; the factorial has not been absorbed into a new kernel. -/
theorem dimensionKernel_rodrigues (d : ℕ) (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    iteratedDeriv (dimensionFactorCount d)
      (fun s : ℝ => s ^ dimensionFactorCount d *
        Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ =
      ((dimensionFactorCount d).factorial : ℝ) *
        dimensionKernel d (c * σ ^ ((d : ℝ) / 2)) := by
  simpa only [dimensionKernel, dimensionPolynomial, mul_assoc] using
    dimensionPolynomialStage_rodrigues d (dimensionFactorCount d) c hσ

/-- A derivative contract for positive-domain integration by parts. -/
theorem hasDerivAt_iteratedDeriv_pow_exp (d m k : ℕ) (c : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (iteratedDeriv k
      (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))))
      (iteratedDeriv (k + 1)
        (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ) σ := by
  rw [iteratedDeriv_succ]
  exact (differentiableAt_iteratedDeriv_pow_exp d m k c hσ).hasDerivAt

/-- The leading coefficient of each lower jet is the falling factorial. -/
theorem dimensionDerivativePolynomial_eval_zero (d m k : ℕ) (hk : k ≤ m) :
    (dimensionDerivativePolynomial d m k).eval 0 = (m.descFactorial k : ℝ) := by
  induction k with
  | zero => simp [dimensionDerivativePolynomial]
  | succ k ih =>
    have hkm : k ≤ m := Nat.le_of_succ_le hk
    simp only [dimensionDerivativePolynomial, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, zero_mul, add_zero, ih hkm, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub hkm]

private theorem tendsto_rodriguesFactor_zero (p : Polynomial ℝ) (q c : ℝ)
    (hq : 0 < q) :
    Tendsto (fun s : ℝ => p.eval (c * s ^ q) * Real.exp (-(c * s ^ q)))
      (𝓝[>] 0) (𝓝 (p.eval 0)) := by
  have hz : ContinuousAt (fun s : ℝ => c * s ^ q) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hq.le))
  have hp : ContinuousAt (fun s : ℝ => p.eval (c * s ^ q)) 0 :=
    (p.hasDerivAt _).continuousAt.comp hz
  simpa only [Real.zero_rpow hq.ne', mul_zero, neg_zero, Real.exp_zero, mul_one]
    using (hp.mul hz.neg.rexp).tendsto.mono_left nhdsWithin_le_nhds

/-- The normalized one-sided lower jets have their exact finite limits. This
also includes the top jet `k = m`, whose limit is `m!`. -/
theorem tendsto_iteratedDeriv_pow_exp_div_rpow_zero (d m k : ℕ)
    (hd : 0 < d) (hk : k ≤ m) (c : ℝ) :
    Tendsto (fun σ : ℝ => iteratedDeriv k
      (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ /
        σ ^ ((m : ℝ) - k)) (𝓝[>] 0) (𝓝 (m.descFactorial k : ℝ)) := by
  have hq : 0 < (d : ℝ) / 2 := by positivity
  have ht := tendsto_rodriguesFactor_zero (dimensionDerivativePolynomial d m k)
    ((d : ℝ) / 2) c hq
  rw [dimensionDerivativePolynomial_eval_zero d m k hk] at ht
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with σ hσ
  rw [iteratedDeriv_pow_exp d m k c hσ]
  have hpow : σ ^ ((m : ℝ) - k) ≠ 0 := (Real.rpow_pos_of_pos hσ _).ne'
  field_simp
  ring

/-- Every jet of order strictly below the prefactor power vanishes at the lower
endpoint, approached from the positive side. -/
theorem tendsto_iteratedDeriv_pow_exp_zero (d m k : ℕ)
    (hd : 0 < d) (hk : k < m) (c : ℝ) :
    Tendsto (iteratedDeriv k
      (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))))
      (𝓝[>] 0) (𝓝 0) := by
  have hr : 0 < (m : ℝ) - k := sub_pos.mpr (Nat.cast_lt.mpr hk)
  have hp : Tendsto (fun σ : ℝ => σ ^ ((m : ℝ) - k)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq, Real.zero_rpow hr.ne'] using
      (continuousAt_id.rpow_const (Or.inr hr.le)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have ht := (tendsto_iteratedDeriv_pow_exp_div_rpow_zero d m k hd hk.le c).mul hp
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_mem_nhdsWithin] with σ hσ
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hσ _).ne'

/-- The top jet has right limit `m!`, without claiming arbitrary-order
smoothness at the endpoint. -/
theorem tendsto_iteratedDeriv_pow_exp_top_zero (d m : ℕ) (hd : 0 < d) (c : ℝ) :
    Tendsto (iteratedDeriv m
      (fun s : ℝ => s ^ m * Real.exp (-(c * s ^ ((d : ℝ) / 2)))))
      (𝓝[>] 0) (𝓝 (m.factorial : ℝ)) := by
  simpa only [sub_self, Real.rpow_zero, div_one, Nat.descFactorial_self] using
    tendsto_iteratedDeriv_pow_exp_div_rpow_zero d m m hd le_rfl c

/-- An explicit power bound on each lower jet near zero. Its radius may depend
on the scale and dimension; the power is positive when `k < m`. -/
theorem eventually_abs_iteratedDeriv_pow_exp_le (d m k : ℕ)
    (hd : 0 < d) (hk : k ≤ m) (c : ℝ) :
    ∀ᶠ σ : ℝ in 𝓝[>] 0,
      |iteratedDeriv k (fun s : ℝ => s ^ m *
        Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ| ≤
        ((m.descFactorial k : ℝ) + 1) * σ ^ ((m : ℝ) - k) := by
  have ht := (tendsto_iteratedDeriv_pow_exp_div_rpow_zero d m k hd hk c).abs
  rw [abs_of_nonneg (Nat.cast_nonneg _)] at ht
  have hb := ht.eventually_lt_const (lt_add_one (m.descFactorial k : ℝ))
  filter_upwards [hb, eventually_mem_nhdsWithin] with σ hb hσ
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hσ _)] at hb
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hσ _)).mp hb).le

/-- Interval form of the endpoint bound, for finite-interval arguments. -/
theorem exists_abs_iteratedDeriv_pow_exp_le (d m k : ℕ)
    (hd : 0 < d) (hk : k ≤ m) (c : ℝ) :
    ∃ δ > (0 : ℝ), ∀ σ ∈ Ioo 0 δ,
      |iteratedDeriv k (fun s : ℝ => s ^ m *
        Real.exp (-(c * s ^ ((d : ℝ) / 2)))) σ| ≤
        ((m.descFactorial k : ℝ) + 1) * σ ^ ((m : ℝ) - k) := by
  exact mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_abs_iteratedDeriv_pow_exp_le d m k hd hk c)

end BoundaryDraft
