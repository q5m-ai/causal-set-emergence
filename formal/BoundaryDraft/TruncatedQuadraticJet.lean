import BoundaryDraft.AveragedQuadraticJet

/-!
# Right quadratic jets with a parameter-dependent closing cutoff

A fibre is smooth up to its own positive cutoff and identically zero beyond it.
Its value and first two Taylor coefficients scale with that cutoff. These
primitive derivative bounds give a normalized-remainder bound on the entire
positive half-line, even after a fibre has closed. Averaging therefore requires
no uniform lower bound on the cutoffs. The short-cone lower endpoint has exactly
this form, with cutoff equal to the square of the long null coordinate.

This is an analytic lemma, not a premise added to geometric admissibility.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TruncatedQuadraticJet

/-- Retain the moving equality stratum. Its value is immaterial for averaging,
but the pointwise identities below do not discard it. -/
def truncate (F : ℝ → ℝ) (q σ : ℝ) : ℝ := if σ ≤ q then F σ else 0

/-- The cutoff may be arbitrarily small. The bound does not divide by it. -/
theorem normalized_remainder_bound {F F' F'' : ℝ → ℝ} {q B σ : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B) (hσ : 0 < σ)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc 0 q, HasDerivAt F' (F'' t) t)
    (hsecond : ∀ t ∈ Icc 0 q, |F'' t| ≤ B)
    (hzero : |F 0| ≤ B * q ^ 2)
    (hfirst : |F' 0| ≤ B * q) :
    |truncate F q σ - (F 0 + F' 0 * σ + F'' 0 / 2 * σ ^ 2)| / σ ^ 2 ≤ 3 * B := by
  by_cases hsq : σ ≤ q
  · rw [truncate, if_pos hsq]
    exact (MonotoneHinge.quadratic_bound hB ⟨hσ, hsq⟩ hF hF' hsecond).trans (by linarith)
  · have hqs : q < σ := lt_of_not_ge hsq
    rw [truncate, if_neg hsq, zero_sub, abs_neg]
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    have hsecond0 := hsecond 0 ⟨le_rfl, hq.le⟩
    have hq2 : q ^ 2 ≤ σ ^ 2 := by nlinarith
    calc
      _ ≤ |F 0| + |F' 0 * σ| + |F'' 0 / 2 * σ ^ 2| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ = |F 0| + |F' 0| * σ + |F'' 0| / 2 * σ ^ 2 := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hσ, abs_of_nonneg (sq_nonneg σ)]
        norm_num
      _ ≤ B * q ^ 2 + (B * q) * σ + B / 2 * σ ^ 2 := by gcongr
      _ ≤ B * σ ^ 2 + (B * σ) * σ + B / 2 * σ ^ 2 := by gcongr
      _ ≤ 3 * B * σ ^ 2 := by nlinarith [mul_nonneg hB (sq_nonneg σ)]

/-- At each fixed fibre the positive cutoff is eventually inactive. No common
positive cutoff is required across the parameter space. -/
theorem right_quadratic_jet {F F' : ℝ → ℝ} {q b : ℝ} (hq : 0 < q)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : HasDerivAt F' b 0) :
    (fun σ => truncate F q σ - (F 0 + F' 0 * σ + b / 2 * σ ^ 2)) =o[𝓝[>] 0]
      (fun σ => σ ^ 2) := by
  apply (MonotoneHinge.quadratic_peano hq hF hF').congr' _ Filter.EventuallyEq.rfl
  filter_upwards [MonotoneHinge.eventually_right hq] with σ hσ
  simp only [truncate, if_pos hσ.2]

/-- Averaging the closed fibres preserves a right quadratic jet. Coefficient
measurability is recovered from positive probes and integrability from the
primitive bounds. In particular a common positive lower cutoff is not assumed. -/
theorem averaged_right_quadratic_jet
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F F' F'' : α → ℝ → ℝ) (q B : α → ℝ) {Q : ℝ}
    (hq : ∀ a, 0 < q a ∧ q a ≤ Q)
    (hB : ∀ a, 0 ≤ B a) (hBi : Integrable B μ)
    (hFm : ∀ σ ∈ Ioc (0 : ℝ) 1, Measurable (fun a => truncate (F a) (q a) σ))
    (hF : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F a) (F' a t) t)
    (hF' : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F' a) (F'' a t) t)
    (hsecond : ∀ a, ∀ t ∈ Icc 0 (q a), |F'' a t| ≤ B a)
    (hzero : ∀ a, |F a 0| ≤ B a * q a ^ 2)
    (hfirst : ∀ a, |F' a 0| ≤ B a * q a) :
    (fun σ => (∫ a, truncate (F a) (q a) σ ∂μ) -
      ((∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ +
        (∫ a, F'' a 0 / 2 ∂μ) * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  have hj (a : α) := right_quadratic_jet (hq a).1 (hF a)
    (hF' a 0 ⟨le_rfl, (hq a).1.le⟩)
  have hm := AveragedQuadraticJet.measurable_coefficients_of_right_jet
    (fun a σ => truncate (F a) (q a) σ) (fun a => F a 0) (fun a => F' a 0)
    (fun a => F'' a 0 / 2) zero_lt_one hFm hj
  have hi₀ : Integrable (fun a => F a 0) μ := by
    apply (hBi.mul_const (Q ^ 2)).mono' hm.1.aestronglyMeasurable
    filter_upwards with a
    change |F a 0| ≤ B a * Q ^ 2
    exact (hzero a).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hq a).1.le (hq a).2 2) (hB a))
  have hi₁ : Integrable (fun a => F' a 0) μ := by
    apply (hBi.mul_const Q).mono' hm.2.1.aestronglyMeasurable
    filter_upwards with a
    change |F' a 0| ≤ B a * Q
    exact (hfirst a).trans (mul_le_mul_of_nonneg_left (hq a).2 (hB a))
  have hi₂ : Integrable (fun a => F'' a 0 / 2) μ := by
    apply (hBi.div_const 2).mono' hm.2.2.aestronglyMeasurable
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (hsecond a 0 ⟨le_rfl, (hq a).1.le⟩) (by norm_num)
  apply AveragedQuadraticJet.averaged_right_quadratic_jet
    (fun a σ => truncate (F a) (q a) σ) (fun a => F a 0) (fun a => F' a 0)
    (fun a => F'' a 0 / 2) (fun a => 3 * B a) zero_lt_one hj
  · intro a σ hσ
    exact normalized_remainder_bound (hq a).1 (hB a) hσ.1 (hF a) (hF' a)
      (hsecond a) (hzero a) (hfirst a)
  · exact fun a => mul_nonneg (by norm_num) (hB a)
  · exact hBi.const_mul 3
  · exact hFm
  · exact hm.1
  · exact hm.2.1
  · exact hm.2.2
  · exact hi₀
  · exact hi₁
  · exact hi₂

end TruncatedQuadraticJet
end BoundaryDraft
