import BoundaryDraft.AveragedQuadraticJet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Affine three-halves jets of closing fibres

The second derivative bound may be nonintegrable in the parameter. What is
integrated is the bound times the square root of the fibre cutoff. Both open
and already closed fibres are retained. This proves an affine little-o of
order three-halves, not a uniform quadratic remainder for the average.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TruncatedAffineJet

/-- The equality stratum remains in the open-fibre formula. -/
def truncate (F : ℝ → ℝ) (q σ : ℝ) : ℝ := if σ ≤ q then F σ else 0

theorem rpow_three_halves {s : ℝ} (hs : 0 ≤ s) :
    s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
  calc
    _ = s ^ (1 + (1 / 2 : ℝ)) := by norm_num
    _ = s * Real.sqrt s := by
      rw [Real.rpow_add' hs (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]

/-- The affine residual on a fixed open fibre has a quadratic bound. -/
theorem affine_bound {F F' F'' : ℝ → ℝ} {q B σ : ℝ}
    (hB : 0 ≤ B) (hσ : σ ∈ Ioc 0 q)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc 0 q, HasDerivAt F' (F'' t) t)
    (hsecond : ∀ t ∈ Icc 0 q, |F'' t| ≤ B) :
    |F σ - (F 0 + F' 0 * σ)| ≤ 3 * B * σ ^ 2 := by
  have hb := (div_le_iff₀ (sq_pos_of_pos hσ.1)).mp
    (MonotoneHinge.quadratic_bound hB hσ hF hF' hsecond)
  have hb₀ := hsecond 0 ⟨le_rfl, hσ.1.le.trans hσ.2⟩
  calc
    _ = |(F σ - (F 0 + F' 0 * σ + F'' 0 / 2 * σ ^ 2)) +
        F'' 0 / 2 * σ ^ 2| := by congr 1; ring
    _ ≤ |F σ - (F 0 + F' 0 * σ + F'' 0 / 2 * σ ^ 2)| +
        |F'' 0 / 2 * σ ^ 2| := abs_add _ _
    _ ≤ 2 * B * σ ^ 2 + B / 2 * σ ^ 2 := by
      apply add_le_add hb
      rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg σ)]
      norm_num
      gcongr
    _ ≤ 3 * B * σ ^ 2 := by nlinarith [mul_nonneg hB (sq_nonneg σ)]

/-- Domination includes all fibres closed at this value of the parameter. -/
theorem normalized_remainder_bound {F F' F'' : ℝ → ℝ} {q B σ : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B) (hσ : 0 < σ)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc 0 q, HasDerivAt F' (F'' t) t)
    (hsecond : ∀ t ∈ Icc 0 q, |F'' t| ≤ B)
    (hzero : |F 0| ≤ B * q ^ 2) (hfirst : |F' 0| ≤ B * q) :
    |truncate F q σ - (F 0 + F' 0 * σ)| / σ ^ (3 / 2 : ℝ) ≤
      3 * B * Real.sqrt q := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hσ _)).mpr
  rw [rpow_three_halves hσ.le]
  by_cases hs : σ ≤ q
  · rw [truncate, if_pos hs]
    calc
      _ ≤ 3 * B * σ ^ 2 := affine_bound hB ⟨hσ, hs⟩ hF hF' hsecond
      _ = 3 * B * Real.sqrt σ * (σ * Real.sqrt σ) := by
        calc
          _ = 3 * B * σ * (Real.sqrt σ ^ 2) := by rw [Real.sq_sqrt hσ.le]; ring
          _ = _ := by ring
      _ ≤ 3 * B * Real.sqrt q * (σ * Real.sqrt σ) := by
        gcongr
  · have hqs : q ≤ σ := (lt_of_not_ge hs).le
    have hroot : q ≤ Real.sqrt q * Real.sqrt σ := by
      calc
        q = Real.sqrt q * Real.sqrt q := (Real.mul_self_sqrt hq.le).symm
        _ ≤ Real.sqrt q * Real.sqrt σ := by gcongr
    rw [truncate, if_neg hs, zero_sub, abs_neg]
    calc
      _ ≤ |F 0| + |F' 0 * σ| := abs_add _ _
      _ = |F 0| + |F' 0| * σ := by rw [abs_mul, abs_of_pos hσ]
      _ ≤ B * q ^ 2 + (B * q) * σ := by gcongr
      _ ≤ 2 * B * q * σ := by nlinarith [mul_nonneg hB (mul_nonneg hq.le (sub_nonneg.mpr hqs))]
      _ ≤ 3 * B * q * σ := by nlinarith [mul_nonneg hB (mul_nonneg hq.le hσ.le)]
      _ ≤ 3 * B * Real.sqrt q * (σ * Real.sqrt σ) := by
        calc
          _ ≤ 3 * B * (Real.sqrt q * Real.sqrt σ) * σ := by gcongr
          _ = _ := by ring

/-- For each fixed positive cutoff the quadratic estimate implies the strictly
weaker three-halves little-o. No uniform positive cutoff is required. -/
theorem right_affine_jet {F F' F'' : ℝ → ℝ} {q B : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc 0 q, HasDerivAt F' (F'' t) t)
    (hsecond : ∀ t ∈ Icc 0 q, |F'' t| ≤ B) :
    (fun σ => truncate F q σ - (F 0 + F' 0 * σ)) =o[𝓝[>] 0]
      (fun σ => σ ^ (3 / 2 : ℝ)) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · have hz : Tendsto (fun σ : ℝ => 3 * B * Real.sqrt σ) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds).const_mul (3 * B)
    apply squeeze_zero_norm' _ hz
    filter_upwards [MonotoneHinge.eventually_right hq] with σ hσ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hσ.1 _),
      truncate, if_pos hσ.2]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hσ.1 _)).mpr
    calc
      _ ≤ 3 * B * σ ^ 2 := affine_bound hB hσ hF hF' hsecond
      _ = (3 * B * Real.sqrt σ) * σ ^ (3 / 2 : ℝ) := by
        rw [rpow_three_halves hσ.1.le]
        calc
          _ = 3 * B * σ * (Real.sqrt σ ^ 2) := by rw [Real.sq_sqrt hσ.1.le]; ring
          _ = _ := by ring
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact fun hz => False.elim ((ne_of_gt (Real.rpow_pos_of_pos hσ _)) hz)

/-- Positive probes recover the affine coefficient measurability, without
requiring measurability of a globally uncontrolled derivative. -/
theorem measurable_coefficients
    {α : Type*} [MeasurableSpace α] (F F' F'' : α → ℝ → ℝ) (q : α → ℝ)
    (hq : ∀ a, 0 < q a)
    (hFm : ∀ σ ∈ Ioc (0 : ℝ) 1, Measurable (fun a => truncate (F a) (q a) σ))
    (hF : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F a) (F' a t) t)
    (hF' : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F' a) (F'' a t) t) :
    Measurable (fun a => F a 0) ∧ Measurable (fun a => F' a 0) := by
  have hj (a : α) : (fun σ => truncate (F a) (q a) σ -
      (F a 0 + F' a 0 * σ + F'' a 0 / 2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
    apply (MonotoneHinge.quadratic_peano (hq a) (hF a)
      (hF' a 0 ⟨le_rfl, (hq a).le⟩)).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [MonotoneHinge.eventually_right (hq a)] with σ hσ
    simp only [truncate, if_pos hσ.2]
  have hm := AveragedQuadraticJet.measurable_coefficients_of_right_jet
    (fun a σ => truncate (F a) (q a) σ) (fun a => F a 0) (fun a => F' a 0)
    (fun a => F'' a 0 / 2) zero_lt_one hFm hj
  exact ⟨hm.1, hm.2.1⟩

/-- DCT is applied to the signed normalized residual, after integrability
justifies subtracting the affine polynomial under the integral. -/
theorem averaged_right_affine_jet
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F F' F'' : α → ℝ → ℝ) (q B : α → ℝ)
    (hq : ∀ a, 0 < q a) (hB : ∀ a, 0 ≤ B a)
    (hD : Integrable (fun a => B a * Real.sqrt (q a)) μ)
    (hFm : ∀ σ ∈ Ioc (0 : ℝ) 1, Measurable (fun a => truncate (F a) (q a) σ))
    (hF : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F a) (F' a t) t)
    (hF' : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F' a) (F'' a t) t)
    (hsecond : ∀ a, ∀ t ∈ Icc 0 (q a), |F'' a t| ≤ B a)
    (hzero : ∀ a, |F a 0| ≤ B a * q a ^ 2)
    (hfirst : ∀ a, |F' a 0| ≤ B a * q a)
    (hi₀ : Integrable (fun a => F a 0) μ) (hi₁ : Integrable (fun a => F' a 0) μ) :
    (fun σ => (∫ a, truncate (F a) (q a) σ ∂μ) -
      ((∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ)) =o[𝓝[>] 0]
      (fun σ => σ ^ (3 / 2 : ℝ)) := by
  obtain ⟨hm₀, hm₁⟩ := measurable_coefficients F F' F'' q hq hFm hF hF'
  let E := fun (a : α) σ =>
    (truncate (F a) (q a) σ - (F a 0 + F' a 0 * σ)) / σ ^ (3 / 2 : ℝ)
  let D := fun a => 3 * B a * Real.sqrt (q a)
  have hDi : Integrable D μ := by simpa [D, mul_assoc] using hD.const_mul 3
  have hm (σ : ℝ) (hσ : σ ∈ Ioc 0 1) : Measurable (fun a => E a σ) :=
    ((hFm σ hσ).sub (hm₀.add (hm₁.mul_const σ))).div_const _
  have hb (a : α) {σ : ℝ} (hσ : 0 < σ) : ‖E a σ‖ ≤ D a := by
    change ‖(truncate (F a) (q a) σ - (F a 0 + F' a 0 * σ)) / σ ^ (3 / 2 : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hσ _)]
    exact normalized_remainder_bound (hq a) (hB a) hσ (hF a) (hF' a)
      (hsecond a) (hzero a) (hfirst a)
  have hlim : Tendsto (fun σ => ∫ a, E a σ ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun σ => ∫ a, E a σ ∂μ) (𝓝[>] 0) (𝓝 (∫ _a, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence D ?_ ?_ hDi ?_
      · filter_upwards [MonotoneHinge.eventually_right zero_lt_one] with σ hσ
        exact (hm σ hσ).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact Eventually.of_forall fun a => hb a hσ
      · exact Eventually.of_forall fun a =>
          (right_affine_jet (hq a) (hB a) (hF a) (hF' a) (hsecond a)).tendsto_div_nhds_zero
    simpa only [integral_zero] using hh
  have heq : (fun σ => ((∫ a, truncate (F a) (q a) σ ∂μ) -
      ((∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ)) / σ ^ (3 / 2 : ℝ)) =ᶠ[𝓝[>] 0]
      (fun σ => ∫ a, E a σ ∂μ) := by
    filter_upwards [MonotoneHinge.eventually_right zero_lt_one] with σ hσ
    have hiE : Integrable (fun a => E a σ) μ :=
      hDi.mono' (hm σ hσ).aestronglyMeasurable (Eventually.of_forall fun a => hb a hσ.1)
    have hiP : Integrable (fun a => F a 0 + F' a 0 * σ) μ := hi₀.add (hi₁.mul_const σ)
    have hiF : Integrable (fun a => truncate (F a) (q a) σ) μ := by
      apply ((hiE.mul_const (σ ^ (3 / 2 : ℝ))).add hiP).congr
      filter_upwards with a
      dsimp [E]
      rw [div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hσ.1 _))]
      ring
    dsimp only [E]
    have hP : (∫ a, F a 0 + F' a 0 * σ ∂μ) =
        (∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ := by
      rw [integral_add hi₀ (hi₁.mul_const σ), integral_mul_const]
    rw [integral_div, integral_sub hiF hiP, hP]
  apply (isLittleO_iff_tendsto' ?_).mpr (hlim.congr' heq.symm)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact fun hz => False.elim ((ne_of_gt (Real.rpow_pos_of_pos hσ _)) hz)

end TruncatedAffineJet
end BoundaryDraft
