import BoundaryDraft.TruncatedAffineJet

/-!
# Affine first-order jets of closing fibres

The domination is the second-derivative bound times the fibre cutoff. Neither
that derivative bound alone nor a common positive cutoff is assumed integrable.
This is a dimension-independent analytic lemma, with first-order normalization.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TruncatedLinearJet
open TruncatedAffineJet (truncate affine_bound measurable_coefficients)

/-- Both still-open and already-closed fibres obey the same domination. -/
theorem normalized_remainder_bound {F F' F'' : ℝ → ℝ} {q B σ : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B) (hσ : 0 < σ)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc 0 q, HasDerivAt F' (F'' t) t)
    (hsecond : ∀ t ∈ Icc 0 q, |F'' t| ≤ B)
    (hzero : |F 0| ≤ B * q ^ 2) (hfirst : |F' 0| ≤ B * q) :
    |truncate F q σ - (F 0 + F' 0 * σ)| / σ ≤ 3 * B * q := by
  apply (div_le_iff₀ hσ).mpr
  by_cases hs : σ ≤ q
  · rw [truncate, if_pos hs]
    calc
      _ ≤ 3 * B * σ ^ 2 := affine_bound hB ⟨hσ, hs⟩ hF hF' hsecond
      _ ≤ 3 * B * q * σ := by nlinarith [mul_nonneg hB (mul_nonneg hσ.le (sub_nonneg.mpr hs))]
  · have hqs : q ≤ σ := (lt_of_not_ge hs).le
    rw [truncate, if_neg hs, zero_sub, abs_neg]
    calc
      _ ≤ |F 0| + |F' 0 * σ| := abs_add _ _
      _ = |F 0| + |F' 0| * σ := by rw [abs_mul, abs_of_pos hσ]
      _ ≤ B * q ^ 2 + (B * q) * σ := by gcongr
      _ ≤ 3 * B * q * σ := by
        nlinarith [mul_nonneg hB (mul_nonneg hq.le (sub_nonneg.mpr hqs)),
          mul_nonneg hB (mul_nonneg hq.le hσ.le)]

theorem right_linear_jet {F F' F'' : ℝ → ℝ} {q B : ℝ}
    (hq : 0 < q) (hB : 0 ≤ B)
    (hF : ∀ t ∈ Icc 0 q, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Icc 0 q, HasDerivAt F' (F'' t) t)
    (hsecond : ∀ t ∈ Icc 0 q, |F'' t| ≤ B) :
    (fun σ => truncate F q σ - (F 0 + F' 0 * σ)) =o[𝓝[>] 0] (fun σ => σ) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · have hz : Tendsto (fun σ : ℝ => 3 * B * σ) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0)).const_mul (3 * B)
    apply squeeze_zero_norm' _ hz
    filter_upwards [MonotoneHinge.eventually_right hq] with σ hσ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hσ.1, truncate, if_pos hσ.2]
    apply (div_le_iff₀ hσ.1).mpr
    simpa only [pow_two, mul_assoc] using affine_bound hB hσ hF hF' hsecond
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact fun hz => False.elim ((ne_of_gt hσ) hz)

/-- Signed DCT is used only after absolute integrability permits subtracting
and averaging the affine polynomial. -/
theorem averaged_right_linear_jet
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F F' F'' : α → ℝ → ℝ) (q B : α → ℝ)
    (hq : ∀ a, 0 < q a) (hB : ∀ a, 0 ≤ B a)
    (hD : Integrable (fun a => B a * q a) μ)
    (hFm : ∀ σ ∈ Ioc (0 : ℝ) 1, Measurable (fun a => truncate (F a) (q a) σ))
    (hF : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F a) (F' a t) t)
    (hF' : ∀ a, ∀ t ∈ Icc 0 (q a), HasDerivAt (F' a) (F'' a t) t)
    (hsecond : ∀ a, ∀ t ∈ Icc 0 (q a), |F'' a t| ≤ B a)
    (hzero : ∀ a, |F a 0| ≤ B a * q a ^ 2)
    (hfirst : ∀ a, |F' a 0| ≤ B a * q a)
    (hi₀ : Integrable (fun a => F a 0) μ) (hi₁ : Integrable (fun a => F' a 0) μ) :
    (fun σ => (∫ a, truncate (F a) (q a) σ ∂μ) -
      ((∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ)) =o[𝓝[>] 0] (fun σ => σ) := by
  obtain ⟨hm₀, hm₁⟩ := measurable_coefficients F F' F'' q hq hFm hF hF'
  let E := fun (a : α) σ => (truncate (F a) (q a) σ - (F a 0 + F' a 0 * σ)) / σ
  let D := fun a => 3 * B a * q a
  have hDi : Integrable D μ := by simpa [D, mul_assoc] using hD.const_mul 3
  have hm (σ : ℝ) (hσ : σ ∈ Ioc 0 1) : Measurable (fun a => E a σ) :=
    ((hFm σ hσ).sub (hm₀.add (hm₁.mul_const σ))).div_const _
  have hb (a : α) {σ : ℝ} (hσ : 0 < σ) : ‖E a σ‖ ≤ D a := by
    change ‖(truncate (F a) (q a) σ - (F a 0 + F' a 0 * σ)) / σ‖ ≤ _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hσ]
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
          (right_linear_jet (hq a) (hB a) (hF a) (hF' a) (hsecond a)).tendsto_div_nhds_zero
    simpa only [integral_zero] using hh
  have heq : (fun σ => ((∫ a, truncate (F a) (q a) σ ∂μ) -
      ((∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ)) / σ) =ᶠ[𝓝[>] 0]
      (fun σ => ∫ a, E a σ ∂μ) := by
    filter_upwards [MonotoneHinge.eventually_right zero_lt_one] with σ hσ
    have hiE : Integrable (fun a => E a σ) μ :=
      hDi.mono' (hm σ hσ).aestronglyMeasurable (Eventually.of_forall fun a => hb a hσ.1)
    have hiP : Integrable (fun a => F a 0 + F' a 0 * σ) μ := hi₀.add (hi₁.mul_const σ)
    have hiF : Integrable (fun a => truncate (F a) (q a) σ) μ := by
      apply ((hiE.mul_const σ).add hiP).congr
      filter_upwards with a
      dsimp [E]
      rw [div_mul_cancel₀ _ hσ.1.ne']
      ring
    dsimp only [E]
    have hP : (∫ a, F a 0 + F' a 0 * σ ∂μ) =
        (∫ a, F a 0 ∂μ) + (∫ a, F' a 0 ∂μ) * σ := by
      rw [integral_add hi₀ (hi₁.mul_const σ), integral_mul_const]
    rw [integral_div, integral_sub hiF hiP, hP]
  apply (isLittleO_iff_tendsto' ?_).mpr (hlim.congr' heq.symm)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact fun hz => False.elim ((ne_of_gt hσ) hz)

end TruncatedLinearJet
end BoundaryDraft
