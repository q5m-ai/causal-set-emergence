import BoundaryDraft.MonotoneHingeIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Averaging pointwise right quadratic jets

This module is geometry-independent.  It averages the normalized remainder,
not a purported uniform little-o estimate.  In particular the quadratic
coefficient may jump on a parameter-space contact locus, and that locus need
not be null.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval

noncomputable section
namespace BoundaryDraft
namespace AveragedQuadraticJet

variable {𝒜 : Type*} [MeasurableSpace 𝒜] {μ : Measure 𝒜}

/-- The normalized remainder used for dominated convergence. -/
def normalizedRemainder (F : 𝒜 → ℝ → ℝ) (C0 C1 C2 : 𝒜 → ℝ) (α : 𝒜) (σ : ℝ) : ℝ :=
  (F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)) / σ ^ 2

/-- Domination of the normalized remainder makes each sufficiently small
positive fibre integrable.  This is needed before polynomial subtraction is
moved through the integral. -/
theorem integrable_fibre_of_mem_Ioc
    (F : 𝒜 → ℝ → ℝ) (C0 C1 C2 D : 𝒜 → ℝ) {ε σ : ℝ}
    (hσ : σ ∈ Ioc 0 ε)
    (hF : Measurable fun α => F α σ)
    (hC0m : Measurable C0) (hC1m : Measurable C1) (hC2m : Measurable C2)
    (hC0 : Integrable C0 μ) (hC1 : Integrable C1 μ) (hC2 : Integrable C2 μ)
    (hD : Integrable D μ)
    (hbound : ∀ α, |F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)| / σ ^ 2 ≤ D α) :
    Integrable (fun α => F α σ) μ := by
  let R : 𝒜 → ℝ := fun α => F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)
  have hRm : Measurable R := by
    dsimp [R]
    fun_prop
  have hRi : Integrable R μ := by
    apply (hD.const_mul (σ ^ 2)).mono' hRm.aestronglyMeasurable
    filter_upwards with α
    have hs : 0 < σ ^ 2 := sq_pos_of_pos hσ.1
    have hb := (div_le_iff₀ hs).mp (hbound α)
    change |R α| ≤ σ ^ 2 * D α
    dsimp [R]
    nlinarith
  have hpoly : Integrable (fun α => C0 α + C1 α * σ + C2 α * σ ^ 2) μ :=
    (hC0.add (hC1.mul_const σ)).add (hC2.mul_const (σ ^ 2))
  apply (hRi.add hpoly).congr
  filter_upwards with α
  dsimp [R]
  ring

/-- For every small positive parameter, integration commutes with normalized
polynomial subtraction. -/
theorem integral_normalizedRemainder
    (F : 𝒜 → ℝ → ℝ) (C0 C1 C2 D : 𝒜 → ℝ) {ε σ : ℝ}
    (hσ : σ ∈ Ioc 0 ε)
    (hF : Measurable fun α => F α σ)
    (hC0m : Measurable C0) (hC1m : Measurable C1) (hC2m : Measurable C2)
    (hC0 : Integrable C0 μ) (hC1 : Integrable C1 μ) (hC2 : Integrable C2 μ)
    (hD : Integrable D μ)
    (hbound : ∀ α, |F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)| / σ ^ 2 ≤ D α) :
    (((∫ α, F α σ ∂μ) -
      ((∫ α, C0 α ∂μ) + (∫ α, C1 α ∂μ) * σ + (∫ α, C2 α ∂μ) * σ ^ 2)) /
        σ ^ 2) = ∫ α, normalizedRemainder F C0 C1 C2 α σ ∂μ := by
  have hFi := integrable_fibre_of_mem_Ioc F C0 C1 C2 D hσ hF hC0m hC1m hC2m
    hC0 hC1 hC2 hD hbound
  have hC1σ := hC1.mul_const σ
  have hC2σ := hC2.mul_const (σ ^ 2)
  have hpoly : Integrable (fun α => (C0 α + C1 α * σ) + C2 α * σ ^ 2) μ :=
    (hC0.add hC1σ).add hC2σ
  have h01 : (∫ α, C0 α + C1 α * σ ∂μ) =
      (∫ α, C0 α ∂μ) + (∫ α, C1 α * σ ∂μ) := by
    simpa only [Pi.add_apply] using integral_add hC0 hC1σ
  have h012 : (∫ α, (C0 α + C1 α * σ) + C2 α * σ ^ 2 ∂μ) =
      (∫ α, C0 α + C1 α * σ ∂μ) + (∫ α, C2 α * σ ^ 2 ∂μ) := by
    simpa only [Pi.add_apply] using integral_add (hC0.add hC1σ) hC2σ
  have hpoly_integral : (∫ α, C0 α + C1 α * σ + C2 α * σ ^ 2 ∂μ) =
      (∫ α, C0 α ∂μ) + (∫ α, C1 α ∂μ) * σ + (∫ α, C2 α ∂μ) * σ ^ 2 := by
    rw [h012, h01, integral_mul_const, integral_mul_const]
  unfold normalizedRemainder
  rw [integral_div, integral_sub hFi hpoly, hpoly_integral]

/-- Dominated convergence for normalized remainders transports pointwise
right quadratic jets to the averaged right quadratic jet.  The measure is
arbitrary: finiteness is not assumed, only integrability of the supplied
parameter-dependent dominator. -/
theorem averaged_right_quadratic_jet
    (F : 𝒜 → ℝ → ℝ) (C0 C1 C2 D : 𝒜 → ℝ) {ε : ℝ}
    (hε : 0 < ε)
    (hjet : ∀ α,
      (fun σ => F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)) =o[𝓝[>] 0]
        (fun σ => σ ^ 2))
    (hbound : ∀ α, ∀ σ ∈ Ioc 0 ε,
      |F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)| / σ ^ 2 ≤ D α)
    (hD0 : ∀ α, 0 ≤ D α) (hD : Integrable D μ)
    (hF : ∀ σ ∈ Ioc 0 ε, Measurable fun α => F α σ)
    (hC0m : Measurable C0) (hC1m : Measurable C1) (hC2m : Measurable C2)
    (hC0 : Integrable C0 μ) (hC1 : Integrable C1 μ) (hC2 : Integrable C2 μ) :
    (fun σ =>
      (∫ α, F α σ ∂μ) -
        ((∫ α, C0 α ∂μ) + (∫ α, C1 α ∂μ) * σ +
          (∫ α, C2 α ∂μ) * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  have hlim : Tendsto (fun σ => ∫ α, normalizedRemainder F C0 C1 C2 α σ ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    have hdc : Tendsto (fun σ => ∫ α, normalizedRemainder F C0 C1 C2 α σ ∂μ)
        (𝓝[>] 0) (𝓝 (∫ _α, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence D ?_ ?_ hD ?_
      · filter_upwards [MonotoneHinge.eventually_right hε] with σ hσ
        simpa [normalizedRemainder] using
          (((hF σ hσ).sub
            ((hC0m.add (hC1m.mul_const σ)).add (hC2m.mul_const (σ ^ 2)))).div_const
              (σ ^ 2)).aestronglyMeasurable
      · filter_upwards [MonotoneHinge.eventually_right hε] with σ hσ
        filter_upwards with α
        rw [normalizedRemainder, Real.norm_eq_abs, abs_div,
          abs_of_nonneg (sq_nonneg σ)]
        have _hD0 := hD0 α
        exact hbound α σ hσ
      · filter_upwards with α
        simpa [normalizedRemainder] using (hjet α).tendsto_div_nhds_zero
    simpa only [integral_zero] using hdc
  have heq : (fun σ =>
      ((∫ α, F α σ ∂μ) -
        ((∫ α, C0 α ∂μ) + (∫ α, C1 α ∂μ) * σ +
          (∫ α, C2 α ∂μ) * σ ^ 2)) / σ ^ 2) =ᶠ[𝓝[>] 0]
      (fun σ => ∫ α, normalizedRemainder F C0 C1 C2 α σ ∂μ) := by
    filter_upwards [MonotoneHinge.eventually_right hε] with σ hσ
    exact integral_normalizedRemainder F C0 C1 C2 D hσ (hF σ hσ)
      hC0m hC1m hC2m hC0 hC1 hC2 hD (hbound · σ hσ)
  apply (isLittleO_iff_tendsto' ?_).mpr (hlim.congr' heq.symm)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact fun hz => False.elim ((pow_ne_zero 2 (ne_of_gt hσ)) hz)

/-! ## Measurability of coefficients from fixed positive quotients -/

private def probe (ε : ℝ) (n : ℕ) : ℝ := ε * (1 / ((n : ℝ) + 1))

private theorem probe_mem_Ioc {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    probe ε n ∈ Ioc 0 ε := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hunit : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn]
    norm_num
  change 0 < ε * (1 / ((n : ℝ) + 1)) ∧ ε * (1 / ((n : ℝ) + 1)) ≤ ε
  exact ⟨mul_pos hε (one_div_pos.mpr hn), by simpa using (mul_le_mul_left hε).2 hunit⟩

private theorem probe_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (probe ε) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · change Tendsto (fun n : ℕ => ε * (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
    simpa using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => ε * (1 / ((n : ℝ) + 1))) atTop (𝓝 (ε * 0)))
  · exact Eventually.of_forall fun n => (probe_mem_Ioc hε n).1

/-- Measurability of all three coefficients follows from measurable fibres on
one common right interval and the pointwise quadratic jets.  The proof uses a
single fixed positive sequence, so it performs no measurable root selection. -/
theorem measurable_coefficients_of_right_jet
    (F : 𝒜 → ℝ → ℝ) (C0 C1 C2 : 𝒜 → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hF : ∀ σ ∈ Ioc 0 ε, Measurable fun α => F α σ)
    (hjet : ∀ α,
      (fun σ => F α σ - (C0 α + C1 α * σ + C2 α * σ ^ 2)) =o[𝓝[>] 0]
        (fun σ => σ ^ 2)) :
    Measurable C0 ∧ Measurable C1 ∧ Measurable C2 := by
  let s := probe ε
  have hs : Tendsto s atTop (𝓝[>] 0) := probe_tendsto hε
  have hsm (n : ℕ) : Measurable fun α => F α (s n) := hF _ (probe_mem_Ioc hε n)
  have hR (α : 𝒜) : Tendsto (fun σ => normalizedRemainder F C0 C1 C2 α σ)
      (𝓝[>] 0) (𝓝 0) := (hjet α).tendsto_div_nhds_zero
  have hF0 (α : 𝒜) : Tendsto (fun n => F α (s n)) atTop (𝓝 (C0 α)) := by
    have hr := (hR α).comp hs
    have hs0 : Tendsto s atTop (𝓝 0) := hs.mono_right inf_le_left
    have he : ∀ n, F α (s n) = C0 α + C1 α * s n + C2 α * s n ^ 2 +
        s n ^ 2 * normalizedRemainder F C0 C1 C2 α (s n) := by
      intro n
      have hsne : s n ≠ 0 := (probe_mem_Ioc hε n).1.ne'
      unfold normalizedRemainder
      field_simp [hsne]
    have ht : Tendsto (fun n => C0 α + (C1 α * s n +
        (C2 α * s n ^ 2 + s n ^ 2 * normalizedRemainder F C0 C1 C2 α (s n))))
        atTop (𝓝 (C0 α)) := by
      convert tendsto_const_nhds.add ((tendsto_const_nhds.mul hs0).add
        ((tendsto_const_nhds.mul (hs0.pow 2)).add ((hs0.pow 2).mul hr))) using 1
      all_goals simp [Function.comp_apply]
    apply ht.congr'
    exact Eventually.of_forall fun n => by simpa only [add_assoc] using (he n).symm
  have hC0 : Measurable C0 := measurable_of_tendsto_metrizable hsm
    (tendsto_pi_nhds.2 hF0)
  have hF1 (α : 𝒜) : Tendsto (fun n => (F α (s n) - C0 α) / s n) atTop
      (𝓝 (C1 α)) := by
    have hr := (hR α).comp hs
    have hs0 : Tendsto s atTop (𝓝 0) := hs.mono_right inf_le_left
    have he : ∀ n, (F α (s n) - C0 α) / s n =
        C1 α + C2 α * s n + s n * normalizedRemainder F C0 C1 C2 α (s n) := by
      intro n
      have hsne : s n ≠ 0 := (probe_mem_Ioc hε n).1.ne'
      unfold normalizedRemainder
      field_simp [hsne]
      ring
    have ht : Tendsto (fun n => C1 α + (C2 α * s n +
        s n * normalizedRemainder F C0 C1 C2 α (s n))) atTop (𝓝 (C1 α)) := by
      convert tendsto_const_nhds.add ((tendsto_const_nhds.mul hs0).add
        (hs0.mul hr)) using 1
      all_goals simp [Function.comp_apply]
    apply ht.congr'
    exact Eventually.of_forall fun n => by simpa only [add_assoc] using (he n).symm
  have hC1 : Measurable C1 := measurable_of_tendsto_metrizable
    (fun n => ((hsm n).sub hC0).div_const (s n)) (tendsto_pi_nhds.2 hF1)
  have hF2 (α : 𝒜) : Tendsto
      (fun n => (F α (s n) - C0 α - C1 α * s n) / s n ^ 2) atTop
      (𝓝 (C2 α)) := by
    have hr := (hR α).comp hs
    have he : ∀ n, (F α (s n) - C0 α - C1 α * s n) / s n ^ 2 =
        C2 α + normalizedRemainder F C0 C1 C2 α (s n) := by
      intro n
      have hsne : s n ≠ 0 := (probe_mem_Ioc hε n).1.ne'
      unfold normalizedRemainder
      field_simp [hsne]
      ring
    have ht : Tendsto (fun n => C2 α +
        normalizedRemainder F C0 C1 C2 α (s n)) atTop (𝓝 (C2 α)) := by
      convert tendsto_const_nhds.add hr using 1
      all_goals simp [Function.comp_apply]
    apply ht.congr'
    exact Eventually.of_forall fun n => (he n).symm
  exact ⟨hC0, hC1, measurable_of_tendsto_metrizable
    (fun n => (((hsm n).sub hC0).sub (hC1.mul_const (s n))).div_const (s n ^ 2))
    (tendsto_pi_nhds.2 hF2)⟩

end AveragedQuadraticJet

namespace MonotoneHinge

variable {𝒜 : Type*} [MeasurableSpace 𝒜] [Nonempty 𝒜] {μ : Measure 𝒜}
variable {g J : 𝒜 → ℝ → ℝ → ℝ} {δ V ε c A M B : ℝ}

/-- The parameter functions used by the averaging theorem, exposed without
copying any part of the fibre theorem. -/
def parameterFibre (g J : 𝒜 → ℝ → ℝ → ℝ) (δ V : ℝ) (α : 𝒜) (σ : ℝ) : ℝ :=
  fibre (g α) (J α) δ V σ

def parameterF0 (g J : 𝒜 → ℝ → ℝ → ℝ) (δ V : ℝ) (α : 𝒜) : ℝ :=
  F0 (g α) (J α) δ V

def parameterF1 (g J : 𝒜 → ℝ → ℝ → ℝ) (δ V : ℝ) (α : 𝒜) : ℝ :=
  F1 (g α) (J α) δ V

def parameterF2 (g J : 𝒜 → ℝ → ℝ → ℝ) (δ V : ℝ) (α : 𝒜) : ℝ :=
  F2 (g α) (J α) δ V

/-- A common monotone-hinge family averages on any measure for which the
constant fibre bound is integrable.  Coefficient measurability is derived from
measurable fibres and the already-proved pointwise jets; coefficient
integrability remains an explicit premise. -/
theorem averaged_right_quadratic_jet
    (h : ∀ α, Hypotheses (g α) (J α) δ V ε c A M B)
    (hF : ∀ σ ∈ Ioc 0 ε, Measurable fun α => parameterFibre g J δ V α σ)
    (hC0 : Integrable (parameterF0 g J δ V) μ)
    (hC1 : Integrable (parameterF1 g J δ V) μ)
    (hC2 : Integrable (parameterF2 g J δ V) μ)
    (hD : Integrable (fun _α : 𝒜 => remainderBound δ V c A M B) μ) :
    (fun σ =>
      (∫ α, parameterFibre g J δ V α σ ∂μ) -
        ((∫ α, parameterF0 g J δ V α ∂μ) +
          (∫ α, parameterF1 g J δ V α ∂μ) * σ +
          (∫ α, parameterF2 g J δ V α ∂μ) * σ ^ 2)) =o[𝓝[>] 0]
      (fun σ => σ ^ 2) := by
  have hε : 0 < ε := (h (Classical.choice inferInstance)).epsilon_pos
  have hj (α : 𝒜) := (h α).right_quadratic_jet
  have hm := AveragedQuadraticJet.measurable_coefficients_of_right_jet
    (parameterFibre g J δ V) (parameterF0 g J δ V) (parameterF1 g J δ V)
      (parameterF2 g J δ V) hε hF hj
  apply AveragedQuadraticJet.averaged_right_quadratic_jet
    (parameterFibre g J δ V) (parameterF0 g J δ V) (parameterF1 g J δ V)
      (parameterF2 g J δ V) (fun _α => remainderBound δ V c A M B) hε hj
  · intro α σ hσ
    exact (h α).normalized_remainder_bound hσ
  · intro _α
    have h₀ := h (Classical.choice inferInstance)
    unfold remainderBound
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) h₀.second_nonneg)
        (sub_nonneg.mpr h₀.cutoff_lt.le))
      (mul_nonneg (by norm_num)
        (div_nonneg (mul_nonneg h₀.weight_nonneg (sq_nonneg A)) h₀.transverse_pos.le))
  · exact hD
  · exact hF
  · exact hm.1
  · exact hm.2.1
  · exact hm.2.2
  · exact hC0
  · exact hC1
  · exact hC2

end MonotoneHinge
end BoundaryDraft
