import BoundaryDraft.FinitePoisson

/-!
# Exact Poisson count laws

The void probability is computed from product measures. Reduced Mecke then
gives the count recurrence, and induction identifies every probability with
the pinned mathlib Poisson PMF. No count law is postulated.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

noncomputable section

namespace BoundaryDraft
namespace FinitePoisson

open FiniteConfiguration

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- Exponential generating series for a finite subvolume, including zero. -/
theorem tsum_weight_mul_pow (q : ℝ≥0∞) (hq : q ≠ ∞) :
    (∑' n : ℕ, weight μ n * q ^ n) =
      ENNReal.ofReal (Real.exp (q.toReal - (μ univ).toReal)) := by
  have h (n : ℕ) : weight μ n * q ^ n =
      ENNReal.ofReal (Real.exp (q.toReal - (μ univ).toReal)) * poissonPMF q.toNNReal n := by
    change _ = _ * ENNReal.ofReal (poissonPMFReal q.toNNReal n)
    rw [weight, ← ENNReal.ofReal_toReal hq, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    have he : Real.exp (q.toReal - (μ univ).toReal) * Real.exp (-q.toReal) =
        Real.exp (-(μ univ).toReal) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [div_mul_eq_mul_div, ← mul_div_assoc, ← mul_assoc, he]
  simp_rw [h]
  rw [ENNReal.tsum_mul_left, (poissonPMF q.toNNReal).tsum_coe, mul_one]

theorem count_zero_probability {s : Set α} (hs : MeasurableSet s) :
    law μ {c | count s c = 0} = ENNReal.ofReal (Real.exp (-(μ s).toReal)) := by
  have hm : MeasurableSet {c : Multiset α | count s c = 0} :=
    (measurable_count hs) (measurableSet_singleton 0)
  have hp (n : ℕ) :
      (ofTuple : (Fin n → α) → Multiset α) ⁻¹' {c | count s c = 0} =
      Set.pi univ (fun _ => sᶜ) := by
    ext v
    simp only [mem_preimage, mem_setOf_eq, count_ofTuple, Finset.sum_eq_zero_iff,
      Finset.mem_univ, true_implies, mem_pi, mem_univ, mem_compl_iff]
    simp
  rw [law, Measure.sum_apply _ hm]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_ofTuple _) hm, hp,
    Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [tsum_weight_mul_pow μ _ (measure_ne_top μ _)]
  congr 2
  have h := congrArg ENNReal.toReal (measure_add_measure_compl hs (μ := μ))
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h
  linarith

/-- The measurable test function for the count recurrence. -/
theorem jointMeasurable_count_event {s : Set α} (hs : MeasurableSet s) (k : ℕ) :
    JointMeasurable (fun x c => if x ∈ s ∧ count s c = k then (1 : ℝ≥0∞) else 0) := by
  intro n
  refine Measurable.ite ((hs.preimage measurable_fst).inter ?_) measurable_const measurable_const
  exact (((measurable_count hs).comp (measurable_ofTuple n)).comp measurable_snd)
    (measurableSet_singleton k)

/-- Mecke yields the Poisson recursion for every measurable subset. -/
theorem count_probability_succ {s : Set α} (hs : MeasurableSet s) (k : ℕ) :
    (k + 1 : ℕ) * law μ {c | count s c = k + 1} = μ s * law μ {c | count s c = k} := by
  have h := lintegral_pointSum μ (jointMeasurable_count_event hs k)
  simp_rw [pointSum_count_event] at h
  have hm (j : ℕ) : MeasurableSet {c : Multiset α | count s c = j} :=
    (measurable_count hs) (measurableSet_singleton j)
  have hi (x : α) :
      (∫⁻ c, if x ∈ s ∧ count s c = k then (1 : ℝ≥0∞) else 0 ∂law μ) =
        if x ∈ s then law μ {c | count s c = k} else 0 := by
    by_cases hx : x ∈ s
    · simp only [hx, true_and, if_true]
      simpa only [Set.indicator, mem_setOf_eq, lintegral_const, Measure.restrict_apply_univ,
        one_mul] using (lintegral_indicator (μ := law μ) (hm k) (fun _ => (1 : ℝ≥0∞)))
    · simp [hx]
  simp_rw [hi] at h
  have hl : (∫⁻ c, if count s c = k + 1 then ((k + 1 : ℕ) : ℝ≥0∞) else 0 ∂law μ) =
      (k + 1 : ℕ) * law μ {c | count s c = k + 1} := by
    simpa only [Set.indicator, mem_setOf_eq, lintegral_const, Measure.restrict_apply_univ]
      using (lintegral_indicator (μ := law μ) (hm (k + 1))
        (fun _ => ((k + 1 : ℕ) : ℝ≥0∞)))
  have hr : (∫⁻ x, if x ∈ s then law μ {c | count s c = k} else 0 ∂μ) =
      μ s * law μ {c | count s c = k} :=
    (lintegral_indicator hs (fun _ => law μ {c | count s c = k})).trans (by simp [mul_comm])
  rwa [hl, hr] at h

theorem poissonPMF_succ_mul (r : ℝ≥0∞) (hr : r ≠ ∞) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ≥0∞) * poissonPMF r.toNNReal (k + 1) =
      r * poissonPMF r.toNNReal k := by
  change _ * ENNReal.ofReal (poissonPMFReal r.toNNReal (k + 1)) =
    _ * ENNReal.ofReal (poissonPMFReal r.toNNReal k)
  rw [← ENNReal.ofReal_toReal hr, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  congr 1
  simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (k : ℝ) + 1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Exact count distribution, with intensity equal to the measure of the
counted subset. This includes empty and null sets. -/
theorem count_probability {s : Set α} (hs : MeasurableSet s) (k : ℕ) :
    law μ {c | count s c = k} = poissonPMF (μ s).toNNReal k := by
  induction k with
  | zero =>
    rw [count_zero_probability μ hs]
    change _ = ENNReal.ofReal (poissonPMFReal (μ s).toNNReal 0)
    simp [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal]
  | succ k ih =>
    have h := count_probability_succ μ hs k
    rw [ih] at h
    exact (ENNReal.mul_right_inj (by positivity : ((k + 1 : ℕ) : ℝ≥0∞) ≠ 0)
      (by simp : ((k + 1 : ℕ) : ℝ≥0∞) ≠ ∞)).1
      (h.trans (poissonPMF_succ_mul (μ s) (measure_ne_top μ s) k).symm)

/-- Equality of probability measures, not just individual point masses. -/
theorem map_count {s : Set α} (hs : MeasurableSet s) :
    Measure.map (count s) (law μ) = poissonMeasure (μ s).toNNReal := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_count hs) (measurableSet_singleton k)]
  rw [show count s ⁻¹' {k} = {c | count s c = k} by rfl, count_probability μ hs]
  exact ((poissonPMF (μ s).toNNReal).toMeasure_apply_singleton k (measurableSet_singleton k)).symm

end FinitePoisson
end BoundaryDraft
