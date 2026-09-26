import BoundaryDraft.PoissonCounts

/-! # Joint count law on two disjoint measurable pieces -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Classical

noncomputable section

namespace BoundaryDraft

namespace FiniteConfiguration

variable {α : Type*}

theorem pointSum_joint_count_event {s t : Set α} (hst : Disjoint s t)
    (k l : ℕ) (c : Multiset α) :
    pointSum (fun x r => if x ∈ s ∧ count s r = k ∧ count t r = l
      then (1 : ℝ≥0∞) else 0) c =
      if count s c = k + 1 ∧ count t c = l then ((k + 1 : ℕ) : ℝ≥0∞) else 0 := by
  classical
  have hc (u : Set α) (x : α) (hx : x ∈ c) :
      count u c = count u (c.erase x) + if x ∈ u then 1 else 0 := by
    rw [← count_cons, Multiset.cons_erase hx]
  have he (x : α) (hx : x ∈ c) (hxs : x ∈ s) : count t (c.erase x) = count t c := by
    have hxt : x ∉ t := fun h => Set.disjoint_left.1 hst hxs h
    simpa [hxt] using (hc t x hx).symm
  by_cases hk : count s c = k + 1 ∧ count t c = l
  · rw [if_pos hk, ← hk.1, count_eq_sum, pointSum]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    have h := hc s x hx
    by_cases hxs : x ∈ s
    · simp_all
    · simp [hxs]
  · rw [if_neg hk, pointSum]
    apply Multiset.sum_eq_zero
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 ha
    have h := hc s x hx
    by_cases hxs : x ∈ s
    · simp only [hxs, if_true, add_left_inj] at h
      have ht := he x hx hxs
      have hn : ¬(count s (c.erase x) = k ∧ count t (c.erase x) = l) := by
        intro hh
        exact hk ⟨by omega, by omega⟩
      simp [hxs, hn]
    · simp [hxs]

end FiniteConfiguration

namespace FinitePoisson

open FiniteConfiguration

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

theorem joint_count_probability_succ {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) (k l : ℕ) :
    ((k + 1 : ℕ) : ℝ≥0∞) * law μ {c | count s c = k + 1 ∧ count t c = l} =
      μ s * law μ {c | count s c = k ∧ count t c = l} := by
  have hm (i j : ℕ) : MeasurableSet {c : Multiset α | count s c = i ∧ count t c = j} :=
    ((measurable_count hs) (measurableSet_singleton i)).inter
      ((measurable_count ht) (measurableSet_singleton j))
  have hF : JointMeasurable (fun x c => if x ∈ s ∧ count s c = k ∧ count t c = l
      then (1 : ℝ≥0∞) else 0) := by
    intro n
    exact Measurable.ite ((hs.preimage measurable_fst).inter
      ((hm k l).preimage ((measurable_ofTuple n).comp measurable_snd)))
      measurable_const measurable_const
  have h := lintegral_pointSum μ hF
  simp_rw [pointSum_joint_count_event hst] at h
  have hi (x : α) :
      (∫⁻ c, if x ∈ s ∧ count s c = k ∧ count t c = l then (1 : ℝ≥0∞) else 0 ∂law μ) =
        if x ∈ s then law μ {c | count s c = k ∧ count t c = l} else 0 := by
    by_cases hx : x ∈ s
    · simp only [hx, true_and, if_true]
      simpa only [Set.indicator, mem_setOf_eq, lintegral_const, Measure.restrict_apply_univ,
        one_mul] using (lintegral_indicator (μ := law μ) (hm k l) (fun _ => (1 : ℝ≥0∞)))
    · simp [hx]
  simp_rw [hi] at h
  have hl : (∫⁻ c, if count s c = k + 1 ∧ count t c = l then ((k + 1 : ℕ) : ℝ≥0∞)
      else 0 ∂law μ) = ((k + 1 : ℕ) : ℝ≥0∞) * law μ {c | count s c = k + 1 ∧ count t c = l} := by
    simpa only [Set.indicator, mem_setOf_eq, lintegral_const, Measure.restrict_apply_univ]
      using (lintegral_indicator (μ := law μ) (hm (k + 1) l)
        (fun _ => ((k + 1 : ℕ) : ℝ≥0∞)))
  have hr : (∫⁻ x, if x ∈ s then law μ {c | count s c = k ∧ count t c = l} else 0 ∂μ) =
      μ s * law μ {c | count s c = k ∧ count t c = l} :=
    (lintegral_indicator hs (fun _ => law μ {c | count s c = k ∧ count t c = l})).trans
      (by simp [mul_comm])
  rwa [hl, hr] at h

/-- Counts on disjoint pieces have the product Poisson PMF, including when
one or both pieces have zero intensity. -/
theorem joint_count_probability {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) (k l : ℕ) :
    law μ {c | count s c = k ∧ count t c = l} =
      poissonPMF (μ s).toNNReal k * poissonPMF (μ t).toNNReal l := by
  have hzero : law μ {c | count s c = 0 ∧ count t c = 0} =
      poissonPMF (μ s).toNNReal 0 * poissonPMF (μ t).toNNReal 0 := by
    rw [show {c | count s c = 0 ∧ count t c = 0} = {c | count (s ∪ t) c = 0} by
      ext c; simp [count_disjoint_union hst]]
    rw [count_zero_probability μ (hs.union ht), measure_union hst ht,
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
    change _ = ENNReal.ofReal (poissonPMFReal (μ s).toNNReal 0) *
      ENNReal.ofReal (poissonPMFReal (μ t).toNNReal 0)
    simp only [poissonPMFReal, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one,
      ENNReal.coe_toNNReal_eq_toReal]
    rw [neg_add, Real.exp_add, ENNReal.ofReal_mul (by positivity)]
  have hz (j : ℕ) : law μ {c | count s c = 0 ∧ count t c = j} =
      poissonPMF (μ s).toNNReal 0 * poissonPMF (μ t).toNNReal j := by
    induction j with
    | zero => exact hzero
    | succ j ih =>
      apply (ENNReal.mul_right_inj (by positivity : ((j + 1 : ℕ) : ℝ≥0∞) ≠ 0)
        (by simp : ((j + 1 : ℕ) : ℝ≥0∞) ≠ ∞)).1
      have hr := joint_count_probability_succ μ ht hs hst.symm j 0
      simp only [and_comm] at hr
      rw [hr, ih]
      calc
        _ = poissonPMF (μ s).toNNReal 0 *
            (μ t * poissonPMF (μ t).toNNReal j) := by ac_rfl
        _ = _ := by rw [← poissonPMF_succ_mul (μ t) (measure_ne_top μ _) j]; ac_rfl
  induction k with
  | zero => exact hz l
  | succ k ih =>
    apply (ENNReal.mul_right_inj (by positivity : ((k + 1 : ℕ) : ℝ≥0∞) ≠ 0)
      (by simp : ((k + 1 : ℕ) : ℝ≥0∞) ≠ ∞)).1
    rw [joint_count_probability_succ μ hs ht hst, ih, ← mul_assoc,
      ← poissonPMF_succ_mul (μ s) (measure_ne_top μ _) k, mul_assoc]

end FinitePoisson
end BoundaryDraft
