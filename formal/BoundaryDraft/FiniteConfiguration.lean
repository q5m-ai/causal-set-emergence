import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Measurable finite configurations

Configurations are multisets, not lists: observables cannot depend on an
ordering. Multiplicities are retained here; atomlessness will make duplicates
a null event for the sprinkling measure. The measurable space is the final
sigma algebra of all finite-tuple presentations.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

noncomputable section

namespace BoundaryDraft
namespace FiniteConfiguration

variable {α β E : Type*}

/-- Forget the enumeration of a finite tuple, retaining multiplicities. -/
def ofTuple {n : ℕ} (v : Fin n → α) : Multiset α := ∑ i, {v i}

@[simp] theorem ofTuple_zero (v : Fin 0 → α) : ofTuple v = 0 := by
  simp [ofTuple]

theorem ofTuple_remove {n : ℕ} (v : Fin (n + 1) → α) (i : Fin (n + 1)) :
    ofTuple v = v i ::ₘ ofTuple (i.removeNth v) := by
  rw [ofTuple, i.sum_univ_succAbove]
  rfl

@[simp] theorem ofTuple_cons {n : ℕ} (x : α) (v : Fin n → α) :
    ofTuple (Fin.cons x v) = x ::ₘ ofTuple v := by
  simp [ofTuple, Fin.sum_univ_succ, Multiset.singleton_add]

@[simp] theorem ofTuple_perm {n : ℕ} (v : Fin n → α) (e : Equiv.Perm (Fin n)) :
    ofTuple (v ∘ e) = ofTuple v := by
  exact Equiv.sum_comp e (fun i => ({v i} : Multiset α))

@[simp] theorem sum_map_ofTuple [AddCommMonoid E] {n : ℕ} (v : Fin n → α) (f : α → E) :
    ((ofTuple v).map f).sum = ∑ i, f (v i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ofTuple_remove v 0, Multiset.map_cons, Multiset.sum_cons, Fin.sum_univ_succ]
    congr 1
    exact ih _

@[simp] theorem card_ofTuple {n : ℕ} (v : Fin n → α) : (ofTuple v).card = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ofTuple_remove v 0, ih]

theorem ofTuple_eq_list {n : ℕ} (v : Fin n → α) :
    ofTuple v = (List.ofFn v : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ofTuple_remove v 0, List.ofFn_succ]
    change v 0 ::ₘ ofTuple (fun i : Fin n => v i.succ) =
      v 0 ::ₘ (List.ofFn (fun i : Fin n => v i.succ) : Multiset α)
    rw [ih]

@[simp] theorem mem_ofTuple {n : ℕ} (v : Fin n → α) (x : α) :
    x ∈ ofTuple v ↔ ∃ i, v i = x := by
  simp [ofTuple_eq_list]

@[simp] theorem nodup_ofTuple {n : ℕ} (v : Fin n → α) :
    (ofTuple v).Nodup ↔ Function.Injective v := by
  simp [ofTuple_eq_list, List.nodup_ofFn]

/-- A set of configurations is measurable exactly when every finite-tuple
presentation has measurable preimage. -/
instance instMeasurableSpace [MeasurableSpace α] : MeasurableSpace (Multiset α) :=
  ⨅ n : ℕ, (inferInstance : MeasurableSpace (Fin n → α)).map ofTuple

@[measurability] theorem measurable_ofTuple [MeasurableSpace α] (n : ℕ) :
    Measurable (ofTuple : (Fin n → α) → Multiset α) :=
  Measurable.of_le_map (iInf_le _ n)

theorem measurable_iff [MeasurableSpace α] [MeasurableSpace β] (f : Multiset α → β) :
    Measurable f ↔ ∀ n : ℕ, Measurable (fun v : Fin n → α => f (ofTuple v)) := by
  simp only [measurable_iff_le_map, instMeasurableSpace, MeasurableSpace.map_iInf,
    le_iInf_iff, MeasurableSpace.map_comp, Function.comp_def]

/-- Count points in a subset, with multiplicity. -/
def count (s : Set α) (c : Multiset α) : ℕ := by
  classical
  exact c.countP (· ∈ s)

@[simp] theorem count_zero (s : Set α) : count s 0 = 0 := by simp [count]

@[simp] theorem count_cons (s : Set α) (x : α) (c : Multiset α) :
    count s (x ::ₘ c) = count s c + if x ∈ s then 1 else 0 := by
  classical
  exact Multiset.countP_cons _ _ _

@[simp] theorem count_singleton (s : Set α) (x : α) :
    count s {x} = if x ∈ s then 1 else 0 := by
  simpa only [count_zero, zero_add] using count_cons s x 0

@[simp] theorem count_ofTuple (s : Set α) {n : ℕ} (v : Fin n → α) :
    count s (ofTuple v) = ∑ i, if v i ∈ s then 1 else 0 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ofTuple_remove v 0, count_cons, Fin.sum_univ_succ]
    rw [ih]
    exact Nat.add_comm _ _

@[measurability] theorem measurable_count [MeasurableSpace α] {s : Set α}
    (hs : MeasurableSet s) :
    Measurable (count s) := by
  classical
  apply (measurable_iff _).2
  intro n
  simp only [count_ofTuple]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (hs.preimage (measurable_pi_apply i)) measurable_const measurable_const

@[simp] theorem count_empty (c : Multiset α) : count ∅ c = 0 := by simp [count]

@[simp] theorem count_univ (c : Multiset α) : count univ c = c.card := by simp [count]

/-- A reduced point sum: remove one occurrence of the selected point. -/
def pointSum [AddCommMonoid E] (F : α → Multiset α → E) (c : Multiset α) : E := by
  classical
  exact (c.map fun x => F x (c.erase x)).sum

@[simp] theorem pointSum_zero [AddCommMonoid E] (F : α → Multiset α → E) :
    pointSum F 0 = 0 := by simp [pointSum]

/-- Finite tuple formula, including multiplicities and removal of exactly one
index. No injectivity hypothesis is needed. -/
theorem pointSum_ofTuple [AddCommMonoid E] (F : α → Multiset α → E)
    {n : ℕ} (v : Fin (n + 1) → α) :
    pointSum F (ofTuple v) = ∑ i, F (v i) (ofTuple (i.removeNth v)) := by
  classical
  rw [pointSum, sum_map_ofTuple]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [ofTuple_remove v i, Multiset.erase_cons_head]

/-- Explicit joint measurability on each finite stratum. This avoids imposing
an implicit product/quotient interchange on the configuration sigma algebra. -/
def JointMeasurable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
    (F : β → Multiset α → E) : Prop :=
  ∀ n : ℕ, Measurable (fun p : β × (Fin n → α) => F p.1 (ofTuple p.2))

theorem JointMeasurable.section [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace E]
    {F : β → Multiset α → E} (hF : JointMeasurable F) (x : β) :
    Measurable (F x) :=
  (measurable_iff _).2 fun n => (hF n).comp (measurable_const.prodMk measurable_id)

theorem measurable_pointSum [MeasurableSpace α] [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E] {F : α → Multiset α → E}
    (hF : JointMeasurable F) :
    Measurable (pointSum F) := by
  apply (measurable_iff _).2
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [pointSum_ofTuple]
    apply Finset.measurable_sum
    intro i _
    exact (hF n).comp (show Measurable (fun v : Fin (n + 1) → α => (v i, i.removeNth v)) from
      (measurable_pi_apply i).prodMk
        (measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)))

/-- Ordered pairs of distinct occurrences, with both occurrences removed
from the residual configuration. Coincident locations are still allowed here. -/
def pairSum [AddCommMonoid E] (F : α → α → Multiset α → E) : Multiset α → E :=
  pointSum fun x c => pointSum (F x) c

theorem jointMeasurable_pointSum [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] [AddCommMonoid E] [MeasurableAdd₂ E]
    {F : β → α → Multiset α → E}
    (hF : JointMeasurable (fun p : β × α => F p.1 p.2)) :
    JointMeasurable (fun b c => pointSum (F b) c) := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [pointSum_ofTuple]
    apply Finset.measurable_sum
    intro i _
    exact (hF n).comp (show Measurable (fun p : β × (Fin (n + 1) → α) =>
        ((p.1, p.2 i), i.removeNth p.2)) from
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)).prodMk
        (measurable_pi_lambda _ fun j => (measurable_pi_apply (i.succAbove j)).comp measurable_snd))

theorem measurable_pairSum [MeasurableSpace α] [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E] {F : α → α → Multiset α → E}
    (hF : JointMeasurable (fun p : α × α => F p.1 p.2)) :
    Measurable (pairSum F) :=
  measurable_pointSum (jointMeasurable_pointSum hF)

/-- Measurable subset counts, with the subset itself depending measurably on
parameters (in particular on the two endpoints of an interval). -/
theorem jointMeasurable_count [MeasurableSpace α] [MeasurableSpace β]
    {s : β → Set α} (hs : MeasurableSet {p : β × α | p.2 ∈ s p.1}) :
    JointMeasurable (fun b c => count (s b) c) := by
  intro n
  simp only [count_ofTuple]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (hs.preimage (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
    measurable_const measurable_const

theorem count_disjoint_union {s t : Set α} (hst : Disjoint s t) (c : Multiset α) :
    count (s ∪ t) c = count s c + count t c := by
  induction c using Multiset.induction_on with
  | empty => simp
  | @cons x c ih =>
    simp only [count_cons, ih, mem_union]
    have : ¬(x ∈ s ∧ x ∈ t) := fun h => Set.disjoint_left.1 hst h.1 h.2
    by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp_all <;> omega

/-- Counts as sums of indicators, including multiplicities. -/
theorem count_eq_sum (s : Set α) (c : Multiset α) :
    (count s c : ℝ≥0∞) = (c.map fun x => if x ∈ s then (1 : ℝ≥0∞) else 0).sum := by
  induction c using Multiset.induction_on with
  | empty => simp
  | @cons x c ih =>
    simp only [count_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, ih]
    split_ifs <;> simp [add_comm]

/-- The algebraic counting identity used to derive the Poisson recurrence. -/
theorem pointSum_count_event (s : Set α) (k : ℕ) (c : Multiset α) :
    pointSum (fun x r => if x ∈ s ∧ count s r = k then (1 : ℝ≥0∞) else 0) c =
      if count s c = k + 1 then ((k + 1 : ℕ) : ℝ≥0∞) else 0 := by
  classical
  have hc (x : α) (hx : x ∈ c) : count s c = count s (c.erase x) + if x ∈ s then 1 else 0 := by
    rw [← count_cons, Multiset.cons_erase hx]
  by_cases hk : count s c = k + 1
  · rw [if_pos hk, ← hk, count_eq_sum, pointSum]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    have := hc x hx
    by_cases hxs : x ∈ s <;> simp_all
  · rw [if_neg hk, pointSum]
    apply Multiset.sum_eq_zero
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 ha
    have := hc x hx
    by_cases hxs : x ∈ s <;> simp_all

theorem measurableSet_nodup [MeasurableSpace α]
    (hdiag : MeasurableSet {p : α × α | p.1 = p.2}) :
    MeasurableSet {c : Multiset α | c.Nodup} := by
  apply measurableSet_setOf.2
  apply (measurable_iff _).2
  intro n
  simp only [nodup_ofTuple, Function.Injective]
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro j
  exact (measurableSet_setOf.1
    (hdiag.preimage (show Measurable (fun v : Fin n → α => (v i, v j)) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)))).imp measurable_const

end FiniteConfiguration
end BoundaryDraft
