import BoundaryDraft.FiniteConfiguration

/-!
# Measurable orders and finite interval layers

This helper has no metric, volume law, dimension, or asymptotic input. An
explicit order avoids installing the coordinatewise order on spacetime.
Intervals exclude only their endpoints, not null-related interior points.
-/

open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section
namespace BoundaryDraft

/-- A partial order with measurable closed relation. No averaging identity is
part of this data. -/
structure MeasuredOrder (α : Type*) [MeasurableSpace α] where
  order : PartialOrder α
  measurable_rel : MeasurableSet {p : α × α | order.le p.1 p.2}

namespace MeasuredOrder
open FiniteConfiguration
variable {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α)

abbrev Rel (x y : α) : Prop := O.order.le x y

include O in
theorem measurable_diagonal : MeasurableSet {p : α × α | p.1 = p.2} := by
  have he : {p : α × α | p.1 = p.2} =
      {p | O.Rel p.1 p.2} ∩ {p | O.Rel p.2 p.1} := by
    ext p
    change (p.1 = p.2) ↔ O.Rel p.1 p.2 ∧ O.Rel p.2 p.1
    exact ⟨fun h => by rw [h]; exact ⟨O.order.le_refl _, O.order.le_refl _⟩,
      fun h => O.order.le_antisymm _ _ h.1 h.2⟩
  rw [he]
  exact O.measurable_rel.inter (O.measurable_rel.preimage measurable_swap)

def interval (x y : α) : Set α := {z | O.Rel x z ∧ O.Rel z y} \ {x, y}

@[simp] theorem left_not_mem_interval (x y : α) : x ∉ O.interval x y := by simp [interval]
@[simp] theorem right_not_mem_interval (x y : α) : y ∉ O.interval x y := by simp [interval]

theorem measurable_interval_joint :
    MeasurableSet {p : (α × α) × α | p.2 ∈ O.interval p.1.1 p.1.2} := by
  exact ((O.measurable_rel.preimage (measurable_fst.fst.prodMk measurable_snd)).inter
    (O.measurable_rel.preimage (measurable_snd.prodMk measurable_fst.snd))).diff
      ((O.measurable_diagonal.preimage (measurable_snd.prodMk measurable_fst.fst)).union
        (O.measurable_diagonal.preimage (measurable_snd.prodMk measurable_fst.snd)))

theorem measurable_interval (x y : α) : MeasurableSet (O.interval x y) :=
  O.measurable_interval_joint.preimage
    (show Measurable (fun z : α => ((x, y), z)) from measurable_const.prodMk measurable_id)

def intervalCount (x y : α) : Multiset α → ℕ := count (O.interval x y)

theorem jointMeasurable_intervalCount :
    JointMeasurable (fun p : α × α => O.intervalCount p.1 p.2) :=
  jointMeasurable_count O.measurable_interval_joint

@[measurability] theorem measurable_intervalCount (x y : α) :
    Measurable (O.intervalCount x y) := measurable_count (O.measurable_interval x y)

@[simp] theorem intervalCount_insert_endpoints (x y : α) (c : Multiset α) :
    O.intervalCount x y (x ::ₘ y ::ₘ c) = O.intervalCount x y c := by simp [intervalCount]

@[simp] theorem intervalCount_erase_left (x y : α) (c : Multiset α) :
    O.intervalCount x y (c.erase x) = O.intervalCount x y c := by
  by_cases hx : x ∈ c
  · calc
      O.intervalCount x y (c.erase x) = O.intervalCount x y (x ::ₘ c.erase x) := by
        simp [intervalCount]
      _ = O.intervalCount x y c := by rw [Multiset.cons_erase hx]
  · rw [Multiset.erase_of_not_mem hx]

@[simp] theorem intervalCount_erase_right (x y : α) (c : Multiset α) :
    O.intervalCount x y (c.erase y) = O.intervalCount x y c := by
  by_cases hy : y ∈ c
  · calc
      O.intervalCount x y (c.erase y) = O.intervalCount x y (y ::ₘ c.erase y) := by
        simp [intervalCount]
      _ = O.intervalCount x y c := by rw [Multiset.cons_erase hy]
  · rw [Multiset.erase_of_not_mem hy]

/-- Reduced occurrence sum; the theorem below recovers counts in the ORIGINAL
configuration, including configurations with multiplicities. -/
def intervalPairSum {E : Type*} [AddCommMonoid E] (f : ℕ → E) : Multiset α → E :=
  pairSum fun x y c => if O.Rel x y ∧ x ≠ y then f (O.intervalCount x y c) else 0

theorem jointMeasurable_pairTerm {E : Type*} [MeasurableSpace E] [Zero E] (f : ℕ → E) :
    JointMeasurable (fun p : α × α =>
      fun c => if O.Rel p.1 p.2 ∧ p.1 ≠ p.2 then f (O.intervalCount p.1 p.2 c) else 0) := by
  intro n
  exact Measurable.ite
    ((O.measurable_rel.inter O.measurable_diagonal.compl).preimage measurable_fst)
    ((measurable_of_countable f).comp (O.jointMeasurable_intervalCount n)) measurable_const

@[measurability] theorem measurable_intervalPairSum {E : Type*} [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E] (f : ℕ → E) : Measurable (O.intervalPairSum f) :=
  measurable_pairSum (O.jointMeasurable_pairTerm f)

theorem intervalPairSum_eq_sum {E : Type*} [AddCommMonoid E] (f : ℕ → E) (c : Multiset α) :
    O.intervalPairSum f c = (c.map fun x => (c.map fun y =>
      if O.Rel x y ∧ x ≠ y then f (O.intervalCount x y c) else 0).sum).sum := by
  unfold intervalPairSum pairSum pointSum
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp only [intervalCount_erase_right, intervalCount_erase_left]
  conv_rhs => rw [← Multiset.cons_erase hx]
  simp only [Multiset.map_cons, Multiset.sum_cons, ne_eq, not_true_eq_false, and_false,
    if_false, zero_add, intervalCount, count_cons, left_not_mem_interval, if_false, add_zero]
  simp only [show ∀ y, count (O.interval x y) (c.erase x) = count (O.interval x y) c from
    fun y => O.intervalCount_erase_left x y c]

/-- Layer zero counts links, layer k counts exactly k exclusive interior points. -/
def layer (k : ℕ) : Multiset α → ℕ := O.intervalPairSum (fun n => if n = k then 1 else 0)

@[measurability] theorem measurable_layer (k : ℕ) : Measurable (O.layer k) :=
  O.measurable_intervalPairSum _

theorem layer_cast (k : ℕ) (c : Multiset α) :
    (O.layer k c : ℝ) = O.intervalPairSum (fun n => if n = k then (1 : ℝ) else 0) c := by
  simp only [layer, intervalPairSum_eq_sum, Nat.cast_multiset_sum, Multiset.map_map,
    Function.comp_def, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Actual interval in the finite support. -/
def configurationInterval (c : Multiset α) (x y : α) : Finset α :=
  c.toFinset.filter (fun z => z ∈ O.interval x y)

theorem intervalCount_eq_card {c : Multiset α} (hc : c.Nodup) (x y : α) :
    O.intervalCount x y c = (O.configurationInterval c x y).card := by
  rw [intervalCount, count, Multiset.countP_eq_card_filter, configurationInterval,
    ← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hc.filter _)]

def layerPairs (k : ℕ) (c : Multiset α) : Finset (α × α) :=
  (c.toFinset ×ˢ c.toFinset).filter (fun p => O.Rel p.1 p.2 ∧ p.1 ≠ p.2 ∧
    (O.configurationInterval c p.1 p.2).card = k)

theorem layer_eq_card {c : Multiset α} (hc : c.Nodup) (k : ℕ) :
    O.layer k c = (O.layerPairs k c).card := by
  have hsum (f : α → ℕ) : (c.map f).sum = ∑ x ∈ c.toFinset, f x := by
    simp [Finset.sum, Multiset.dedup_eq_self.mpr hc]
  rw [layer, intervalPairSum_eq_sum, layerPairs, Finset.card_filter, Finset.sum_product]
  simp only [← hsum, ← O.intervalCount_eq_card hc]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  by_cases hxy : O.Rel x y <;> by_cases hne : x = y <;>
    by_cases hk : O.intervalCount x y c = k <;> simp [hxy, hne, hk]

/-- The finite support with the supplied order, never an ambient coordinate order. -/
structure Point (O : MeasuredOrder α) (c : Multiset α) where
  val : α
  mem : val ∈ c

namespace Point
variable {O}

@[ext] theorem ext {c : Multiset α} {x y : O.Point c} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  congr

instance (c : Multiset α) : PartialOrder (O.Point c) where
  le x y := O.Rel x.val y.val
  le_refl x := O.order.le_refl x.val
  le_trans _ _ _ := O.order.le_trans _ _ _
  le_antisymm _ _ hxy hyx := ext (O.order.le_antisymm _ _ hxy hyx)

instance (c : Multiset α) : Fintype (O.Point c) :=
  Fintype.ofEquiv ↥c.toFinset
    { toFun := fun x => ⟨x.val, Multiset.mem_toFinset.mp x.property⟩
      invFun := fun x => ⟨x.val, Multiset.mem_toFinset.mpr x.mem⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem lt_iff {c : Multiset α} (x y : O.Point c) :
    x < y ↔ O.Rel x.val y.val ∧ x.val ≠ y.val := by
  rw [lt_iff_le_and_ne]
  exact and_congr_right fun _ => not_congr ⟨congrArg Point.val, ext⟩

theorem mem_interval_iff {c : Multiset α} (x y z : O.Point c) :
    z.val ∈ O.interval x.val y.val ↔ x < z ∧ z < y := by
  simp only [interval, mem_diff, mem_setOf_eq, mem_insert_iff, mem_singleton_iff, lt_iff]
  constructor
  · rintro ⟨⟨hxz, hzy⟩, he⟩
    exact ⟨⟨hxz, fun h => he (Or.inl h.symm)⟩, ⟨hzy, fun h => he (Or.inr h)⟩⟩
  · rintro ⟨⟨hxz, hx⟩, ⟨hzy, hy⟩⟩
    exact ⟨⟨hxz, hzy⟩, fun h => h.elim (fun h => hx h.symm) hy⟩

end Point
end MeasuredOrder
end BoundaryDraft
