import BoundaryDraft.SpacetimeSprinkling

/-!
# The finite order induced by a spacetime configuration

The support carries the actual Minkowski partial order, not the coordinatewise
order on functions. Counts retain multiplicities on arbitrary configurations;
on the almost-surely simple sprinklings they equal finite-set cardinalities.
Null-related points remain part of the order and its open order intervals.
-/

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable section

namespace BoundaryDraft

open FiniteConfiguration

theorem causalFuture_refl (x : Spacetime) : x ∈ causalFuture x := by
  simp [causalFuture, spatialSeparationSq]

theorem causalFuture_antisymm {x y : Spacetime}
    (hxy : y ∈ causalFuture x) (hyx : x ∈ causalFuture y) : x = y := by
  have ht : x 0 = y 0 := le_antisymm hxy.1 hyx.1
  have hs : spatialSeparationSq x y ≤ 0 := by simpa [ht] using hxy.2
  ext i
  refine Fin.cases ht (fun j => ?_) i
  have hj : (y j.succ - x j.succ) ^ 2 ≤ spatialSeparationSq x y :=
    Finset.single_le_sum (fun k _ => sq_nonneg (y k.succ - x k.succ)) (Finset.mem_univ j)
  nlinarith [sq_nonneg (y j.succ - x j.succ)]

/-- A new type prevents accidental use of the coordinatewise spacetime order. -/
structure CausalPoint (c : Multiset Spacetime) where
  val : Spacetime
  mem : val ∈ c

namespace CausalPoint

/-- Forget only the wrapper, not any point of the support. -/
def equivSupport (c : Multiset Spacetime) : CausalPoint c ≃ ↥c.toFinset where
  toFun x := ⟨x.val, Multiset.mem_toFinset.mpr x.mem⟩
  invFun x := ⟨x.val, Multiset.mem_toFinset.mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (c : Multiset Spacetime) : Fintype (CausalPoint c) :=
  Fintype.ofEquiv ↥c.toFinset (equivSupport c).symm

instance (c : Multiset Spacetime) : CoeOut (CausalPoint c) Spacetime := ⟨CausalPoint.val⟩

@[ext] theorem ext {c : Multiset Spacetime} {x y : CausalPoint c}
    (h : (x : Spacetime) = (y : Spacetime)) : x = y := by
  cases x
  cases y
  congr

instance (c : Multiset Spacetime) : PartialOrder (CausalPoint c) where
  le x y := (y : Spacetime) ∈ causalFuture x
  le_refl x := causalFuture_refl x
  le_trans _ _ _ := causalFuture_trans
  le_antisymm _ _ hxy hyx := ext (causalFuture_antisymm hxy hyx)

@[simp] theorem le_iff {c : Multiset Spacetime} (x y : CausalPoint c) :
    x ≤ y ↔ (y : Spacetime) ∈ causalFuture x := Iff.rfl

theorem lt_iff {c : Multiset Spacetime} (x y : CausalPoint c) :
    x < y ↔ (y : Spacetime) ∈ causalFuture x ∧ (x : Spacetime) ≠ y := by
  rw [lt_iff_le_and_ne, le_iff]
  exact and_congr_right fun _ => not_congr ⟨congrArg CausalPoint.val, ext⟩

theorem card_eq {c : Multiset Spacetime} (hc : c.Nodup) :
    Fintype.card (CausalPoint c) = c.card := by
  rw [Fintype.card_congr (equivSupport c), Fintype.card_coe,
    Multiset.toFinset_card_of_nodup hc]

/-- The ambient endpoint-excluded interval is exactly the strict order interval
on the induced finite causal set. -/
theorem mem_interval_iff {c : Multiset Spacetime} (x y z : CausalPoint c) :
    (z : Spacetime) ∈ causalIntervalInterior x y ↔ x < z ∧ z < y := by
  simp only [causalIntervalInterior, causalInterval, causalPast, mem_diff,
    mem_inter_iff, mem_setOf_eq, mem_insert_iff, mem_singleton_iff, lt_iff]
  constructor
  · rintro ⟨⟨hxz, hzy⟩, he⟩
    exact ⟨⟨hxz, fun h => he (Or.inl h.symm)⟩, ⟨hzy, fun h => he (Or.inr h)⟩⟩
  · rintro ⟨⟨hxz, hx⟩, ⟨hzy, hy⟩⟩
    exact ⟨⟨hxz, hzy⟩, fun h => h.elim (fun h => hx h.symm) hy⟩

end CausalPoint

/-- The open order interval among sampled locations, with no endpoints. -/
def configurationInterval (c : Multiset Spacetime) (x y : Spacetime) : Finset Spacetime :=
  c.toFinset.filter (fun z => z ∈ causalIntervalInterior x y)

theorem intervalCount_eq_card {c : Multiset Spacetime} (hc : c.Nodup) (x y : Spacetime) :
    intervalCount x y c = (configurationInterval c x y).card := by
  rw [intervalCount, count, Multiset.countP_eq_card_filter, configurationInterval,
    ← Multiset.toFinset_filter, Multiset.toFinset_card_of_nodup (hc.filter _)]

/-- Removing either endpoint does not change the interval count, whether or
not that endpoint is present, and even with multiplicities. -/
@[simp] theorem intervalCount_erase_left [DecidableEq Spacetime] (x y : Spacetime) (c : Multiset Spacetime) :
    intervalCount x y (c.erase x) = intervalCount x y c := by
  by_cases hx : x ∈ c
  · calc
      intervalCount x y (c.erase x) = intervalCount x y (x ::ₘ c.erase x) := by
        simp [intervalCount]
      _ = intervalCount x y c := by rw [Multiset.cons_erase hx]
  · rw [Multiset.erase_of_not_mem hx]

@[simp] theorem intervalCount_erase_right [DecidableEq Spacetime] (x y : Spacetime) (c : Multiset Spacetime) :
    intervalCount x y (c.erase y) = intervalCount x y c := by
  by_cases hy : y ∈ c
  · calc
      intervalCount x y (c.erase y) = intervalCount x y (y ::ₘ c.erase y) := by
        simp [intervalCount]
      _ = intervalCount x y c := by rw [Multiset.cons_erase hy]
  · rw [Multiset.erase_of_not_mem hy]

/-- A reduced pair sum is the full finite double sum with zero diagonal.
This proves that the residual count used by Mecke is the original interval
cardinality; it is not a different action on a punctured causal set. -/
theorem intervalPairSum_eq_sum {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    (c : Multiset Spacetime) :
    intervalPairSum f c = (c.map fun x => (c.map fun y =>
      if y ∈ causalFuture x ∧ x ≠ y then f (intervalCount x y c) else 0).sum).sum := by
  letI : DecidableEq Spacetime := Classical.decEq _
  unfold intervalPairSum pairSum pointSum
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  simp only [intervalCount_erase_right, intervalCount_erase_left]
  conv_rhs => rw [← Multiset.cons_erase hx]
  simp only [Multiset.map_cons, Multiset.sum_cons, ne_eq, not_true_eq_false, and_false,
    if_false, zero_add, intervalCount, count_cons, left_not_mem_causalIntervalInterior,
    if_false, add_zero]
  simp only [show ∀ y, count (causalIntervalInterior x y) (c.erase x) =
    count (causalIntervalInterior x y) c from fun y => intervalCount_erase_left x y c]

/-- Relabelling any finite tuple does not change an interval-pair observable. -/
theorem intervalPairSum_perm {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    {n : ℕ} (v : Fin n → Spacetime) (e : Equiv.Perm (Fin n)) :
    intervalPairSum f (ofTuple (v ∘ e)) = intervalPairSum f (ofTuple v) := by
  rw [ofTuple_perm]

end BoundaryDraft
