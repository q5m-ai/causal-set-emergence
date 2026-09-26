import BoundaryDraft.DiscreteBDG

/-!
# Independent discrete-action contracts and finite examples

No expectation identity is assumed or asserted. The five-point chain tests
all four nonzero layers; the six-point chain tests the vanishing higher-layer
weight. A null-sided diamond tests both null relations and a negative action.
-/

open MeasureTheory Set BoundaryDraft
open BoundaryDraft.FiniteConfiguration
open scoped BigOperators Classical

noncomputable section

namespace DiscreteBDGRegression

example (ρ : ℝ) : discreteBDGAction ρ 0 = 0 := by
  simp [discreteBDGAction, intervalLayer, intervalPairSum_eq_sum]

example (ρ : ℝ) (x : Spacetime) : discreteBDGAction ρ {x} = bdgNormalization ρ := by
  simp [discreteBDGAction, intervalLayer, intervalPairSum_eq_sum]

private theorem timeAxis_eq_iff (s t : ℝ) : timeAxis s = timeAxis t ↔ s = t := by
  constructor
  · intro h
    simpa using congrFun h 0
  · rintro rfl
    rfl

private theorem timeAxis_causal_iff (s t : ℝ) :
    timeAxis t ∈ causalFuture (timeAxis s) ↔ s ≤ t := by
  simp [causalFuture, spatialSeparationSq, sq_nonneg]

private theorem timeAxis_interval_iff (s t u : ℝ) :
    timeAxis u ∈ causalIntervalInterior (timeAxis s) (timeAxis t) ↔ s < u ∧ u < t := by
  simp only [causalIntervalInterior, causalInterval, causalPast, mem_diff, mem_inter_iff,
    mem_setOf_eq, timeAxis_causal_iff, mem_insert_iff, mem_singleton_iff, timeAxis_eq_iff]
  constructor
  · rintro ⟨⟨hs, ht⟩, hn⟩
    exact ⟨lt_of_le_of_ne hs (fun h => hn (Or.inl h.symm)),
      lt_of_le_of_ne ht (fun h => hn (Or.inr h))⟩
  · rintro ⟨hs, ht⟩
    exact ⟨⟨hs.le, ht.le⟩, fun h => h.elim (ne_of_gt hs) (ne_of_lt ht)⟩

def chainFive : Multiset Spacetime :=
  timeAxis 0 ::ₘ timeAxis 1 ::ₘ timeAxis 2 ::ₘ timeAxis 3 ::ₘ timeAxis 4 ::ₘ 0

theorem chainFive_layers :
    intervalLayer 0 chainFive = 4 ∧ intervalLayer 1 chainFive = 3 ∧
    intervalLayer 2 chainFive = 2 ∧ intervalLayer 3 chainFive = 1 := by
  norm_num [intervalLayer, intervalPairSum_eq_sum, chainFive, timeAxis_causal_iff,
    timeAxis_eq_iff, intervalCount, count_cons, timeAxis_interval_iff]

example : chainFive.Nodup := by simp [chainFive, timeAxis_eq_iff]

example (ρ : ℝ) : discreteBDGAction ρ chainFive = 4 * bdgNormalization ρ := by
  rcases chainFive_layers with ⟨h0, h1, h2, h3⟩
  rw [discreteBDGAction, h0, h1, h2, h3]
  norm_num [chainFive]
  ring

/-- The pair spanning all six points has four interior points and contributes
zero, rather than accidentally extending the cubic weights. -/
example : intervalLayer 4 (timeAxis 5 ::ₘ chainFive) = 1 ∧ bdgLayerWeight 4 = 0 := by
  norm_num [intervalLayer, intervalPairSum_eq_sum, chainFive, timeAxis_causal_iff,
    timeAxis_eq_iff, intervalCount, count_cons, timeAxis_interval_iff, bdgLayerWeight]

example (ρ : ℝ) : discreteBDGAction ρ (timeAxis 5 ::ₘ chainFive) =
    5 * bdgNormalization ρ := by
  norm_num [discreteBDGAction, intervalLayer, intervalPairSum_eq_sum, chainFive,
    timeAxis_causal_iff, timeAxis_eq_iff, intervalCount, count_cons, timeAxis_interval_iff]
  ring

def antichainThree : Multiset Spacetime :=
  (![0, 0, 0, 0] : Spacetime) ::ₘ ![0, 1, 0, 0] ::ₘ ![0, 2, 0, 0] ::ₘ 0

/-- A simultaneous spacelike antichain has no causal pairs, in any layer. -/
theorem antichainThree_layers (k : ℕ) : intervalLayer k antichainThree = 0 := by
  norm_num [intervalLayer, intervalPairSum_eq_sum, antichainThree, causalFuture,
    spatialSeparationSq, Fin.sum_univ_three, Matrix.cons_val_two]

example (ρ : ℝ) : discreteBDGAction ρ antichainThree = 3 * bdgNormalization ρ := by
  simp only [discreteBDGAction, antichainThree_layers]
  simp [antichainThree, mul_comm]

/-- All four links are null-related; replacing the causal order by the
chronological relation would destroy this example. -/
def nullDiamond : Multiset Spacetime :=
  (![0, 0, 0, 0] : Spacetime) ::ₘ ![1, 1, 0, 0] ::ₘ ![1, -1, 0, 0] ::ₘ ![2, 0, 0, 0] ::ₘ 0

private theorem planarEvent_eq_iff (t x s y : ℝ) :
    (![t, x, 0, 0] : Spacetime) = ![s, y, 0, 0] ↔ t = s ∧ x = y := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem nullDiamond_layers : intervalLayer 0 nullDiamond = 4 ∧
    intervalLayer 1 nullDiamond = 0 ∧ intervalLayer 2 nullDiamond = 1 ∧
    intervalLayer 3 nullDiamond = 0 := by
  norm_num [intervalLayer, intervalPairSum_eq_sum, nullDiamond, causalFuture,
    spatialSeparationSq, Fin.sum_univ_three, intervalCount, count_cons,
    causalIntervalInterior, causalInterval, causalPast, planarEvent_eq_iff,
    Matrix.cons_val_two, Matrix.cons_val_three]

example (ρ : ℝ) : discreteBDGAction ρ nullDiamond = -16 * bdgNormalization ρ := by
  rcases nullDiamond_layers with ⟨h0, h1, h2, h3⟩
  rw [discreteBDGAction, h0, h1, h2, h3]
  norm_num [nullDiamond]
  ring

/-- Density dependence is inverse square-root, not square-root. -/
example : bdgNormalization 16 = bdgNormalization 1 / 4 := by
  have hs : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [bdgNormalization, hs]
  ring

/-- Coincident locations do not introduce strictly causal self-pairs. The
multiplicity-preserving extension is total; such samples are almost surely
absent under every FiniteSprinkling. -/
example (ρ : ℝ) (x : Spacetime) :
    discreteBDGAction ρ (x ::ₘ x ::ₘ 0) = 2 * bdgNormalization ρ := by
  simp [discreteBDGAction, intervalLayer, intervalPairSum_eq_sum, mul_comm]

example (S : FiniteSprinkling) : ∀ᵐ c ∂S.probability, c.Nodup := S.ae_nodup

/-- Independent restatement of the downstream point/pair contract. -/
example (ρ : ℝ) (c : Multiset Spacetime) :
    discreteBDGAction ρ c = 4 / (Real.sqrt 6 * Real.sqrt ρ) *
      ((c.card : ℝ) - pairSum (fun x y r =>
        if y ∈ causalFuture x ∧ x ≠ y then
          (if intervalCount x y r = 0 then 1 else
           if intervalCount x y r = 1 then -9 else
           if intervalCount x y r = 2 then 16 else
           if intervalCount x y r = 3 then -8 else 0) else 0) c) :=
  discreteBDGAction_eq_pairSum ρ c

example (S : FiniteSprinkling) : Measurable (discreteBDGAction S.density) :=
  measurable_discreteBDGAction _

example (S : FiniteSprinkling) : Integrable (discreteBDGAction S.density) S.probability :=
  integrable_discreteBDGAction S

example (S : FiniteSprinkling) (hS : volume S.region = 0) :
    ∀ᵐ c ∂S.probability, discreteBDGAction S.density c = 0 := by
  filter_upwards [S.ae_empty_of_volume_zero hS] with c hc
  simp [hc, discreteBDGAction, intervalLayer, intervalPairSum_eq_sum]

example {n : ℕ} (ρ : ℝ) (v : Fin n → Spacetime) (e : Equiv.Perm (Fin n)) :
    discreteBDGAction ρ (ofTuple (v ∘ e)) = discreteBDGAction ρ (ofTuple v) :=
  discreteBDGAction_perm ρ v e

/-- The induced order is not the coordinatewise order on the ambient type. -/
example :
    (⟨![0, 1, 0, 0], by simp⟩ :
      CausalPoint ({![0, 1, 0, 0], ![2, 0, 0, 0]} : Multiset Spacetime)) <
    ⟨![2, 0, 0, 0], by simp⟩ := by
  rw [CausalPoint.lt_iff]
  norm_num [causalFuture, spatialSeparationSq, Fin.sum_univ_three,
    funext_iff, Fin.forall_fin_succ, Matrix.cons_val_two]

example {c : Multiset Spacetime} (x y z : CausalPoint c) :
    (z : Spacetime) ∈ causalIntervalInterior x y ↔ x < z ∧ z < y :=
  CausalPoint.mem_interval_iff x y z

example {c : Multiset Spacetime} (hc : c.Nodup) (k : ℕ) :
    intervalLayer k c = (causalLayerPairs k c).card := intervalLayer_eq_card hc k

end DiscreteBDGRegression
