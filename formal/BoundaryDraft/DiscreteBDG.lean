import BoundaryDraft.FiniteCausalOrder

/-!
# The discrete four-dimensional BDG action

Layer k counts strictly causal ordered pairs with exactly k interior points
(so layer 0 counts links). The normalized action is the genuine finite-order
observable (l_p² / hbar) S, with density rho = l⁻⁴. It does not use a continuum
integral or an expected value in its definition. Identifying its expectation
with the deterministic continuum mean is separate work.
-/

open MeasureTheory Set
open scoped BigOperators Classical

noncomputable section

namespace BoundaryDraft

open FiniteConfiguration

/-- Number of strictly causal ordered pairs with k points in their open order
interval. On simple samples these are ordinary finite causal-set layer counts. -/
def intervalLayer (k : ℕ) : Multiset Spacetime → ℕ :=
  intervalPairSum (fun n => if n = k then 1 else 0)

/-- Actual finite set of layer-k causal pairs in the support. -/
def causalLayerPairs (k : ℕ) (c : Multiset Spacetime) : Finset (Spacetime × Spacetime) :=
  (c.toFinset ×ˢ c.toFinset).filter (fun p => p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2 ∧
    (configurationInterval c p.1 p.2).card = k)

/-- On a simple configuration the random layer observable really is a
finite-set cardinality, not an occurrence count with hidden multiplicities. -/
theorem intervalLayer_eq_card {c : Multiset Spacetime} (hc : c.Nodup) (k : ℕ) :
    intervalLayer k c = (causalLayerPairs k c).card := by
  have hsum (f : Spacetime → ℕ) : (c.map f).sum = ∑ x ∈ c.toFinset, f x := by
    simp [Finset.sum, Multiset.dedup_eq_self.mpr hc]
  rw [intervalLayer, intervalPairSum_eq_sum, causalLayerPairs, Finset.card_filter,
    Finset.sum_product]
  simp only [← hsum, ← intervalCount_eq_card hc]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  by_cases hxy : y ∈ causalFuture x <;> by_cases hne : x = y <;>
    by_cases hk : intervalCount x y c = k <;> simp [hxy, hne, hk]

/-- Kernel-side coefficients; the pair contribution to the action has the
opposite sign. The factorial denominators belong to the Poisson PMF, not here. -/
def bdgLayerWeight (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then -9 else if n = 2 then 16 else if n = 3 then -8 else 0

theorem bdgLayerWeight_expansion (n : ℕ) :
    bdgLayerWeight n = (if n = 0 then 1 else 0) +
      (-9) * (if n = 1 then 1 else 0) +
      16 * (if n = 2 then 1 else 0) + (-8) * (if n = 3 then 1 else 0) := by
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;>
    by_cases h2 : n = 2 <;> by_cases h3 : n = 3 <;>
    simp_all [bdgLayerWeight]

theorem abs_bdgLayerWeight_le (n : ℕ) : |bdgLayerWeight n| ≤ 16 := by
  unfold bdgLayerWeight
  split_ifs <;> norm_num

/-- The finite exponential generating polynomial is exactly the existing P. -/
theorem bdgLayerWeight_polynomial (z : ℝ) :
    (∑ k ∈ Finset.range 4, bdgLayerWeight k * z ^ k / k.factorial) = bdgPolynomial z := by
  norm_num [Finset.sum_range_succ, bdgLayerWeight, bdgPolynomial, Nat.factorial]
  ring

/-- Including the Poisson exponential recovers the existing signed kernel. -/
theorem bdgLayerWeight_kernel (z : ℝ) :
    (∑ k ∈ Finset.range 4, bdgLayerWeight k * (Real.exp (-z) * z ^ k / k.factorial)) =
      bdgKernel z := by
  norm_num [Finset.sum_range_succ, bdgLayerWeight, bdgKernel, bdgPolynomial, Nat.factorial]
  ring

/-- Four-dimensional physical normalization after multiplying S by l_p²/hbar.
Only positive density is used by the sprinkling API. -/
def bdgNormalization (ρ : ℝ) : ℝ := 4 / (Real.sqrt 6 * Real.sqrt ρ)

theorem bdgNormalization_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < bdgNormalization ρ := by
  unfold bdgNormalization
  positivity

/-- Averaging one point contributes one factor of density, leaving precisely
the prefactor used in the deterministic convention. This is only algebra. -/
theorem bdgNormalization_mul_density {ρ : ℝ} (hρ : 0 < ρ) :
    bdgNormalization ρ * ρ = (4 / Real.sqrt 6) * Real.sqrt ρ := by
  have hs := Real.sq_sqrt hρ.le
  have hn : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hρ)
  unfold bdgNormalization
  field_simp
  nlinarith [congrArg (fun t : ℝ => (4 * Real.sqrt 6) * t) hs]

/-- Genuine finite action, defined using only cardinality and interval layers.
The signs are N - N₀ + 9 N₁ - 16 N₂ + 8 N₃. -/
def discreteBDGAction (ρ : ℝ) (c : Multiset Spacetime) : ℝ :=
  bdgNormalization ρ * ((c.card : ℝ) - intervalLayer 0 c +
    9 * intervalLayer 1 c - 16 * intervalLayer 2 c + 8 * intervalLayer 3 c)

/-- Identification with the actual induced finite-order cardinalities. -/
theorem discreteBDGAction_eq_finite_order (ρ : ℝ) {c : Multiset Spacetime} (hc : c.Nodup) :
    discreteBDGAction ρ c = bdgNormalization ρ *
      ((Fintype.card (CausalPoint c) : ℝ) - (causalLayerPairs 0 c).card +
        9 * (causalLayerPairs 1 c).card - 16 * (causalLayerPairs 2 c).card +
        8 * (causalLayerPairs 3 c).card) := by
  simp only [discreteBDGAction, CausalPoint.card_eq hc, intervalLayer_eq_card hc]

/-- The identity with a genuine finite causal-set action holds almost surely
for the constructed probability measure; support and simplicity are derived. -/
theorem FiniteSprinkling.ae_discreteBDGAction_eq_finite_order (S : FiniteSprinkling) :
    ∀ᵐ c ∂S.probability, (∀ x ∈ c, x ∈ S.region) ∧
      discreteBDGAction S.density c = bdgNormalization S.density *
        ((Fintype.card (CausalPoint c) : ℝ) - (causalLayerPairs 0 c).card +
          9 * (causalLayerPairs 1 c).card - 16 * (causalLayerPairs 2 c).card +
          8 * (causalLayerPairs 3 c).card) := by
  filter_upwards [S.ae_supported, S.ae_nodup] with c hs hc
  exact ⟨hs, discreteBDGAction_eq_finite_order _ hc⟩

/-- Natural layer counts transport to the real pair-sum observable. -/
theorem intervalLayer_cast (k : ℕ) (c : Multiset Spacetime) :
    (intervalLayer k c : ℝ) = intervalPairSum (fun n => if n = k then (1 : ℝ) else 0) c := by
  simp only [intervalLayer, intervalPairSum_eq_sum, Nat.cast_multiset_sum,
    Multiset.map_map, Function.comp_def, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem intervalPairSum_add (f g : ℕ → ℝ) (c : Multiset Spacetime) :
    intervalPairSum (fun n => f n + g n) c = intervalPairSum f c + intervalPairSum g c := by
  simp only [intervalPairSum_eq_sum, ite_add_zero, Multiset.sum_map_add]

private theorem intervalPairSum_mul (a : ℝ) (f : ℕ → ℝ) (c : Multiset Spacetime) :
    intervalPairSum (fun n => a * f n) c = a * intervalPairSum f c := by
  have hi (p : Prop) [Decidable p] (b : ℝ) : (if p then a * b else 0) =
      a * (if p then b else 0) := by split_ifs <;> simp
  simp only [intervalPairSum_eq_sum, hi, Multiset.sum_map_mul_left]

/-- Finite regrouping by interval layers, before taking any expectation. -/
theorem intervalPairSum_bdgLayerWeight (c : Multiset Spacetime) :
    intervalPairSum bdgLayerWeight c = (intervalLayer 0 c : ℝ) -
      9 * intervalLayer 1 c + 16 * intervalLayer 2 c - 8 * intervalLayer 3 c := by
  simp only [show bdgLayerWeight = fun n => (if n = 0 then 1 else 0) +
      (-9) * (if n = 1 then 1 else 0) + 16 * (if n = 2 then 1 else 0) +
      (-8) * (if n = 3 then 1 else 0) from funext bdgLayerWeight_expansion,
    intervalPairSum_add, intervalPairSum_mul, ← intervalLayer_cast]
  ring

/-- Reduced-pair form ready for the already proved Campbell--Mecke API. -/
theorem discreteBDGAction_eq_pairSum (ρ : ℝ) (c : Multiset Spacetime) :
    discreteBDGAction ρ c = bdgNormalization ρ *
      ((c.card : ℝ) - intervalPairSum bdgLayerWeight c) := by
  rw [intervalPairSum_bdgLayerWeight, discreteBDGAction]
  ring

/-- Separate point and reduced-pair contributions. Both terms are integrable;
this equality itself is purely finite combinatorics. -/
theorem discreteBDGAction_eq_point_pair (ρ : ℝ) (c : Multiset Spacetime) :
    discreteBDGAction ρ c = bdgNormalization ρ *
      (pointSum (fun _ _ => (1 : ℝ)) c - pairSum (fun x y r =>
        if y ∈ causalFuture x ∧ x ≠ y then bdgLayerWeight (intervalCount x y r) else 0) c) := by
  rw [discreteBDGAction_eq_pairSum]
  simp [intervalPairSum, pointSum]

/-- The full double-sum version counts intervals in the original sample. -/
theorem discreteBDGAction_eq_sum (ρ : ℝ) (c : Multiset Spacetime) :
    discreteBDGAction ρ c = bdgNormalization ρ * ((c.card : ℝ) -
      (c.map fun x => (c.map fun y => if y ∈ causalFuture x ∧ x ≠ y then
        bdgLayerWeight (intervalCount x y c) else 0).sum).sum) := by
  rw [discreteBDGAction_eq_pairSum, intervalPairSum_eq_sum]

@[measurability] theorem measurable_intervalLayer (k : ℕ) : Measurable (intervalLayer k) :=
  measurable_intervalPairSum _

@[measurability] theorem measurable_discreteBDGAction (ρ : ℝ) :
    Measurable (discreteBDGAction ρ) := by
  have hc : Measurable (fun c : Multiset Spacetime => (c.card : ℝ)) := by
    simpa only [Function.comp_def, count_univ] using
      (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (measurable_count (α := Spacetime) MeasurableSet.univ)
  simp only [funext (discreteBDGAction_eq_pairSum ρ)]
  exact measurable_const.mul (hc.sub (measurable_intervalPairSum _))

theorem integrable_intervalLayer (S : FiniteSprinkling) (k : ℕ) :
    Integrable (fun c => (intervalLayer k c : ℝ)) S.probability := by
  simp only [funext (intervalLayer_cast k)]
  apply integrable_intervalPairSum S _ 1 (by norm_num)
  intro n
  split_ifs <;> norm_num

/-- Absolute integrability is derived from the Poisson factorial moments and
the bounded layer weights, without a bounded-cardinality assumption. Finite
volume suffices; in particular every bounded measurable region is covered. -/
theorem integrable_discreteBDGAction (S : FiniteSprinkling) :
    Integrable (discreteBDGAction S.density) S.probability := by
  simp only [funext (discreteBDGAction_eq_pairSum S.density)]
  exact ((FinitePoisson.integrable_card S.intensity).sub
    (integrable_intervalPairSum S bdgLayerWeight 16 (by norm_num) abs_bdgLayerWeight_le)).const_mul _

/-- An explicit quadratic absolute bound, useful without taking expectations. -/
theorem abs_discreteBDGAction_le (ρ : ℝ) (c : Multiset Spacetime) :
    |discreteBDGAction ρ c| ≤ |bdgNormalization ρ| *
      ((c.card : ℝ) + 16 * (c.card * (c.card - 1) : ℕ)) := by
  have h := abs_pairSum_le (fun x y r => if y ∈ causalFuture x ∧ x ≠ y then
    bdgLayerWeight (intervalCount x y r) else 0) c 16 (by
      intro x y r
      dsimp only
      split_ifs
      · exact abs_bdgLayerWeight_le _
      · norm_num)
  rw [discreteBDGAction_eq_pairSum, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (abs_sub _ _).trans
  simpa only [Nat.abs_cast, intervalPairSum, mul_comm] using
    (add_le_add_left h (c.card : ℝ))

theorem discreteBDGAction_perm (ρ : ℝ) {n : ℕ} (v : Fin n → Spacetime)
    (e : Equiv.Perm (Fin n)) :
    discreteBDGAction ρ (ofTuple (v ∘ e)) = discreteBDGAction ρ (ofTuple v) := by
  rw [ofTuple_perm]

end BoundaryDraft
