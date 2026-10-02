import BoundaryDraft.MeasuredOrderPoisson
import BoundaryDraft.DimensionActionConstants
import BoundaryDraft.DiscreteBDG
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Genuine dimension-indexed finite-order BDG action

Physical dimensions are integers d ≥ 2. The definitions use the independently
published point/pair constants and Euler-polynomial layer coefficients from
#71. No deterministic integral or expectation is used to define the action.
The layer coefficient is k! times the polynomial coefficient, not that
coefficient itself. The normalization is dimensionless in d = 2.
-/

open MeasureTheory Set Polynomial
open scoped BigOperators Classical
noncomputable section
namespace BoundaryDraft

/-- Published layer weights (zero-based layer index). Factorials are NOT
absorbed into the interval counts. -/
def dimensionLayerWeight (d k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (dimensionPolynomial d).coeff k

theorem dimensionPolynomialStage_natDegree_le (d m : ℕ) :
    (dimensionPolynomialStage d m).natDegree ≤ m := by
  induction m with
  | zero => simp [dimensionPolynomialStage]
  | succ m ih =>
    simp only [dimensionPolynomialStage]
    apply (natDegree_add_le _ _).trans
    apply max_le (ih.trans (Nat.le_succ m))
    apply natDegree_mul_le.trans
    have hleft : (C ((d : ℝ) / (2 * (m + 1))) * X).natDegree ≤ 1 := by
      simpa using (natDegree_C_mul_le ((d : ℝ) / (2 * (m + 1))) (X : Polynomial ℝ))
    have hright : ((dimensionPolynomialStage d m).derivative -
        dimensionPolynomialStage d m).natDegree ≤ m :=
      (natDegree_sub_le _ _).trans (max_le
        ((natDegree_le_natDegree degree_derivative_le).trans ih) ih)
    omega

theorem dimensionLayerWeight_zero (d k : ℕ) (hk : dimensionFactorCount d < k) :
    dimensionLayerWeight d k = 0 := by
  have hdeg : (dimensionPolynomial d).natDegree < k :=
    (dimensionPolynomialStage_natDegree_le d _).trans_lt hk
  rw [dimensionLayerWeight, coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]

/-- Exponential generating weights recover the independently defined kernel. -/
theorem dimensionLayerWeight_kernel (d : ℕ) (z : ℝ) :
    (∑ k ∈ Finset.range (dimensionFactorCount d + 1),
      dimensionLayerWeight d k * (Real.exp (-z) * z ^ k / k.factorial)) = dimensionKernel d z := by
  have he (k : ℕ) : dimensionLayerWeight d k * (Real.exp (-z) * z ^ k / k.factorial) =
      (dimensionPolynomial d).coeff k * z ^ k * Real.exp (-z) := by
    unfold dimensionLayerWeight
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
    ring
  simp_rw [he]
  have hdeg : (dimensionPolynomial d).natDegree < dimensionFactorCount d + 1 :=
    Nat.lt_succ_of_le (dimensionPolynomialStage_natDegree_le d _)
  rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range' hdeg]
  rfl

theorem dimensionLayerWeight_two (k : ℕ) :
    dimensionLayerWeight 2 k = if k = 0 then 1 else if k = 1 then -2 else if k = 2 then 1 else 0 := by
  by_cases hk : k ≤ 2
  · interval_cases k <;> norm_num [dimensionLayerWeight, dimensionPolynomial,
      dimensionFactorCount, dimensionPolynomialStage, mul_assoc, coeff_C_mul, coeff_X_mul,
      coeff_one, coeff_X, coeff_derivative, Nat.factorial]
  · rw [dimensionLayerWeight_zero 2 k (by norm_num [dimensionFactorCount]; omega)]
    simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, if_false]

theorem dimensionLayerWeight_four (k : ℕ) : dimensionLayerWeight 4 k = bdgLayerWeight k := by
  by_cases hk : k ≤ 3
  · interval_cases k <;> norm_num [dimensionLayerWeight, dimensionPolynomial,
      dimensionFactorCount, dimensionPolynomialStage, mul_assoc, coeff_C_mul, coeff_X_mul,
      coeff_one, coeff_X, coeff_derivative, Nat.factorial, bdgLayerWeight]
  · rw [dimensionLayerWeight_zero 4 k (by norm_num [dimensionFactorCount]; omega)]
    simp [bdgLayerWeight, show k ≠ 0 by omega, show k ≠ 1 by omega,
      show k ≠ 2 by omega, show k ≠ 3 by omega]

/-- Finite-order observable. For positive density the power is -(d-2)/d.
Only point cardinality and exclusive order layers enter this definition. -/
def discreteDimensionAction {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α)
    (d : ℕ) (ρ : ℝ) (c : Multiset α) : ℝ :=
  ρ ^ (2 / (d : ℝ) - 1) * (dimensionPointCoefficient d * c.card - dimensionPairCoefficient d *
    ∑ k ∈ Finset.range (dimensionFactorCount d + 1), dimensionLayerWeight d k * (O.layer k c : ℝ))

theorem dimension_discrete_exponent (d : ℕ) (hd : 2 ≤ d) :
    2 / (d : ℝ) - 1 = -((d : ℝ) - 2) / d := by
  have h : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem discreteDimensionAction_eq_finite_order {α : Type*} [MeasurableSpace α]
    (O : MeasuredOrder α) (d : ℕ) (ρ : ℝ) {c : Multiset α} (hc : c.Nodup) :
    discreteDimensionAction O d ρ c = ρ ^ (2 / (d : ℝ) - 1) *
      (dimensionPointCoefficient d * c.toFinset.card - dimensionPairCoefficient d *
        ∑ k ∈ Finset.range (dimensionFactorCount d + 1),
          dimensionLayerWeight d k * (O.layerPairs k c).card) := by
  simp only [discreteDimensionAction, O.layer_eq_card hc, Multiset.toFinset_card_of_nodup hc]

theorem discreteDimensionAction_perm {α : Type*} [MeasurableSpace α]
    (O : MeasuredOrder α) (d : ℕ) (ρ : ℝ) {N : ℕ} (v : Fin N → α) (e : Equiv.Perm (Fin N)) :
    discreteDimensionAction O d ρ (FiniteConfiguration.ofTuple (v ∘ e)) =
      discreteDimensionAction O d ρ (FiniteConfiguration.ofTuple v) := by
  rw [FiniteConfiguration.ofTuple_perm]

@[measurability] theorem measurable_discreteDimensionAction {α : Type*} [MeasurableSpace α]
    (O : MeasuredOrder α) (d : ℕ) (ρ : ℝ) : Measurable (discreteDimensionAction O d ρ) := by
  have hc : Measurable (fun c : Multiset α => (c.card : ℝ)) := by
    simpa only [Function.comp_def, FiniteConfiguration.count_univ] using
      (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (FiniteConfiguration.measurable_count (α := α) MeasurableSet.univ)
  apply measurable_const.mul
  apply (measurable_const.mul hc).sub
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (O.measurable_layer k))

/-- First and second factorial moments suffice. No bounded-cardinality premise. -/
theorem integrable_discreteDimensionAction {α : Type*} [MeasurableSpace α]
    (O : MeasuredOrder α) (d : ℕ) (ρ : ℝ) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (discreteDimensionAction O d ρ) (FinitePoisson.law μ) :=
  (((FinitePoisson.integrable_card μ).const_mul _).sub
    ((integrable_finset_sum _ fun k _ => (O.integrable_layer μ k).const_mul _).const_mul _)).const_mul _

/-- Density cancels the single-point power, exactly, at every positive density. -/
theorem dimensionNormalization_mul_density (d : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (2 / (d : ℝ) - 1) * ρ = ρ ^ (2 / (d : ℝ)) := by
  conv_lhs => rhs; rw [← Real.rpow_one ρ]
  rw [← Real.rpow_add hρ, sub_add_cancel]

/-- Dimension two uses no Planck-length definition and no residual density power. -/
theorem discreteDimensionAction_two {α : Type*} [MeasurableSpace α]
    (O : MeasuredOrder α) (ρ : ℝ) (c : Multiset α) :
    discreteDimensionAction O 2 ρ c =
      2 * c.card - 4 * (O.layer 0 c : ℝ) + 8 * (O.layer 1 c : ℝ) - 4 * (O.layer 2 c : ℝ) := by
  simp only [discreteDimensionAction, dimensionPointCoefficient_two, dimensionPairCoefficient_two,
    dimensionLayerWeight_two]
  norm_num [dimensionFactorCount, Finset.sum_range_succ]
  ring

end BoundaryDraft
