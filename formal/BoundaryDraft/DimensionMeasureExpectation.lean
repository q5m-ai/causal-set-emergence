import BoundaryDraft.DimensionDiscrete

/-!
# Dimension-indexed finite-measure expectation, before any volume law

The observable uses only finite order layers. Its expectation is derived from
the generic layer identity. The deterministic functional below uses the actual
measure of the exclusive order interval. In particular, restricting a measure
to a region restricts every interval; no convexity is assumed at this stage.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical
noncomputable section
namespace BoundaryDraft

namespace MeasuredOrder
variable {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α)
variable (μ : Measure α) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem dimensionKernel_eq_sum (d : ℕ) (x y : α) :
    dimensionKernel d (μ (O.interval x y)).toReal =
      ∑ k ∈ Finset.range (dimensionFactorCount d + 1),
        dimensionLayerWeight d k * O.layerProbability μ k x y := by
  simp_rw [O.layerProbability_eq]
  exact (dimensionLayerWeight_kernel d _).symm

/-- All pairs before masking; a different finite endpoint measure is allowed. -/
theorem integrable_dimensionKernel (d : ℕ) (ν : Measure α) [IsFiniteMeasure ν] :
    Integrable (fun p : α × α => dimensionKernel d (μ (O.interval p.1 p.2)).toReal) (ν.prod ν) := by
  simp_rw [O.dimensionKernel_eq_sum]
  apply integrable_finset_sum
  intro k _
  apply Integrable.const_mul
  apply (integrable_const (1 : ℝ)).mono' (O.measurable_layerProbability μ k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (O.layerProbability_nonneg μ k p.1 p.2)]
    exact O.layerProbability_le_one μ k p.1 p.2

theorem integrable_dimensionKernel_section (d : ℕ) (ν : Measure α) [IsFiniteMeasure ν] (x : α) :
    Integrable (fun y => dimensionKernel d (μ (O.interval x y)).toReal) ν := by
  simp_rw [O.dimensionKernel_eq_sum]
  apply integrable_finset_sum
  intro k _
  apply Integrable.const_mul
  apply (integrable_const (1 : ℝ)).mono'
    ((O.measurable_layerProbability μ k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖O.layerProbability μ k x y‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (O.layerProbability_nonneg μ k x y)]
    exact O.layerProbability_le_one μ k x y

def dimensionPairMean (d : ℕ) (x y : α) : ℝ :=
  if O.Rel x y ∧ x ≠ y then dimensionKernel d (μ (O.interval x y)).toReal else 0

omit [IsFiniteMeasure μ] in
theorem dimensionPairMean_eq_sum (d : ℕ) (x y : α) :
    O.dimensionPairMean μ d x y = ∑ k ∈ Finset.range (dimensionFactorCount d + 1),
      dimensionLayerWeight d k * O.layerMean μ k x y := by
  by_cases hxy : O.Rel x y ∧ x ≠ y
  · simpa only [dimensionPairMean, layerMean, hxy.1, hxy.2, ne_eq,
      not_false_eq_true, and_self, if_true] using O.dimensionKernel_eq_sum μ d x y
  · simp [dimensionPairMean, layerMean, hxy]

theorem integrable_dimensionPairMean (d : ℕ) :
    Integrable (fun p : α × α => O.dimensionPairMean μ d p.1 p.2) (μ.prod μ) := by
  simp only [funext₂ (O.dimensionPairMean_eq_sum μ d)]
  exact integrable_finset_sum _ fun k _ => (O.integrable_layerMean μ k).const_mul _

theorem integrable_dimensionPairMean_section (d : ℕ) (x : α) :
    Integrable (O.dimensionPairMean μ d x) μ := by
  simp only [funext (O.dimensionPairMean_eq_sum μ d x)]
  exact integrable_finset_sum _ fun k _ => (O.integrable_layerMean_section μ k x).const_mul _

/-- Exact signed finite-measure identity, retaining a possible atomic diagonal
mask. This is derived, not an assumption in the order or action. -/
theorem integral_discreteDimensionAction (d : ℕ) (ρ : ℝ) :
    (∫ c, discreteDimensionAction O d ρ c ∂FinitePoisson.law μ) =
      ρ ^ (2 / (d : ℝ) - 1) * (dimensionPointCoefficient d * (μ univ).toReal -
        dimensionPairCoefficient d * ∫ x, ∫ y, O.dimensionPairMean μ d x y ∂μ ∂μ) := by
  have hc : (∫ c : Multiset α, (c.card : ℝ) ∂FinitePoisson.law μ) = (μ univ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (μ := FinitePoisson.law μ)
      (f := fun c : Multiset α => (c.card : ℝ))
      (Filter.Eventually.of_forall fun c => Nat.cast_nonneg c.card)
      (FinitePoisson.integrable_card μ).aestronglyMeasurable]
    simp only [ENNReal.ofReal_natCast, FinitePoisson.lintegral_card]
  simp only [discreteDimensionAction]
  rw [integral_const_mul, integral_sub ((FinitePoisson.integrable_card μ).const_mul _)
    ((integrable_finset_sum _ fun k _ => (O.integrable_layer μ k).const_mul _).const_mul _),
    integral_const_mul, integral_const_mul, hc,
    integral_finset_sum _ (fun k _ => (O.integrable_layer μ k).const_mul _)]
  simp_rw [integral_const_mul, O.integral_layer, O.dimensionPairMean_eq_sum]
  simp_rw [integral_finset_sum _ (fun k _ => (O.integrable_layerMean_section μ k _).const_mul _),
    integral_const_mul]
  rw [integral_finset_sum _ (fun k _ => (O.integrable_layerMean μ k).integral_prod_left.const_mul _)]
  simp only [integral_const_mul]

end MeasuredOrder

/-- Independently defined deterministic finite-measure action. In a restricted
region this uses the restricted interval measure, including for non-convex M. -/
def dimensionFiniteMeasureAction {α : Type*} [MeasurableSpace α] (O : MeasuredOrder α)
    (d : ℕ) (μ : Measure α) (ρ : ℝ) : ℝ :=
  ρ ^ (2 / (d : ℝ)) * (dimensionPointCoefficient d * (μ univ).toReal -
    dimensionPairCoefficient d * ρ * ∫ x, ∫ y in {y | O.Rel x y},
      dimensionKernel d (ρ * (μ (O.interval x y)).toReal) ∂μ ∂μ)

/-- The exact finite-density bridge for any finite atomless measured order.
No flat interval law, causal-convexity premise or limiting statement enters. -/
theorem dimensionFiniteMeasureAction_expectation {α : Type*} [MeasurableSpace α]
    (O : MeasuredOrder α) (d : ℕ) (μ : Measure α) [IsFiniteMeasure μ] [NoAtoms μ]
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteDimensionAction O d ρ c ∂FinitePoisson.law (ENNReal.ofReal ρ • μ)) =
      dimensionFiniteMeasureAction O d μ ρ := by
  letI : IsFiniteMeasure (ENNReal.ofReal ρ • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)⟩
  rw [O.integral_discreteDimensionAction]
  have he (x : α) : (∫ y, O.dimensionPairMean (ENNReal.ofReal ρ • μ) d x y ∂μ) =
      ∫ y in {y | O.Rel x y}, dimensionKernel d (ρ * (μ (O.interval x y)).toReal) ∂μ := by
    have hm : MeasurableSet {y | O.Rel x y} := O.measurable_rel.preimage
      (show Measurable (fun y : α => (x, y)) from measurable_const.prodMk measurable_id)
    rw [← integral_indicator hm]
    apply integral_congr_ae
    have hne : ∀ᵐ y ∂μ, y ≠ x := by simp [ae_iff]
    filter_upwards [hne] with y hy
    have hy' : x ≠ y := Ne.symm hy
    simp only [MeasuredOrder.dimensionPairMean, Measure.smul_apply, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ.le]
    by_cases hc : O.Rel x y <;> simp [hc, hy']
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hρ.le, smul_eq_mul,
    integral_const_mul, he, Measure.smul_apply, ENNReal.toReal_mul]
  rw [show dimensionPointCoefficient d * (ρ * (μ univ).toReal) - dimensionPairCoefficient d *
      (ρ * (ρ * (∫ x, ∫ y in {y | O.Rel x y}, dimensionKernel d
        (ρ * (μ (O.interval x y)).toReal) ∂μ ∂μ))) =
      ρ * (dimensionPointCoefficient d * (μ univ).toReal - dimensionPairCoefficient d * ρ *
        (∫ x, ∫ y in {y | O.Rel x y}, dimensionKernel d
          (ρ * (μ (O.interval x y)).toReal) ∂μ ∂μ)) by ring,
    ← mul_assoc, dimensionNormalization_mul_density d hρ]
  rfl

end BoundaryDraft
