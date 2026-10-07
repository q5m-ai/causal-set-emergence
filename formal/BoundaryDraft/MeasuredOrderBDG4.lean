import BoundaryDraft.DimensionMeasureExpectation

/-!
# The canonical four-dimensional measured-order bridge

These are specializations of the existing dimension-indexed observable and
finite-measure action, not competing definitions. All count/Mecke and factorial
integrability proofs are reused. The probability law remains `FinitePoisson.law`.
The general theorem needs only a measurable order and finite atomless measure;
standard Borel geometry is verified separately for the compact instances.
-/

open MeasureTheory Set
open scoped ENNReal Classical BigOperators
noncomputable section
namespace BoundaryDraft
namespace MeasuredOrderBDG4

variable {X : Type*} [MeasurableSpace X] (O : MeasuredOrder X)

abbrev discreteAction (ρ : ℝ) : Multiset X → ℝ := discreteDimensionAction O 4 ρ
abbrev action (μ : Measure X) (ρ : ℝ) : ℝ := dimensionFiniteMeasureAction O 4 μ ρ

/-- Exactly the original four signed layers and square-root normalization. -/
theorem discreteAction_eq {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset X) :
    discreteAction O ρ c = bdgNormalization ρ *
      ((c.card : ℝ) - O.layer 0 c + 9 * O.layer 1 c - 16 * O.layer 2 c + 8 * O.layer 3 c) := by
  have hn : ρ ^ (2 / (4 : ℝ) - 1) = (Real.sqrt ρ)⁻¹ := by
    rw [show 2 / (4 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hρ.le,
      ← Real.sqrt_eq_rpow]
  simp only [discreteAction, discreteDimensionAction, dimensionPointCoefficient_four,
    dimensionPairCoefficient_four, dimensionLayerWeight_four, Nat.cast_ofNat, hn]
  norm_num [dimensionFactorCount, Finset.sum_range_succ, bdgLayerWeight, bdgNormalization]
  ring

/-- Actual exclusive interval volume; both endpoint measures and both density
factors are retained. Null-related pairs are not removed by the causal mask. -/
theorem action_eq (μ : Measure X) (ρ : ℝ) :
    action O μ ρ = (4 / Real.sqrt 6) * Real.sqrt ρ * ((μ univ).toReal -
      ρ * ∫ x, ∫ y in {y | O.Rel x y},
        bdgKernel (ρ * (μ (O.interval x y)).toReal) ∂μ ∂μ) := by
  simp only [action, dimensionFiniteMeasureAction, dimensionPointCoefficient_four,
    dimensionPairCoefficient_four, dimensionKernel_four, Nat.cast_ofNat]
  rw [show 2 / (4 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

@[measurability] theorem measurable_discreteAction (ρ : ℝ) :
    Measurable (discreteAction O ρ) := measurable_discreteDimensionAction O 4 ρ

theorem integrable_discreteAction (μ : Measure X) [IsFiniteMeasure μ] (ρ : ℝ) :
    Integrable (discreteAction O ρ) (FinitePoisson.law μ) :=
  integrable_discreteDimensionAction O 4 ρ μ

/-- Exact count/Mecke bridge, obtained from the existing generic proof. -/
theorem expectation_eq (μ : Measure X) [IsFiniteMeasure μ] [NoAtoms μ]
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteAction O ρ c ∂FinitePoisson.law (ENNReal.ofReal ρ • μ)) = action O μ ρ :=
  dimensionFiniteMeasureAction_expectation O 4 μ hρ

/-- The interval indicator is the actual jointly measurable exclusive interval,
not a separately supplied rate function. -/
theorem measurable_intervalVolume (μ : Measure X) [SFinite μ] :
    Measurable (fun p : X × X => (μ (O.interval p.1 p.2)).toReal) :=
  (measurable_measure_prodMk_left O.measurable_interval_joint).ennreal_toReal

theorem intervalVolume_bounds (μ : Measure X) [IsFiniteMeasure μ] (x y : X) :
    0 ≤ (μ (O.interval x y)).toReal ∧ (μ (O.interval x y)).toReal ≤ (μ univ).toReal :=
  ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (subset_univ _))⟩

/-- Joint measurability includes the density parameter. -/
theorem measurable_kernel (μ : Measure X) [SFinite μ] :
    Measurable (fun p : ℝ × (X × X) =>
      bdgKernel (p.1 * (μ (O.interval p.2.1 p.2.2)).toReal)) := by
  have hc : Continuous bdgKernel := by unfold bdgKernel bdgPolynomial; fun_prop
  exact hc.measurable.comp
    (measurable_fst.mul ((measurable_intervalVolume O μ).comp measurable_snd))

theorem integrable_kernel (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure X) [IsFiniteMeasure ν] :
    Integrable (fun p : X × X => bdgKernel (μ (O.interval p.1 p.2)).toReal) (ν.prod ν) := by
  simpa only [dimensionKernel_four] using O.integrable_dimensionKernel μ 4 ν

/-- Unnormalized intensity version, exposing the two factorial density factors
before the physical normalization. It also retains a possible atomic diagonal. -/
theorem integral_action (μ : Measure X) [IsFiniteMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteAction O ρ c ∂FinitePoisson.law μ) = bdgNormalization ρ *
      ((μ univ).toReal - ∫ x, ∫ y,
        if O.Rel x y ∧ x ≠ y then bdgKernel (μ (O.interval x y)).toReal else 0 ∂μ ∂μ) := by
  rw [O.integral_discreteDimensionAction]
  have hn : ρ ^ (2 / (4 : ℝ) - 1) = (Real.sqrt ρ)⁻¹ := by
    rw [show 2 / (4 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hρ.le,
      ← Real.sqrt_eq_rpow]
  simp only [dimensionPointCoefficient_four, dimensionPairCoefficient_four,
    MeasuredOrder.dimensionPairMean, dimensionKernel_four, Nat.cast_ofNat, hn, bdgNormalization]
  ring

end MeasuredOrderBDG4
end BoundaryDraft
