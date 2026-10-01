import BoundaryDraft.DimensionExpectation
import BoundaryDraft.PoissonTransport
import BoundaryDraft.ExpectationBridge

/-!
# Exact recovery of the unchanged four-dimensional discrete and expected action

The coordinate equivalence from #91 transports each configuration, its complete
closed order and exclusive intervals, and the actual Poisson probability law.
Consequently expectation compatibility needs only finite volume: it does not
assume causal convexity or either deterministic expectation bridge.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- Counts agree on every multiset, including multiplicities and null intervals. -/
theorem dimensionIntervalCount_four (x y : DimensionSpacetime 3) (c : Multiset (DimensionSpacetime 3)) :
    intervalCount (dimensionSpacetimeCoordinates 3 x) (dimensionSpacetimeCoordinates 3 y)
      (c.map (dimensionSpacetimeCoordinates 3)) = (dimensionMeasuredOrder 3).intervalCount x y c := by
  have hm (z : DimensionSpacetime 3) : dimensionSpacetimeCoordinates 3 z ∈
      causalIntervalInterior (dimensionSpacetimeCoordinates 3 x) (dimensionSpacetimeCoordinates 3 y) ↔
      z ∈ dimensionCausalIntervalInterior x y := by
    rw [← dimensionSpacetimeCoordinates_intervalInterior]
    exact (dimensionSpacetimeCoordinates 3).injective.mem_set_image
  induction c using Multiset.induction_on with
  | empty => simp [intervalCount, MeasuredOrder.intervalCount]
  | cons z c ih =>
    simpa only [intervalCount, MeasuredOrder.intervalCount, Multiset.map_cons,
      FiniteConfiguration.count_cons, hm, dimensionMeasuredOrder_interval] using
        congrArg (fun a : ℕ => a + if z ∈ dimensionCausalIntervalInterior x y then 1 else 0) ih

theorem dimensionLayer_four (k : ℕ) (c : Multiset (DimensionSpacetime 3)) :
    (dimensionMeasuredOrder 3).layer k c = intervalLayer k (c.map (dimensionSpacetimeCoordinates 3)) := by
  simp only [MeasuredOrder.layer, MeasuredOrder.intervalPairSum_eq_sum, intervalLayer,
    intervalPairSum_eq_sum, Multiset.map_map, Function.comp_def, dimensionIntervalCount_four,
    dimensionSpacetimeCoordinates_causal, (dimensionSpacetimeCoordinates 3).injective.ne_iff]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  by_cases h : y ∈ dimensionCausalFuture x ∧ x ≠ y <;>
    simp [MeasuredOrder.Rel, dimensionMeasuredOrder, dimensionCausalOrder, h]

/-- Equality of actual finite-order observables, not only their coefficients. -/
theorem discreteDimensionAction_four {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset (DimensionSpacetime 3)) :
    discreteDimensionAction (dimensionMeasuredOrder 3) 4 ρ c =
      discreteBDGAction ρ (c.map (dimensionSpacetimeCoordinates 3)) := by
  have hn : ρ ^ (2 / (4 : ℝ) - 1) = (Real.sqrt ρ)⁻¹ := by
    rw [show 2 / (4 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hρ.le,
      ← Real.sqrt_eq_rpow]
  simp only [discreteDimensionAction, dimensionPointCoefficient_four, dimensionPairCoefficient_four,
    dimensionLayerWeight_four, dimensionLayer_four, Nat.cast_ofNat, hn, discreteBDGAction, Multiset.card_map]
  norm_num [dimensionFactorCount, Finset.sum_range_succ, bdgLayerWeight, bdgNormalization]
  ring

/-- The very same finite sprinkling expressed in the original four coordinates. -/
def DimensionSprinkling.toFour (S : DimensionSprinkling 3) : FiniteSprinkling where
  region := dimensionSpacetimeCoordinates 3 '' S.region
  measurable_region := (dimensionSpacetimeCoordinates 3).measurableEmbedding.measurableSet_image.mpr
    S.measurable_region
  finite_volume := by rw [dimensionSpacetimeCoordinates_volume_image]; exact S.finite_volume
  density := S.density
  density_pos := S.density_pos

/-- Measure-level recovery of the original probability, stronger than comparing
expectations through a common deterministic integral. -/
theorem DimensionSprinkling.four_probability (S : DimensionSprinkling 3) :
    MeasurePreserving (FiniteConfiguration.mapEquiv (dimensionSpacetimeCoordinates 3))
      S.probability S.toFour.probability := by
  apply FinitePoisson.measurePreserving_mapEquiv _ S.intensity S.toFour.intensity
  exact ((dimensionSpacetimeCoordinates_measurePreserving 3).restrict_image_emb
    (dimensionSpacetimeCoordinates 3).measurableEmbedding S.region).smul_measure (ENNReal.ofReal S.density)

/-- Exact unchanged expectedBDGAction for any measurable finite-volume region,
including non-convex ones. No continuum identity is used to prove transport. -/
theorem dimensionExpectedAction_four {ρ : ℝ} (hρ : 0 < ρ) {M : Set (DimensionSpacetime 3)}
    (hM : MeasurableSet M) (hv : volume M < ∞) :
    dimensionExpectedAction 3 ρ M = expectedBDGAction ρ (dimensionSpacetimeCoordinates 3 '' M) := by
  let S : DimensionSprinkling 3 := ⟨M, hM, hv, ρ, hρ⟩
  have h := S.four_probability.integral_comp'
    (f := FiniteConfiguration.mapEquiv (dimensionSpacetimeCoordinates 3)) (discreteBDGAction ρ)
  change (∫ c, discreteDimensionAction (dimensionMeasuredOrder 3) 4 ρ c ∂S.probability) =
    ∫ c, discreteBDGAction ρ c ∂S.toFour.probability
  simp_rw [discreteDimensionAction_four hρ]
  exact h

end BoundaryDraft
