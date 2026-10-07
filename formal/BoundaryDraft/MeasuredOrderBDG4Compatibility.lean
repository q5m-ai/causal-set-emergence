import BoundaryDraft.MeasuredOrderBDG4
import BoundaryDraft.DimensionExpectationCompatibility
import BoundaryDraft.ConformalAction

/-!
# Compatibility with the unchanged coordinate, dimensional and conformal APIs

These are equalities of actual observables and of the constructed laws, not
comparisons through a postulated common expectation. No old definition changes.
-/

open MeasureTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft
namespace MeasuredOrderBDG4

/-- Original Minkowski order, explicitly supplied rather than coordinatewise order. -/
def coordinateOrder : MeasuredOrder Spacetime where
  order := {
    le := fun x y => y ∈ causalFuture x
    lt := fun x y => y ∈ causalFuture x ∧ ¬ x ∈ causalFuture y
    le_refl := causalFuture_refl
    le_trans := fun _ _ _ => causalFuture_trans
    le_antisymm := fun _ _ => causalFuture_antisymm }
  measurable_rel := measurableSet_causalRelation

@[simp] theorem coordinate_rel (x y : Spacetime) :
    coordinateOrder.Rel x y ↔ y ∈ causalFuture x := Iff.rfl

@[simp] theorem coordinate_interval (x y : Spacetime) :
    coordinateOrder.interval x y = causalIntervalInterior x y := rfl

@[simp] theorem coordinate_intervalCount (x y : Spacetime) (c : Multiset Spacetime) :
    coordinateOrder.intervalCount x y c = intervalCount x y c := rfl

@[simp] theorem coordinate_layer (k : ℕ) (c : Multiset Spacetime) :
    coordinateOrder.layer k c = intervalLayer k c := by
  simp only [MeasuredOrder.layer, intervalLayer, MeasuredOrder.intervalPairSum,
    intervalPairSum, coordinate_intervalCount, coordinate_rel]

/-- This holds on every multiset, including multiplicities and null pairs. -/
theorem coordinate_discreteAction {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset Spacetime) :
    discreteAction coordinateOrder ρ c = discreteBDGAction ρ c := by
  simp only [discreteAction_eq _ hρ, coordinate_layer, discreteBDGAction]

/-- Deterministic compatibility needs neither finiteness nor causal convexity. -/
theorem coordinate_action (μ : Measure Spacetime) (ρ : ℝ) :
    action coordinateOrder μ ρ = finiteMeasureAction μ ρ := by
  rw [action_eq]
  rfl

theorem coordinate_layerMean (μ : Measure Spacetime) (k : ℕ) (x y : Spacetime) :
    coordinateOrder.layerMean μ k x y = FiniteMeasureBDG.layerMean μ k x y := by
  simp only [MeasuredOrder.layerMean, FiniteMeasureBDG.layerMean,
    MeasuredOrder.layerProbability, FiniteMeasureBDG.layerProbability,
    coordinate_interval, coordinate_rel]

/-- The actual original flat probability and discrete observable are recovered. -/
theorem flat_expectedAction {ρ : ℝ} (hρ : 0 < ρ) (M : Set Spacetime) :
    (∫ c, discreteAction coordinateOrder ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict M)) = expectedBDGAction ρ M := by
  simp only [coordinate_discreteAction hρ]
  rfl

theorem conformal_probability (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) :
    FinitePoisson.law (ENNReal.ofReal ρ • (conformalVolume Ω).restrict M) =
      conformalProbability Ω ρ M := rfl

theorem conformal_action (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) :
    action coordinateOrder ((conformalVolume Ω).restrict M) ρ = conformalAction Ω ρ M :=
  coordinate_action _ _

theorem conformal_expectedAction (Ω : Spacetime → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (M : Set Spacetime) :
    (∫ c, discreteAction coordinateOrder ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • (conformalVolume Ω).restrict M)) =
      conformalExpectedAction Ω ρ M := by
  simp only [coordinate_discreteAction hρ]
  rfl

/-- Applicable dimension-indexed compatibility includes the original coordinate
transport, with its existing law-level proof left intact. -/
theorem dimension_discreteAction {ρ : ℝ} (hρ : 0 < ρ)
    (c : Multiset (DimensionSpacetime 3)) :
    discreteAction (dimensionMeasuredOrder 3) ρ c =
      discreteBDGAction ρ (c.map (dimensionSpacetimeCoordinates 3)) :=
  discreteDimensionAction_four hρ c

end MeasuredOrderBDG4
end BoundaryDraft
