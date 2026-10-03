import BoundaryDraft.Pilot3Geometry
import BoundaryDraft.Pilot3Components

/-! Standalone #78 consumer contracts: geometry and actual finite-density
normalization, NOT an assumed overlap density, jet or long cancellation. -/

open BoundaryDraft MeasureTheory Set
open scoped Topology
noncomputable section

example (h f : EuclideanSpace ℝ (Fin 2) → ℝ) :
    pilot3Region h f = {p : ℝ × EuclideanSpace ℝ (Fin 2) | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2} := rfl

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    IsOpen (pilot3Region h f) ∧ MeasurableSet (pilot3Region h f) ∧
      Bornology.IsBounded (pilot3Region h f) ∧ volume (pilot3Region h f) < ⊤ :=
  ⟨hf.isOpen_region, hf.measurableSet_region, hf.isBounded_region, hf.isBounded_region.measure_lt_top⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
    (p q z : Pilot3Spacetime) (hp : p ∈ pilot3Region h f) (hq : q ∈ pilot3Region h f)
    (hzp : ‖z.2 - p.2‖ ≤ z.1 - p.1) (hqz : ‖q.2 - z.2‖ ≤ q.1 - z.1) :
    z ∈ pilot3Region h f := hf.causallyConvex_region p hp q hq ⟨hzp, hqz⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ c, discreteDimensionAction (dimensionMeasuredOrder 2) 3 ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict
        {p : Pilot3Spacetime | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2})) =
      ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * (∫ _p in pilot3Region h f, (1 : ℝ)) -
        dimensionPairCoefficient 3 * ρ * ∫ p in pilot3Region h f,
          ∫ q in pilot3Region h f ∩ dimensionCausalFuture p,
            dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ *
              ((q.1 - p.1) ^ 2 - ‖q.2 - p.2‖ ^ 2) ^ (3 / 2 : ℝ))) := by
  simpa only [dimensionExpectedAction, pilot3Action, dimensionWeightedAction,
    dimensionBilocalKernel, dimensionIntervalSq, pilot3Region, one_mul, Nat.reduceAdd,
    Nat.cast_ofNat] using hf.expectedAction_eq hρ

example {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ closure {x | 0 < h x}, h x ≤ δ → fderiv ℝ h x ≠ 0 :=
  hh.exists_noncritical_band

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    frontier (pilot3Region h f) =
      ((fun x : Pilot3Space => (f x - h x, x)) '' closure {x | 0 < h x}) ∪
      ((fun x : Pilot3Space => (f x, x)) '' closure {x | 0 < h x}) := hf.frontier_region

example (h₁ h₂ f : Pilot3Space → ℝ) :
    pilot3Region (fun x => max (h₁ x) (h₂ x)) f = pilot3Region h₁ f ∪ pilot3Region h₂ f :=
  pilot3Region_max h₁ h₂ f

example {h k f : Pilot3Space → ℝ} (he : ∀ x, max 0 (h x) = max 0 (k x)) :
    pilot3Region h f = pilot3Region k f := pilot3Region_eq_of_positivePart_eq he
