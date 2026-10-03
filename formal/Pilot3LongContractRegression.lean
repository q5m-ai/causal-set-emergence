import BoundaryDraft.Pilot3Tubes
import BoundaryDraft.Pilot3Components
import BoundaryDraft.Pilot3JointAtlas
import BoundaryDraft.Pilot3AtlasRegularity

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

-- Even exact cutoff contact kills the entire right fibre, for every direction.
example {h f : Pilot3Space → ℝ} {κ η δ v σ : ℝ} (C : Pilot3SlopeControl h f κ η)
    (hδ : 0 < δ) (hv : δ ≤ v) (hσ : 0 ≤ σ) (x θ : Pilot3Space) (hθ : ‖θ‖ = 1)
    (hg : pilot3RayGap h f x θ 0 δ = 0) : max 0 (pilot3RayGap h f x θ σ v) = 0 :=
  max_eq_left (C.rayGap_nonpos_of_cutoff_nonpos hδ hv hσ x θ hθ hg.le)

-- Actual first-endpoint signed overlap, not a supplied density.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (closure {x | 0 < h x})) (τ : ℝ) (b : Pilot3Space) (hc : ‖b‖ ≤ τ) :
    (∫ p in pilot3Region h f, w p.2 *
      (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p + (τ, b))) =
      ∫ x, w x * max 0 (max 0 (h x) + f (x + b) - f x - τ) :=
  hf.weightedOverlap_eq_gap w hw (τ, b) hc

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hc : ‖z.2‖ ≤ z.1) :
    Integrable (fun x => w x * max 0 (max 0 (h x) + f (x + z.2) - f x - z.1)) :=
  hf.integrable_weighted_overlapGap w hw z hc

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ κ η ε : ℝ, Pilot3SlopeControl h f κ η ∧
      ε = pilot3PerturbationWidth κ (1 - κ - η) δ ∧ 0 < ε ∧ ε < δ ^ 2 ∧
      ∀ (x θ : Pilot3Space) (v σ : ℝ), ‖θ‖ = 1 → δ ≤ v → σ ∈ Icc 0 ε →
        0 ≤ max 0 (h x) + f (x + (v / 2) • θ) - f x - v / 2 →
        x ∈ pilot3HeightTube h ((1 - κ - η) * δ / 2) ∧
        x + (v / 2) • θ ∈ pilot3HeightTube h ((1 - κ - η) * δ / 2) ∧
        x + ((v - σ / v) / 2) • θ ∈ pilot3HeightTube h ((1 - κ - η) * δ / 4) := by
  simpa only [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, zero_div, add_zero, sub_zero]
    using hf.exists_long_perturbationTube δ hδ

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (a : ℝ) (n : ℕ) :
    IsCompact (pilot3HeightTube h a) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ pilot3HeightTube h a, ‖iteratedFDeriv ℝ n f x‖ ≤ B :=
  ⟨hf.isCompact_heightTube a, hf.future_derivative_bounds a n⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) : ∃ V : ℝ, 0 < V ∧
    ∀ (x θ : Pilot3Space) (v σ : ℝ), ‖θ‖ = 1 → 0 < v → 0 ≤ σ →
      0 ≤ pilot3RayGap h f x θ σ v → v ≤ V := hf.exists_long_length_bound

example {θ : Pilot3Space} (hθ : ‖θ‖ = 1) {σ v : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖(pilot3RayDisplacement θ σ v).2‖ ≤ (pilot3RayDisplacement θ σ v).1 ∧
    (pilot3RayDisplacement θ σ v).1 + ‖(pilot3RayDisplacement θ σ v).2‖ = v ∧
    (pilot3RayDisplacement θ σ v).1 ^ 2 - ‖(pilot3RayDisplacement θ σ v).2‖ ^ 2 = σ :=
  ⟨pilot3RayDisplacement_causal hθ hv hσ, pilot3RayDisplacement_parameters hθ hv hσ⟩

-- The new height geometry does not assume a long overlap density or jet.
example {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h) : Nonempty (Pilot3CollarAtlas h) :=
  hh.exists_collarAtlas

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (A B : Pilot3CollarAtlas h) :
    (∑ i, A.localJointMeasure f i) = pilot3JointArea h f ∧
      (∑ i, A.localJointMeasure f i) = ∑ j, B.localJointMeasure f j :=
  ⟨A.sum_localJointMeasure hf, A.jointAtlas_independent hf B⟩

open scoped ContDiff

-- Each finite derivative order has its own bound on the SAME fixed rectangles.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (A : Pilot3CollarAtlas h) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ i, ∀ p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk,
      ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ => A.weightedLocalTerm f i q.1 q.2) p‖ ≤ B :=
  A.exists_uniform_weighted_derivative_bound f hf.future_smoothAt n
