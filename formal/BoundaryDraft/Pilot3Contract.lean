import BoundaryDraft.DimensionExpectation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# The smooth three-dimensional two-graph pilot

This is exactly the combined-budget class in §1 of
`notes/dimension-two-face-geometry.md`, not the independent-envelope class E.
Physical dimension three means `DimensionSpacetime 2`. Smoothness is an
ambient smooth germ on an open neighborhood, not smoothness of the clipped
height. No analytic conclusion is an admissibility field.

The canonical candidate target is specified from the actual gradients and
one-dimensional diameter-Hausdorff measure (normalization factor one).
Finiteness, positivity, and chart identification are separate obligations;
none is smuggled into the goal propositions or the geometric data.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
noncomputable section
namespace BoundaryDraft

abbrev Pilot3Space := DimensionSpatial 2
abbrev Pilot3Spacetime := DimensionSpacetime 2

def pilot3ClosedPositive (h : Pilot3Space → ℝ) : Set Pilot3Space :=
  closure {x | 0 < h x}

def pilot3SpatialJoint (h : Pilot3Space → ℝ) : Set Pilot3Space :=
  pilot3ClosedPositive h ∩ {x | h x = 0}

/-- Slope-independent regular-height data. In particular, critical points at
positive height are permitted, and exterior raw data are unrestricted. -/
structure Pilot3RegularHeight (h : Pilot3Space → ℝ) : Prop where
  bounded_positive : Bornology.IsBounded {x | 0 < h x}
  smooth_near : ∀ x ∈ pilot3ClosedPositive h, ∃ U : Set Pilot3Space,
    IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ h U
  zero_frontier : ∀ x ∈ frontier {x | 0 < h x}, h x = 0
  regular_zero : ∀ x ∈ pilot3ClosedPositive h, h x = 0 → fderiv ℝ h x ≠ 0

/-- Exactly `CandidateTwoFace(3,infinity;h,f)`. The two constants share a
strict combined budget. No jet, measure, coarea, expectation or limit field. -/
structure SmoothPilot3 (h f : Pilot3Space → ℝ) : Prop extends Pilot3RegularHeight h where
  smooth_future : ∀ x ∈ pilot3ClosedPositive h, ∃ U : Set Pilot3Space,
    IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ f U
  slope_budget : ∃ κ η : ℝ, 0 ≤ κ ∧ 0 ≤ η ∧ κ + η < 1 ∧
    (∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * ‖y - x‖) ∧
    (∀ x y, |f x - f y| ≤ η * ‖y - x‖)

def pilot3Region (h f : Pilot3Space → ℝ) : Set Pilot3Spacetime :=
  {p | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2}

def pilot3Lift (f : Pilot3Space → ℝ) (x : Pilot3Space) : Pilot3Spacetime := (f x, x)

def pilot3Past (h f : Pilot3Space → ℝ) : Set Pilot3Spacetime :=
  pilot3Lift (fun x => f x - h x) '' pilot3ClosedPositive h

def pilot3Future (h f : Pilot3Space → ℝ) : Set Pilot3Spacetime :=
  pilot3Lift f '' pilot3ClosedPositive h

def pilot3Joint (h f : Pilot3Space → ℝ) : Set Pilot3Spacetime :=
  pilot3Lift f '' pilot3SpatialJoint h

/-- The actual differential's Euclidean Riesz representative. -/
def pilot3Gradient (f : Pilot3Space → ℝ) (x : Pilot3Space) : Pilot3Space := gradient f x

def pilot3Inward (h : Pilot3Space → ℝ) (x : Pilot3Space) : Pilot3Space :=
  ‖pilot3Gradient h x‖⁻¹ • pilot3Gradient h x

/-- Future normal, including the inward normal on the past face. -/
def pilot3Normal (f : Pilot3Space → ℝ) (x : Pilot3Space) : Pilot3Spacetime :=
  (Real.sqrt (1 - ‖pilot3Gradient f x‖ ^ 2))⁻¹ • (1, pilot3Gradient f x)

def pilot3Cosh (h f : Pilot3Space → ℝ) (x : Pilot3Space) : ℝ :=
  dimensionMinkowski 2 (pilot3Normal (fun y => f y - h y) x) (pilot3Normal f x)

def pilot3Angle (h f : Pilot3Space → ℝ) (x : Pilot3Space) : ℝ :=
  Real.log (pilot3Cosh h f x + Real.sqrt (pilot3Cosh h f x ^ 2 - 1))

def pilot3Weight (h f : Pilot3Space → ℝ) (x : Pilot3Space) : ℝ :=
  pilot3Cosh h f x / Real.sqrt (pilot3Cosh h f x ^ 2 - 1)

/-- The positive Lorentzian Gram form on graph tangents; not the Euclidean
spacetime metric. Its restriction to the joint is used below. -/
def pilot3TangentMetric (f : Pilot3Space → ℝ) (x v w : Pilot3Space) : ℝ :=
  inner (𝕜 := ℝ) v w - fderiv ℝ f x v * fderiv ℝ f x w

def pilot3TangentialGradient (h f : Pilot3Space → ℝ) (x : Pilot3Space) : Pilot3Space :=
  pilot3Gradient f x -
    inner (𝕜 := ℝ) (pilot3Gradient f x) (pilot3Inward h x) • pilot3Inward h x

def pilot3AreaDensity (h f : Pilot3Space → ℝ) (x : Pilot3Space) : ℝ :=
  Real.sqrt (1 - ‖pilot3TangentialGradient h f x‖ ^ 2)

/-- Diameter-Hausdorff one-measure: the line normalization is one, NOT pi/4. -/
def pilot3SurfaceMeasure (h : Pilot3Space → ℝ) : Measure Pilot3Space :=
  (μH[1] : Measure Pilot3Space).restrict (pilot3SpatialJoint h)

def pilot3ProjectedArea (h f : Pilot3Space → ℝ) : Measure Pilot3Space :=
  (pilot3SurfaceMeasure h).withDensity (fun x => ENNReal.ofReal (pilot3AreaDensity h f x))

def pilot3JointArea (h f : Pilot3Space → ℝ) : Measure Pilot3Spacetime :=
  Measure.map (pilot3Lift f) (pilot3ProjectedArea h f)

/-- Fixed independently of the action. Its intrinsic chart interpretation
is a theorem obligation, not an arbitrary supplied measure. -/
def pilot3BoundaryIntegral (h f : Pilot3Space → ℝ) : ℝ :=
  ∫ x, pilot3Weight h f x ∂pilot3ProjectedArea h f

/-- The EXISTING dimension-indexed action at physical dimension three. -/
def pilot3Action (ρ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  dimensionWeightedAction 2 (dimensionPointCoefficient 3) (dimensionPairCoefficient 3)
    (dimensionIntervalCoefficient 3) ρ (pilot3Region h f) (fun _ => 1)

/-- Independently stated deterministic target, proved separately in `Pilot3Limit`. -/
def Pilot3DeterministicGoal : Prop :=
  ∀ h f, SmoothPilot3 h f →
    Tendsto (fun ρ => pilot3Action ρ h f) atTop (𝓝 (pilot3BoundaryIntegral h f))

/-- Independently stated expected-action target, proved separately in `Pilot3Limit`.
It uses the constructed Poisson law and actual discrete action, not an
expectation defined as a continuum action. -/
def Pilot3ExpectedGoal : Prop :=
  ∀ h f, SmoothPilot3 h f →
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region h f))
      atTop (𝓝 (pilot3BoundaryIntegral h f))

end BoundaryDraft
