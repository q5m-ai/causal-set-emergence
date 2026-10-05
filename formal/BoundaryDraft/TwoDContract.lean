import BoundaryDraft.DimensionTwoEndpoints

/-!
# Smooth combined-budget flat two-dimensional contract

Physical dimension two means ONE spatial coordinate. This is #92's smooth
candidate, not a relabelled three-dimensional theorem. All components and
positive-height critical points are retained. The target is fixed from the
actual normals and the existing zero-dimensional Hausdorff measure BEFORE
any action asymptotics. The unchanged limit propositions below are proved
unconditionally in `TwoDLimit`, with expectation transfer performed afterward.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

abbrev TwoDSpace := DimensionSpatial 1
abbrev TwoDSpacetime := DimensionSpacetime 1

def twoDClosedPositive (h : TwoDSpace → ℝ) : Set TwoDSpace := closure {x | 0 < h x}

/-- Geometric hypotheses only. Empty members are permitted, but no component
or endpoint of a nonempty member may be selected away. -/
structure SmoothTwoD (h f : TwoDSpace → ℝ) : Prop where
  bounded_positive : Bornology.IsBounded {x | 0 < h x}
  smooth_height : ∀ x ∈ twoDClosedPositive h, ∃ U : Set TwoDSpace,
    IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ h U
  zero_frontier : ∀ x ∈ frontier {x | 0 < h x}, h x = 0
  regular_zero : ∀ x ∈ twoDClosedPositive h, h x = 0 → fderiv ℝ h x ≠ 0
  smooth_future : ∀ x ∈ twoDClosedPositive h, ∃ U : Set TwoDSpace,
    IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ f U
  slope_budget : ∃ κ η : ℝ, 0 ≤ κ ∧ 0 ≤ η ∧ κ + η < 1 ∧
    (∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * ‖y - x‖) ∧
    (∀ x y, |f x - f y| ≤ η * ‖y - x‖)

def twoDRegion (h f : TwoDSpace → ℝ) : Set TwoDSpacetime :=
  {p | f p.2 - h p.2 < p.1 ∧ p.1 < f p.2}

def twoDLift (f : TwoDSpace → ℝ) (x : TwoDSpace) : TwoDSpacetime := (f x, x)

def twoDJoint (h f : TwoDSpace → ℝ) : Set TwoDSpacetime :=
  twoDLift f '' dimensionTwoSpatialJoint h

def twoDGradient (f : TwoDSpace → ℝ) (x : TwoDSpace) : TwoDSpace := gradient f x

def twoDUnitNormal (v : TwoDSpace) : TwoDSpacetime :=
  (Real.sqrt (1 - ‖v‖ ^ 2))⁻¹ • (1, v)

/-- Future-directed normal on either face (inward on the past face). -/
def twoDNormal (f : TwoDSpace → ℝ) (x : TwoDSpace) : TwoDSpacetime :=
  twoDUnitNormal (twoDGradient f x)

def twoDCosh (h f : TwoDSpace → ℝ) (x : TwoDSpace) : ℝ :=
  dimensionMinkowski 1 (twoDNormal (fun y => f y - h y) x) (twoDNormal f x)

def twoDAngle (h f : TwoDSpace → ℝ) (x : TwoDSpace) : ℝ :=
  Real.log (twoDCosh h f x + Real.sqrt (twoDCosh h f x ^ 2 - 1))

def twoDWeight (h f : TwoDSpace → ℝ) (x : TwoDSpace) : ℝ :=
  twoDCosh h f x / Real.sqrt (twoDCosh h f x ^ 2 - 1)

/-- A zero-dimensional tangent metric has empty Gram determinant one.
Use the PRE-EXISTING canonical unit endpoint measure, not a fitted coefficient. -/
def twoDJointArea (h f : TwoDSpace → ℝ) : Measure TwoDSpacetime :=
  Measure.map (twoDLift f) (dimensionTwoJointMeasure h)

def twoDBoundaryIntegral (h f : TwoDSpace → ℝ) : ℝ :=
  ∫ x, twoDWeight h f x ∂dimensionTwoJointMeasure h

/-- The unchanged unsmeared dimension-indexed action. -/
def twoDAction (ρ : ℝ) (h f : TwoDSpace → ℝ) : ℝ :=
  dimensionWeightedAction 1 (dimensionPointCoefficient 2) (dimensionPairCoefficient 2)
    (dimensionIntervalCoefficient 2) ρ (twoDRegion h f) (fun _ => 1)

/-- Deterministic limit contract, NOT an admissibility field. Its proof term
is `twoDDeterministicGoal` in `TwoDLimit`. -/
def TwoDDeterministicGoal : Prop :=
  ∀ h f, SmoothTwoD h f →
    Tendsto (fun ρ => twoDAction ρ h f) atTop (𝓝 (twoDBoundaryIntegral h f))

/-- Independently constructed Poisson law and actual discrete observable. -/
def TwoDExpectedGoal : Prop :=
  ∀ h f, SmoothTwoD h f →
    Tendsto (fun ρ => dimensionExpectedAction 1 ρ (twoDRegion h f))
      atTop (𝓝 (twoDBoundaryIntegral h f))

end BoundaryDraft
