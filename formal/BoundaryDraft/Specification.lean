import BoundaryDraft.Algebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Definitions and UNPROVED targets

Every name ending in `Goal` below is a DEFINITION OF A PROPOSITION, not a
proved theorem, not an axiom, and not an instance of that proposition.

The main targets refer to the actual four-dimensional deterministic continuum
integral, not an action defined to equal its expected limiting answer.
The separate identification of that integral with a Poisson expectation is
not yet formalized.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators

noncomputable section

namespace BoundaryDraft

/-- Coordinates (t,x,y,z), with product Lebesgue measure. The norm of this
function space is NOT used as a Lorentzian norm. -/
abbrev Spacetime := Fin 4 → ℝ
abbrev Spatial := Fin 3 → ℝ

def spatialPart (x : Spacetime) : Spatial := fun i => x i.succ

def spatialSeparationSq (x y : Spacetime) : ℝ :=
  ∑ i : Fin 3, (y i.succ - x i.succ) ^ 2

/-- Squared Minkowski proper time; used on causally related pairs. -/
def intervalSq (x y : Spacetime) : ℝ :=
  (y 0 - x 0) ^ 2 - spatialSeparationSq x y

def causalFuture (x : Spacetime) : Set Spacetime :=
  {y | x 0 ≤ y 0 ∧ spatialSeparationSq x y ≤ (y 0 - x 0) ^ 2}

def chronologicalFuture (x : Spacetime) : Set Spacetime :=
  {y | x 0 < y 0 ∧ spatialSeparationSq x y < (y 0 - x 0) ^ 2}

def bdgKernel (z : ℝ) : ℝ := bdgPolynomial z * Real.exp (-z)

/-- Equation (2) of the draft, normalized as l_p² E[S]/hbar when the
unformalized Poisson-counting bridge and causal convexity apply. -/
def continuumMean (ρ : ℝ) (M : Set Spacetime) : ℝ :=
  (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ _x in M, (1 : ℝ)) - ρ *
      ∫ x in M, ∫ y in M ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * ρ * (intervalSq x y) ^ 2))

def pastTip (T : ℝ) : Spacetime := fun i => if i = 0 then -T else 0

/-- The first spatial axis is the z-axis of the paper's t-z > -a cut. -/
def nullCapRegion (T a : ℝ) : Set Spacetime :=
  {x | x ∈ chronologicalFuture (pastTip T) ∧
    (0 : Spacetime) ∈ chronologicalFuture x ∧ -a < x 0 - x 1}

/-- Full four-dimensional null-truncation target. NOT PROVED. -/
def NullCapLimitGoal : Prop :=
  ∀ T a : ℝ, 0 < a → a < T →
    Tendsto (fun ρ => continuumMean ρ (nullCapRegion T a))
      atTop (𝓝 (nullJointArea T a))

def graphCapRegion (h : Spatial → ℝ) : Set Spacetime :=
  {x | -h (spatialPart x) < x 0 ∧ x 0 < 0}

def ellipsoidProfile (a : ℝ) (b : Fin 3 → ℝ) (x : Spatial) : ℝ :=
  a * (1 - ∑ i : Fin 3, (x i / b i) ^ 2)

/-- Full four-dimensional target for the explicit family with variable angle.
Its hypotheses force positive axes and strict spacelikeness. NOT PROVED. -/
def EllipsoidLimitGoal : Prop :=
  ∀ (a : ℝ) (b : Fin 3 → ℝ), 0 < a → (∀ i, 2 * a < b i) →
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b)))
      atTop (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a))

/-- The concrete auxiliary integral, rather than an arbitrary kernel. -/
def planeAuxiliary (ρ H : ℝ) : ℝ :=
  4 * Real.pi * ∫ r in (0 : ℝ)..H,
    r ^ 2 * Real.exp (-(Real.pi / 24) * ρ * (H ^ 2 - r ^ 2) ^ 2)

def planeKernel (ρ H : ℝ) : ℝ :=
  Real.sqrt ρ / (2 * Real.pi * Real.sqrt 6) *
    deriv (deriv (planeAuxiliary ρ)) H

/-- A per-profile obligation, to be established only for admissible graph
caps. This does not assert that the reduction holds for arbitrary h. -/
def GraphReductionGoal (h : Spatial → ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    continuumMean ρ (graphCapRegion h) =
      ∫ x in {x | 0 < h x}, planeKernel ρ (h x)

/-- Analytic obligations for the specific signed BDG kernel. NOT PROVED. -/
def KernelMassGoal : Prop :=
  IntegrableOn (planeKernel 1) (Ioi (0 : ℝ)) ∧
    (∫ u in Ioi (0 : ℝ), planeKernel 1 u) = 1 ∧
    IntegrableOn (fun u => u * |planeKernel 1 u|) (Ioi (0 : ℝ))

/-- A bound adequate for the non-collar part of a general graph cap.
This is a target, not an assumed estimate. NOT PROVED. -/
def KernelTailGoal : Prop :=
  ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
    ∀ u : ℝ, R ≤ u → |planeKernel 1 u| ≤ C / u ^ 3

end BoundaryDraft
