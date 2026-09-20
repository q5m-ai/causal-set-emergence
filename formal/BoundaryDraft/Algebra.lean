import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact algebra used in the paper proof. These results alone do not verify
any exchange of limits, differentiation, integration, or geometric measure. -/

noncomputable section

namespace BoundaryDraft

/-- Polynomial multiplying exp(-z) in the four-dimensional mean action. -/
def bdgPolynomial (z : ℝ) : ℝ :=
  1 - 9 * z + 8 * z ^ 2 - (4 / 3 : ℝ) * z ^ 3

/-- Factor remaining after multiplying the exponential series coefficients
by the BDG polynomial. -/
def coefficientFactor (n : ℝ) : ℝ :=
  (n + 1) * (2 * n + 1) * (2 * n + 3) / 3

theorem coefficient_factorization (n : ℝ) :
    1 + 9 * n + 8 * n * (n - 1) +
      (4 / 3 : ℝ) * n * (n - 1) * (n - 2) = coefficientFactor n := by
  unfold coefficientFactor
  ring

/-- The coefficient cancellation for every natural-number interval moment.
The formula for the interval moment itself remains an analytic obligation. -/
theorem interval_moment_cancellation (n : ℕ) :
    Real.pi * coefficientFactor (n : ℝ) /
        ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) *
          (2 * (n : ℝ) + 3) * (4 * (n : ℝ) + 4)) =
      (Real.pi / 24) / ((n : ℝ) + 1) := by
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h4 : (4 * (n : ℝ) + 4) ≠ 0 := by positivity
  have h5 : ((n : ℝ) + 1) ≠ 0 := by positivity
  unfold coefficientFactor
  field_simp
  ring

/-- Polynomial form of the beta-function recurrence used in the plane-cap
calculation. Establishing the beta integral representation is separate. -/
theorem plane_coefficient_recurrence (n : ℝ) :
    2 * (4 * n + 2) * (2 * n) * (2 * n - 1) =
      24 * coefficientFactor (n - 1) := by
  unfold coefficientFactor
  ring

def nullJointArea (T a : ℝ) : ℝ := Real.pi * a * (2 * T - a)

theorem null_joint_area_decomposition (T a : ℝ) :
    Real.pi * a * T + Real.pi * a * (T - a) = nullJointArea T a := by
  unfold nullJointArea
  ring

theorem uncut_joint_area (T : ℝ) :
    nullJointArea T T = Real.pi * T ^ 2 := by
  unfold nullJointArea
  ring

/-- The square of the claimed angle weight, conditional on the geometric
cosh-squared relation. Choosing the positive square root is a separate step. -/
theorem angle_weight_squared (k : ℝ) (hk : 0 < k) (hk1 : k < 1) :
    (1 / (1 - k ^ 2)) / (1 / (1 - k ^ 2) - 1) = 1 / k ^ 2 := by
  have hkn : k ≠ 0 := ne_of_gt hk
  have hden : 1 - k ^ 2 ≠ 0 := by nlinarith
  field_simp

end BoundaryDraft
