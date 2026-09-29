import BoundaryDraft.NullTransverseMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Dimension-indexed BDG kernel algebra

The finite polynomial recurrence implements Glaser's operator with
`H = d * z * d/dz`. The Mellin multiplier is a separate algebraic object:
its identification with a general-dimensional integral is proved conventionally
in `notes/dimension-kernels.md`, not assumed or asserted here.
The four-dimensional integral regression uses the existing checked theorem.
No general-dimensional expectation bridge or localization theorem is asserted.
-/

open Finset Polynomial
noncomputable section
namespace BoundaryDraft

/-- Number of operator factors; the number of interval layers is one larger. -/
def dimensionFactorCount (d : ℕ) : ℕ := d / 2 + 1

/-- Polynomial after applying the first `m` normalized Euler factors. -/
def dimensionPolynomialStage (d : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | m + 1 =>
    let p := dimensionPolynomialStage d m
    p + C ((d : ℝ) / (2 * (m + 1))) * X * (derivative p - p)

def dimensionPolynomial (d : ℕ) : Polynomial ℝ :=
  dimensionPolynomialStage d (dimensionFactorCount d)

def dimensionKernel (d : ℕ) (z : ℝ) : ℝ :=
  (dimensionPolynomial d).eval z * Real.exp (-z)

/-- Algebraic Mellin multiplier, not an integral by definition. -/
def dimensionMellinFactor (d m : ℕ) (s : ℝ) : ℝ :=
  ∏ i ∈ range m, (1 - (d : ℝ) * s / (2 * (i + 1)))

/-- The zeros follow from actual factors, for every positive dimension. -/
theorem dimensionMellinFactor_root (d m k : ℕ) (hd : 0 < d) (hk : k < m) :
    dimensionMellinFactor d m (2 * (k + 1) / d) = 0 := by
  unfold dimensionMellinFactor
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hk)
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hk' : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The normalized transverse multiplier is independent of dimension.
The Gamma factor and change-of-variable prefactor are not. -/
theorem dimensionMellinFactor_transverse (d m : ℕ) (hd : 0 < d) (j : ℝ) :
    dimensionMellinFactor d m (2 * (j + 1) / d) =
      ∏ i ∈ range m, (1 - (j + 1) / (i + 1)) := by
  unfold dimensionMellinFactor
  apply Finset.prod_congr rfl
  intro i _
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hi : (i : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem dimensionPolynomial_four (z : ℝ) :
    (dimensionPolynomial 4).eval z = bdgPolynomial z := by
  norm_num [dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    Polynomial.derivative_mul, bdgPolynomial]
  ring

theorem dimensionKernel_four (z : ℝ) : dimensionKernel 4 z = bdgKernel z := by
  simp [dimensionKernel, bdgKernel, dimensionPolynomial_four]

/-- Independent identification with the unchanged, already integrated 4D kernel. -/
theorem dimensionKernel_four_moment (j : ℕ) :
    (∫ z : ℝ in Set.Ioi 0, z ^ j * dimensionKernel 4 (z ^ 2)) =
      -((j : ℝ) * ((j : ℝ) - 1) * ((j : ℝ) - 2)) / 12 *
        Real.Gamma (((j : ℝ) + 1) / 2) := by
  simp_rw [dimensionKernel_four]
  exact integral_bdgKernel_transverse_moment j

/-- Positive-density rescaling in squared proper time, valid in odd dimensions
as well. This is pointwise scaling, not an integral or limit theorem. -/
theorem dimensionKernel_density_scaling (d : ℕ) (hd : 0 < d)
    (c ρ σ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hσ : 0 ≤ σ) :
    dimensionKernel d (c * ρ * σ ^ ((d : ℝ) / 2)) =
      dimensionKernel d (((c * ρ) ^ (2 / (d : ℝ)) * σ) ^ ((d : ℝ) / 2)) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hbase : 0 ≤ c * ρ := le_of_lt (mul_pos hc hρ)
  rw [Real.mul_rpow (Real.rpow_nonneg hbase _) hσ, ← Real.rpow_mul hbase]
  have he : (2 / (d : ℝ)) * ((d : ℝ) / 2) = 1 := by field_simp
  rw [he, Real.rpow_one]

end BoundaryDraft
