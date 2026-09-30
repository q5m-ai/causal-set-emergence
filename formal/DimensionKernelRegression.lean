import BoundaryDraft.DimensionKernel

/-! Independent low-dimensional polynomial and normalization regressions.
These do not encode general-dimensional integral or localization hypotheses. -/

open BoundaryDraft MeasureTheory Set

example (z : ℝ) :
    (dimensionPolynomial 2).eval z = 1 - 2 * z + z ^ 2 / 2 := by
  norm_num [dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    Polynomial.derivative_mul]
  ring

example (z : ℝ) :
    (dimensionPolynomial 3).eval z = 1 - (27 / 8) * z + (9 / 8) * z ^ 2 := by
  norm_num [dimensionPolynomial, dimensionFactorCount, dimensionPolynomialStage,
    Polynomial.derivative_mul]
  ring

example (z : ℝ) :
    dimensionKernel 4 z = (1 - 9 * z + 8 * z ^ 2 - (4 / 3) * z ^ 3) *
      Real.exp (-z) := by
  rw [dimensionKernel_four]
  rfl

example (j : ℝ) :
    dimensionMellinFactor 4 (dimensionFactorCount 4) ((j + 1) / 2) =
      -(j * (j - 1) * (j - 2)) / 6 := by
  norm_num [dimensionMellinFactor, dimensionFactorCount, Finset.prod_range_succ]
  ring

-- Every dimension has its own scale, but these transverse roots are universal.
example (d k : ℕ) (hd : 2 ≤ d) (hk : k < dimensionFactorCount d) :
    dimensionMellinFactor d (dimensionFactorCount d) (2 * (k + 1) / d) = 0 :=
  dimensionMellinFactor_root d _ k (by omega) hk

-- The odd-dimensional critical fractional exponent is not a root.
example : dimensionMellinFactor 3 (dimensionFactorCount 3) (5 / 3) = 3 / 8 := by
  norm_num [dimensionMellinFactor, dimensionFactorCount, Finset.prod_range_succ]

example : (∫ z : ℝ in Ioi 0, z ^ 3 * dimensionKernel 4 (z ^ 2)) = -(1 / 2) := by
  rw [dimensionKernel_four_moment]
  norm_num

example (c ρ σ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (hσ : 0 ≤ σ) :
    dimensionKernel 5 (c * ρ * σ ^ (5 / 2 : ℝ)) =
      dimensionKernel 5 (((c * ρ) ^ (2 / 5 : ℝ) * σ) ^ (5 / 2 : ℝ)) := by
  exact dimensionKernel_density_scaling 5 (by norm_num) c ρ σ hc hρ hσ
