import BoundaryDraft.DimensionMellin

/-! Independent integral contracts: actual signed kernels, absolute convergence,
density powers, divergent endpoints, and even/odd critical orders. -/

open BoundaryDraft MeasureTheory Set

example (d : ℕ) (a : ℝ) (ha : 0 < a) :
    (∫ z : ℝ in Ioi 0, z ^ (a - 1) *
      ((dimensionPolynomialStage d (d / 2 + 1)).eval z * Real.exp (-z))) =
      Real.Gamma a * ∏ i ∈ Finset.range (d / 2 + 1),
        (1 - (d : ℝ) * a / (2 * (i + 1))) :=
  integral_dimensionKernel_mellin d ha

example (d : ℕ) (hd : 2 ≤ d) (j c ρ : ℝ) (hj : -1 < j)
    (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun u : ℝ => u ^ j * |dimensionKernel d (c * ρ * u ^ ((d : ℝ) / 2))|)
      (Ioi 0) := by
  have hi := integrableOn_dimensionKernel_density_rpow d
    (q := (d : ℝ) / 2) (j := j) (c := c * ρ)
    (div_pos (by exact_mod_cast (show 0 < d by omega)) (by norm_num)) hj (mul_pos hc hρ)
  apply hi.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu _)]

example (d : ℕ) (hd : 2 ≤ d) (j c ρ : ℝ) (hj : -1 < j)
    (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ u : ℝ in Ioi 0, u ^ j * dimensionKernel d (c * ρ * u ^ ((d : ℝ) / 2))) =
      (c * ρ) ^ (-(j + 1) / ((d : ℝ) / 2)) *
        ((1 / ((d : ℝ) / 2)) * Real.Gamma ((j + 1) / ((d : ℝ) / 2)) *
          ∏ i ∈ Finset.range (d / 2 + 1),
            (1 - (d : ℝ) * ((j + 1) / ((d : ℝ) / 2)) / (2 * (i + 1)))) :=
  integral_dimensionKernel_density_rpow d
    (div_pos (by exact_mod_cast (show 0 < d by omega)) (by norm_num)) hj (mul_pos hc hρ)

example (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (j : ℝ) (hj : j ≤ -1) :
    ¬ IntegrableOn (fun u : ℝ => u ^ j * dimensionKernel d (c * u ^ ((d : ℝ) / 2)))
      (Ioi 0) :=
  not_integrableOn_dimensionKernel_rpow d
    (div_pos (by exact_mod_cast (show 0 < d by omega)) (by norm_num)) hj

example : (∫ u : ℝ in Ioi 0, u ^ (2 : ℝ) * dimensionKernel 2 (u ^ (1 : ℝ))) = 2 := by
  have h := integral_dimensionKernel_transverse 2 (by norm_num) (j := 2) (by norm_num)
  norm_num [dimensionFactorCount, Finset.prod_range_succ] at h
  simpa using h

example : (∫ u : ℝ in Ioi 0, u ^ (2 : ℝ) * dimensionKernel 3 (u ^ (3 / 2 : ℝ))) = 2 / 3 := by
  have h := integral_dimensionKernel_transverse 3 (by norm_num) (j := 2) (by norm_num)
  norm_num [dimensionFactorCount, Finset.prod_range_succ] at h
  simpa using h

example : (∫ u : ℝ in Ioi 0, u ^ (3 / 2 : ℝ) * dimensionKernel 3 (u ^ (3 / 2 : ℝ))) =
    Real.Gamma (5 / 3) / 4 := by
  have h := integral_dimensionKernel_transverse 3 (by norm_num) (j := 3 / 2) (by norm_num)
  norm_num [dimensionFactorCount, Finset.prod_range_succ] at h
  rw [h]
  ring

example : (∫ u : ℝ in Ioi 0, u ^ (5 / 2 : ℝ) * dimensionKernel 5 (u ^ (5 / 2 : ℝ))) =
    -Real.Gamma (7 / 5) / 8 := by
  have h := integral_dimensionKernel_transverse 5 (by norm_num) (j := 5 / 2) (by norm_num)
  norm_num [dimensionFactorCount, Finset.prod_range_succ] at h
  rw [h]
  ring

-- Critical half-orders survive in every odd dimension, not only in examples.
example (d : ℕ) (hd : 2 ≤ d) (hodd : d % 2 = 1) :
    (∫ u : ℝ in Ioi 0,
      u ^ ((d : ℝ) / 2) * dimensionKernel d (u ^ ((d : ℝ) / 2))) ≠ 0 :=
  integral_dimensionKernel_odd_critical_ne_zero d (by omega) hodd

-- Recover the old integrated 4D theorem from the newly proved all-dimensional result.
example : (∫ u : ℝ in Ioi 0, u ^ (3 : ℝ) * bdgKernel (u ^ 2)) = -(1 / 2) := by
  have h := integral_dimensionKernel_transverse 4 (by norm_num) (j := 3) (by norm_num)
  norm_num [dimensionFactorCount, Finset.prod_range_succ, dimensionKernel_four] at h
  exact h
