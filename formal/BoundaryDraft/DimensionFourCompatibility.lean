import BoundaryDraft.DimensionSpacetime
import BoundaryDraft.ConeIntegral

/-!
# Four-dimensional physical reduced-kernel compatibility

The independent dimension-indexed spatial integral is identified with the
original four-dimensional radial slice. Finite vertical integration then gives
the unchanged derivative-defined `planeKernel`, with the actual point, pair and
interval coefficients. No desired kernel equality or limit is a premise.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- The angular factor is computed from Euclidean three-ball volume. -/
theorem dimensionRadialFactor_three : dimensionRadialFactor 3 = 4 * Real.pi := by
  have hv : (volume : Measure (DimensionSpatial 3)).real (Metric.ball 0 1) =
      Real.pi * 4 / 3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_ofReal,
      show 0 ≤ Real.pi * 4 / 3 by positivity]
  rw [dimensionRadialFactor, hv]
  norm_num
  ring

/-- Equality of the actual radial integrals, not just their polynomial factors.
It also holds for oriented negative-height integrals. -/
theorem dimensionRadialSlice_three (ρ H : ℝ) :
    dimensionRadialSlice 3 (Real.pi / 24) ρ H = coneRadialSlice ρ H := by
  rw [coneRadialSlice_eq_radial, dimensionRadialSlice, dimensionRadialFactor_three]
  norm_num [dimensionKernel_four]

/-- Spatial integration of the independent pair kernel recovers the original
four-dimensional cone slice, including the zero-height endpoint. -/
theorem dimensionSpatialSlice_three (ρ H : ℝ) (hH : 0 ≤ H) :
    dimensionSpatialSlice 3 (Real.pi / 24) ρ H = coneRadialSlice ρ H := by
  rw [dimensionSpatialSlice_eq_radial 3 (by norm_num) _ _ _ hH,
    dimensionRadialSlice_three]

/-- The complete spacetime cone integral has exactly the old radial-time value. -/
theorem dimensionConeIntegral_three (ρ H : ℝ) (hH : 0 ≤ H) :
    dimensionConeIntegral 3 (Real.pi / 24) ρ H = coneRadialIntegral ρ H := by
  rw [dimensionConeIntegral_eq_radial 3 (by norm_num) _ _ _ hH]
  simp only [dimensionRadialSlice_three, coneRadialIntegral]

/-- The original action-density primitive is exactly its finite triangular
convolution. All integrations are on finite intervals with continuous slices. -/
theorem coneRadialIntegral_vertical (ρ H : ℝ) (hH : 0 ≤ H) :
    (∫ s in (0 : ℝ)..H, coneRadialIntegral ρ s) =
      ∫ t in Ioc 0 H, (H - t) * coneRadialSlice ρ t := by
  calc
    _ = ∫ t in (0 : ℝ)..H, (H - t) * coneRadialSlice ρ t :=
      integral_dimensionConePrimitive (coneRadialSlice ρ) (continuous_coneRadialSlice ρ) H
    _ = _ := intervalIntegral.integral_of_le hH

/-- Exact finite-density recovery of the unchanged four-dimensional kernel.
In particular this holds at every positive density. The stronger all-real-density
statement uses the same total real square root/power conventions on both sides. -/
theorem dimensionVerticalKernel_three_eq_planeKernel (ρ H : ℝ) (hH : 0 ≤ H) :
    dimensionVerticalKernel 3 (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) ρ H =
      planeKernel ρ H := by
  have hp : ρ ^ (2 / ((3 + 1 : ℕ) : ℝ)) = Real.sqrt ρ := by
    norm_num [Real.sqrt_eq_rpow]
  rw [← integral_radial_actionDensity ρ H, dimensionVerticalKernel, hp, verticalActionReduction]
  simp only [dimensionRadialSlice_three]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 H)
      ((continuous_const.mul (continuous_coneRadialIntegral ρ)).intervalIntegrable 0 H),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    coneRadialIntegral_vertical ρ H hH]
  simp only [sub_zero, smul_eq_mul, mul_one]
  ring

/-- The independently normalized dimension-four kernel is exactly the existing
four-dimensional kernel, rather than a new normalization with matching moments. -/
theorem dimensionPlaneKernel_four (H : ℝ) (hH : 0 ≤ H) :
    dimensionPlaneKernel 4 H = planeKernel 1 H := by
  calc
    _ = dimensionVerticalKernel 3 (dimensionPointCoefficient 4) (dimensionPairCoefficient 4)
        (dimensionIntervalCoefficient 4) 1 H :=
      (congrFun (dimensionVerticalKernel_one_eq_planeKernel 3 (by norm_num)) H).symm
    _ = _ := by
      rw [dimensionPointCoefficient_four, dimensionPairCoefficient_four,
        dimensionIntervalCoefficient_four]
      exact dimensionVerticalKernel_three_eq_planeKernel 1 H hH

/-- The genuine new weighted bilocal action therefore reduces to the unchanged
four-dimensional `planeKernel`. The second endpoint still ranges over the whole
cap, including partners outside the support of the first-endpoint weight. -/
theorem dimensionWeighted_graphCap_four (h : DimensionSpatial 3 → ℝ)
    (hh : DimensionGraphCapData h) (w : DimensionSpatial 3 → ℝ) (hw : Continuous w) (ρ : ℝ) :
    dimensionWeightedAction 3 (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) ρ
      (dimensionGraphCap h) (fun p => w p.2) =
      ∫ x in {x | 0 < h x}, w x * planeKernel ρ (h x) := by
  rw [dimensionWeighted_graphCap_reduction 3 (by norm_num) h hh w hw]
  apply setIntegral_congr_fun hh.measurableSet_positive
  intro x hx
  dsimp only
  rw [dimensionVerticalKernel_three_eq_planeKernel ρ (h x) hx.le]

end BoundaryDraft
