import BoundaryDraft.DimensionFourCompatibility

/-! Calibrate actual finite reductions and weighted bilocal actions against the
unchanged four-dimensional kernel, not just its polynomial coefficients. -/

open MeasureTheory Set BoundaryDraft

example (H : ℝ) (hH : 0 ≤ H) : dimensionPlaneKernel 4 H = planeKernel 1 H :=
  dimensionPlaneKernel_four H hH

-- Independently expanded finite vertical formula at arbitrary positive density.
example (ρ H : ℝ) (_hρ : 0 < ρ) (hH : 0 ≤ H) :
    ρ ^ (1 / 2 : ℝ) * ((4 / Real.sqrt 6) * H - (4 / Real.sqrt 6) * ρ *
      ∫ t in Ioc 0 H, (H - t) * dimensionRadialSlice 3 (Real.pi / 24) ρ t) =
      planeKernel ρ H := by
  simpa only [dimensionVerticalKernel, verticalActionReduction,
    show (2 : ℝ) / ((3 + 1 : ℕ) : ℝ) = 1 / 2 by norm_num] using
      dimensionVerticalKernel_three_eq_planeKernel ρ H hH

example : dimensionPlaneKernel 4 0 = planeKernel 1 0 :=
  dimensionPlaneKernel_four 0 (by norm_num)

example : dimensionVerticalKernel 3 (4 / Real.sqrt 6) (4 / Real.sqrt 6)
    (Real.pi / 24) 7 2 = planeKernel 7 2 :=
  dimensionVerticalKernel_three_eq_planeKernel 7 2 (by norm_num)

-- The action calibration is genuinely bilocal and keeps all future partners.
example (h : DimensionSpatial 3 → ℝ) (hh : DimensionGraphCapData h)
    (w : DimensionSpatial 3 → ℝ) (hw : Continuous w) (ρ : ℝ) :
    ρ ^ (1 / 2 : ℝ) *
      ((4 / Real.sqrt 6) * (∫ x in dimensionGraphCap h, w x.2) -
        (4 / Real.sqrt 6) * ρ * ∫ x in dimensionGraphCap h, w x.2 *
          ∫ y in dimensionGraphCap h ∩ dimensionCausalFuture x,
            dimensionBilocalKernel 3 (Real.pi / 24) ρ x y) =
      ∫ x in {x | 0 < h x}, w x * planeKernel ρ (h x) := by
  simpa only [dimensionWeightedAction,
    show (2 : ℝ) / ((3 + 1 : ℕ) : ℝ) = 1 / 2 by norm_num] using
      dimensionWeighted_graphCap_four h hh w hw ρ
