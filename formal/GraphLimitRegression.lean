import BoundaryDraft

/-!
Independent contracts for the completed deterministic graph-cap limit. Restate
the actual action, canonical reciprocal-gradient and angle targets without
relying only on the goal alias. Recover the original unequal-axis ellipsoid
limit through the general theorem, not through its prior concrete limit.
Quartic/critical-point regressions extend `GraphCapRegression.lean`.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) : GraphCapLimitGoal h :=
  hh.graphCapLimit

-- No reduction, atlas, coarea, continuity, normalization, or limit premise.
-- The surface measure is independently expanded to its canonical definition.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion h)) atTop
      (𝓝 (∫ x : JointSpace, 1 / ‖graphGradient h x‖
        ∂(ENNReal.ofReal (Real.pi / 4) •
          (μH[2] : Measure JointSpace).restrict (graphClosedPositive h ∩ {x | h x = 0})))) :=
  hh.graphCapLimit

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion h)) atTop
      (𝓝 (∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h)) :=
  hh.tendsto_continuumMean_graphCap_eq_angle

-- One constructed width supports coarea, the collar limit and the vanishing
-- tail together. Coarea/noncriticality are asserted only below that width.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ graphClosedCollar h δ, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) ∧
      (∀ ρ : ℝ, 0 < ρ → continuumMean ρ (graphCapRegion h) =
        (∫ t in (0 : ℝ)..δ, planeKernel ρ t * graphHeightDensity h t) +
          ∫ x in {x | δ ≤ h x}, planeKernel ρ (h x)) ∧
      Tendsto (fun ρ : ℝ => ∫ t in (0 : ℝ)..δ, planeKernel ρ t * graphHeightDensity h t)
        atTop (𝓝 (graphBoundaryIntegral h)) ∧
      Tendsto (fun ρ : ℝ => ∫ x in {x | δ ≤ h x}, planeKernel ρ (h x)) atTop (𝓝 0) := by
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  exact ⟨A.width, A.width_pos, A.noncritical,
    A.continuumMean_eq_height_collar_add_remainder hh,
    A.tendsto_integral_planeKernel_mul_graphHeightDensity hh,
    hh.toGraphCapData.tendsto_integral_kernel_superlevel A.width A.width_pos⟩

namespace GraphLimitRegression

-- The old concrete hypotheses suffice; neither the prior ellipsoid limit nor
-- a global noncriticality/height-density-continuity assumption is used.
theorem ellipsoid_from_general (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b))) atTop
      (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a)) := by
  simpa only [GraphCapLimitGoal, graphBoundaryIntegral_ellipsoid a b ha hb] using
    (ellipsoid_admissible a b ha hb).graphCapLimit

-- Reconstruct the unchanged concrete target from the new general theorem.
example : EllipsoidLimitGoal := ellipsoid_from_general

example : Tendsto (fun ρ => continuumMean ρ
    (graphCapRegion (ellipsoidProfile (1 / 4) ![1, 2, 3]))) atTop (𝓝 (48 * Real.pi)) := by
  convert ellipsoid_from_general (1 / 4) ![1, 2, 3] (by norm_num)
    (by intro i; fin_cases i <;> norm_num) using 1
  norm_num [Fin.prod_univ_succ]
  ring

end GraphLimitRegression
