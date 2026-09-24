import BoundaryDraft

/-!
Canonical level-density contracts. They check finiteness and integrability in
a band and the boundary value, not the still-missing continuity or coarea.
-/

open BoundaryDraft MeasureTheory Set
open scoped Topology ENNReal
noncomputable section

-- All levels are explicitly normalized in the Euclidean ambient space.
example (h : Spatial → ℝ) (s : ℝ) : graphLevelMeasure h s =
    ENNReal.ofReal (Real.pi / 4) •
      (μH[2] : Measure JointSpace).restrict (graphClosedPositive h ∩ {x | h x = s}) := by
  simp only [graphLevelMeasure, graphLevel, normalizedHausdorffTwo, Measure.restrict_smul]

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (s : ℝ) :
    IsCompact (graphLevel h s) ∧ MeasurableSet (graphLevel h s) :=
  ⟨hh.isCompact_level s, hh.measurableSet_level s⟩

-- No nonvanishing assumption on all positive levels has been introduced.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ≤ δ, IsFiniteMeasure (graphLevelMeasure h s) ∧
      Integrable (fun x => 1 / ‖gradient (fun y : JointSpace => h y) x‖) (graphLevelMeasure h s) :=
  hh.exists_integrable_level_band

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    graphHeightDensity h 0 = graphBoundaryIntegral h ∧
      graphHeightDensity h 0 = ∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h :=
  ⟨graphHeightDensity_zero h, hh.graphHeightDensity_zero_eq_angle⟩

-- A cover of the joint extends to a whole sufficiently thin collar.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (U : Set JointSpace)
    (hU : IsOpen U) (hJU : graphJoint h ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ graphClosedPositive h, h x ≤ δ → x ∈ U :=
  hh.exists_band_subset_joint_neighborhood U hU hJU

-- Exterior zeros of an empty cap carry no height-zero surface mass.
example : graphLevelMeasure (fun _ : Spatial => (0 : ℝ)) 0 = 0 := by
  simp [graphSurfaceMeasure, graphJoint, graphClosedPositive]

-- The original unequal-axis ellipsoid meets these level-measure contracts
-- without changing its concrete parametric measure or original hypotheses.
example : ∃ δ : ℝ, 0 < δ ∧ ∀ s ≤ δ,
    IsFiniteMeasure (graphLevelMeasure (ellipsoidProfile (1 / 4) ![1, 2, 3]) s) ∧
      Integrable (fun x => 1 / ‖graphGradient (ellipsoidProfile (1 / 4) ![1, 2, 3]) x‖)
        (graphLevelMeasure (ellipsoidProfile (1 / 4) ![1, 2, 3]) s) :=
  (ellipsoid_admissible _ _ (by norm_num) (by intro i; fin_cases i <;> norm_num)).exists_integrable_level_band
