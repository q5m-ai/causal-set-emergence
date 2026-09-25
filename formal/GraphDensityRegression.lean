import BoundaryDraft

/-!
Canonical level-density contracts: finite/integrable levels, measurability,
a uniform collar bound, and the right-hand boundary limit. Negative-height
vanishing and a nonzero ellipsoid boundary value distinguish the proved
one-sided continuity from false two-sided continuity. Coarea has separate
regressions in `GraphCoareaRegression.lean`.
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

-- These are contracts for the existing density, with no assumed atlas,
-- continuity, measurability, bound, or equivalent regularity premise.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ∃ δ : ℝ, 0 < δ ∧ ContinuousOn (graphHeightDensity h) (Icc 0 δ) ∧
      Measurable (fun t : Icc (0 : ℝ) δ => graphHeightDensity h t) ∧
      AEStronglyMeasurable (graphHeightDensity h) (volume.restrict (Icc 0 δ)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 δ, ‖graphHeightDensity h t‖ ≤ C :=
  hh.exists_regular_heightDensity_band

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ContinuousWithinAt (graphHeightDensity h) (Ici 0) 0 :=
  hh.continuousWithinAt_graphHeightDensity_zero

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Filter.Tendsto (graphHeightDensity h) (𝓝[≥] 0) (𝓝 (graphBoundaryIntegral h)) :=
  hh.tendsto_graphHeightDensity_zero

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    Filter.Tendsto (graphHeightDensity h) (𝓝[≥] 0)
      (𝓝 (∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h)) := by
  rw [← hh.graphBoundaryIntegral_eq_angle]
  exact hh.tendsto_graphHeightDensity_zero

-- A half-line signed-kernel consumer may cut off above this collar without
-- needing any global density regularity. At zero it keeps the right limit.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (A : ControlledCollarAtlas h) :
    Measurable ((Icc 0 A.width).indicator (graphHeightDensity h)) ∧
      ContinuousWithinAt ((Icc 0 A.width).indicator (graphHeightDensity h)) (Ici 0) 0 := by
  refine ⟨A.measurable_indicator_graphHeightDensity hh, ?_⟩
  apply hh.continuousWithinAt_graphHeightDensity_zero.congr_of_eventuallyEq
  · filter_upwards [Icc_mem_nhdsGE A.width_pos] with t ht
    exact indicator_of_mem ht _
  · exact indicator_of_mem (show (0 : ℝ) ∈ Icc 0 A.width from ⟨le_rfl, A.width_pos.le⟩) _

-- Reused from draft #29: canonical negative levels carry no surface mass,
-- regardless of negative ambient levels outside the closed positive region.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (s : ℝ) (hs : s < 0) :
    graphLevelMeasure h s = 0 ∧ graphHeightDensity h s = 0 :=
  ⟨hh.graphLevelMeasure_eq_zero_of_neg s hs, hh.graphHeightDensity_eq_zero_of_neg s hs⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h)
    (hc : ContinuousAt (graphHeightDensity h) 0) : graphBoundaryIntegral h = 0 :=
  hh.graphBoundaryIntegral_eq_zero_of_continuousAt_heightDensity hc

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

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    ContinuousWithinAt (graphHeightDensity (ellipsoidProfile a b)) (Ici 0) 0 :=
  (ellipsoid_admissible a b ha hb).continuousWithinAt_graphHeightDensity_zero

private theorem unequal_boundary_value :
    graphBoundaryIntegral (ellipsoidProfile (1 / 4) ![1, 2, 3]) = 48 * Real.pi := by
  rw [graphBoundaryIntegral_ellipsoid _ _ (by norm_num)
    (by intro i; fin_cases i <;> norm_num)]
  norm_num [Fin.prod_univ_succ]
  ring

-- A genuinely nonzero boundary limit: two-sided continuity would be false.
example : Filter.Tendsto (graphHeightDensity (ellipsoidProfile (1 / 4) ![1, 2, 3]))
    (𝓝[≥] 0) (𝓝 (48 * Real.pi)) := by
  have hh := ellipsoid_admissible (1 / 4) ![1, 2, 3] (by norm_num)
    (by intro i; fin_cases i <;> norm_num)
  simpa only [unequal_boundary_value] using hh.tendsto_graphHeightDensity_zero

example : ¬ ContinuousAt (graphHeightDensity (ellipsoidProfile (1 / 4) ![1, 2, 3])) 0 := by
  intro hc
  have hh := ellipsoid_admissible (1 / 4) ![1, 2, 3] (by norm_num)
    (by intro i; fin_cases i <;> norm_num)
  have hz := hh.graphBoundaryIntegral_eq_zero_of_continuousAt_heightDensity hc
  rw [unequal_boundary_value] at hz
  exact (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 48) Real.pi_pos)) hz
