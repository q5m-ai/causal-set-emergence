import BoundaryDraft

/-!
Canonical level-density contracts. They check finiteness, integrability,
endpoint nullity in a band, and the boundary value. Neither right continuity
nor coarea is asserted; the negative-height checks rule out silently replacing
the required one-sided continuity by two-sided continuity.
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

-- Canonical levels are empty below zero, even when the raw profile has
-- negative-height level sets outside the closed positive region.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (s : ℝ) (hs : s < 0) :
    graphLevelMeasure h s = 0 ∧ graphHeightDensity h s = 0 :=
  ⟨hh.graphLevelMeasure_eq_zero_of_neg s hs, hh.graphHeightDensity_eq_zero_of_neg s hs⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h)
    (hc : ContinuousAt (graphHeightDensity h) 0) : graphBoundaryIntegral h = 0 :=
  hh.graphBoundaryIntegral_eq_zero_of_continuousAt_heightDensity hc

-- The nullity conclusion is in the same product Lebesgue measure as the
-- original action reduction. There is no global noncriticality premise.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioc (0 : ℝ) δ, volume {x : Spatial | h x = s} = 0 :=
  hh.exists_null_level_band

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x : JointSpace, x ∈ closure {y : JointSpace | 0 < h y} → h x = s →
      fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) (f : Spatial → ℝ) :
    (∫ x in {x | 0 < h x ∧ h x < s}, f x) = ∫ x in {x | 0 < h x ∧ h x ≤ s}, f x :=
  hh.integral_collar_eq_closed_endpoint s hs (fun x hx => hreg x hx.1 hx.2) f

-- Exterior zeros of an empty cap carry no height-zero surface mass.
example : graphLevelMeasure (fun _ : Spatial => (0 : ℝ)) 0 = 0 := by
  simp [graphSurfaceMeasure, graphJoint, graphClosedPositive]

-- A raw zero level can have infinite spatial volume. The null-level theorem
-- deliberately requires positive height and does not discard these zeros.
example : volume {x : Spatial | (fun _ : Spatial => (0 : ℝ)) x = 0} = ⊤ := by simp

-- The original unequal-axis ellipsoid meets these level-measure contracts
-- without changing its concrete parametric measure or original hypotheses.
example : ∃ δ : ℝ, 0 < δ ∧ ∀ s ≤ δ,
    IsFiniteMeasure (graphLevelMeasure (ellipsoidProfile (1 / 4) ![1, 2, 3]) s) ∧
      Integrable (fun x => 1 / ‖graphGradient (ellipsoidProfile (1 / 4) ![1, 2, 3]) x‖)
        (graphLevelMeasure (ellipsoidProfile (1 / 4) ![1, 2, 3]) s) :=
  (ellipsoid_admissible _ _ (by norm_num) (by intro i; fin_cases i <;> norm_num)).exists_integrable_level_band

example : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioc (0 : ℝ) δ,
    volume {x : Spatial | ellipsoidProfile (1 / 4) ![1, 2, 3] x = s} = 0 :=
  (ellipsoid_admissible _ _ (by norm_num) (by intro i; fin_cases i <;> norm_num)).exists_null_level_band
