import BoundaryDraft.EllipsoidHausdorff

/-!
Independent contracts for canonical/parametric measure compatibility. These
check measures, arbitrary observables, subtype transport and actual absolute
integrability, not just equality of one selected integral. The unequal-axis
example retains the original hypotheses, slopes, nonconstant weights and 48π.
-/

open BoundaryDraft MeasureTheory Set
open scoped ENNReal Topology
noncomputable section

-- Euclidean Hausdorff normalization, not coordinate supremum-norm area.
example : (ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure JointSpace)).restrict JointSphere =
    Measure.map (Subtype.val : JointSphere → JointSpace) (volume : Measure JointSpace).toSphere :=
  normalizedHausdorffTwo_restrict_sphere

-- The comparison holds with merely positive axes; no spacelike-height
-- assumption is needed to identify the two surface measures.
example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    (ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure JointSpace)).restrict (ellipsoidJoint b) =
      Measure.map (Subtype.val : ellipsoidJoint b → JointSpace) (ellipsoidSurfaceMeasure b hb) :=
  normalizedHausdorffTwo_restrict_ellipsoidJoint b hb

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo =
      ellipsoidSurfaceMeasure b hb := normalizedHausdorffTwo_comap_ellipsoidJoint b hb

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) : MeasurableSet (ellipsoidJoint b) :=
  measurableSet_ellipsoidJoint b hb

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (f : ellipsoidJoint b → ℝ≥0∞) :
    (∫⁻ x, f x ∂Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo) =
      ∫⁻ x, f x ∂ellipsoidSurfaceMeasure b hb := lintegral_ellipsoid_canonical b hb f

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (f : ellipsoidJoint b → ℝ) :
    Integrable f (Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo) ↔
      Integrable f (ellipsoidSurfaceMeasure b hb) := integrable_ellipsoid_subtype_canonical_iff b hb f

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (f : ellipsoidJoint b → ℝ) :
    (∫ x, f x ∂Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo) =
      ∫ x, f x ∂ellipsoidSurfaceMeasure b hb := integral_ellipsoid_subtype_canonical b hb f

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (f : JointSpace → ℝ) :
    IntegrableOn f (ellipsoidJoint b) normalizedHausdorffTwo ↔
      Integrable (fun x : ellipsoidJoint b => f x.val) (ellipsoidSurfaceMeasure b hb) :=
  integrableOn_ellipsoid_canonical_iff b hb f

example (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (f : JointSpace → ℝ) :
    (∫ x in ellipsoidJoint b, f x ∂normalizedHausdorffTwo) =
      ∫ x : ellipsoidJoint b, f x.val ∂ellipsoidSurfaceMeasure b hb :=
  integral_ellipsoid_canonical b hb f

-- The equator was proved null in both the sphere and its axis-scaled image.
example (b : Fin 3 → ℝ) : normalizedHausdorffTwo
    (ellipsoidAxisLinear b '' {x : JointSpace | x ∈ JointSphere ∧ x 0 = 0}) = 0 :=
  normalizedHausdorffTwo_linear_image_null (ellipsoidAxisLinear b).toContinuousLinearMap _
    normalizedHausdorffTwo_equator

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    graphSurfaceMeasure (ellipsoidProfile a b) =
      Measure.map (Subtype.val : ellipsoidJoint b → JointSpace)
        (ellipsoidSurfaceMeasure b (fun i => by linarith [hb i])) :=
  graphSurfaceMeasure_ellipsoid a b ha hb

private theorem axes : ∀ i : Fin 3, 2 * (1 / 4 : ℝ) < ![1, 2, 3] i := by
  intro i
  fin_cases i <;> norm_num

example : IntegrableOn (fun x => jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x))
    (ellipsoidJoint ![1, 2, 3]) normalizedHausdorffTwo :=
  integrableOn_ellipsoid_canonical_coth _ _ (by norm_num) axes

example : Integrable (fun x => 1 / ‖graphGradient (ellipsoidProfile (1 / 4) ![1, 2, 3]) x‖)
    (graphSurfaceMeasure (ellipsoidProfile (1 / 4) ![1, 2, 3])) :=
  (ellipsoid_admissible _ _ (by norm_num) axes).integrable_reciprocal_slope

example : (∫ x in ellipsoidJoint ![1, 2, 3], jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x)
    ∂normalizedHausdorffTwo) = 48 * Real.pi := by
  rw [integral_ellipsoid_canonical_coth _ _ (by norm_num) axes]
  norm_num [Fin.prod_univ_succ]
  ring

example : (∫ x, 1 / ‖graphGradient (ellipsoidProfile (1 / 4) ![1, 2, 3]) x‖
    ∂graphSurfaceMeasure (ellipsoidProfile (1 / 4) ![1, 2, 3])) = 48 * Real.pi := by
  change graphBoundaryIntegral (ellipsoidProfile (1 / 4) ![1, 2, 3]) = _
  rw [graphBoundaryIntegral_ellipsoid _ _ (by norm_num) axes]
  norm_num [Fin.prod_univ_succ]
  ring

example : GraphCapLimitGoal (ellipsoidProfile (1 / 4) ![1, 2, 3]) :=
  ellipsoid_canonical_limit _ _ (by norm_num) axes

example : ellipsoidSlope (1 / 4) ![1, 2, 3] (ellipsoidAxisPoint ![1, 2, 3] 0) = 1 / 2 ∧
    ellipsoidSlope (1 / 4) ![1, 2, 3] (ellipsoidAxisPoint ![1, 2, 3] 2) = 1 / 6 := by
  simp only [ellipsoidSlope_axis _ _ (by norm_num : (0 : ℝ) < 1 / 4)
    (fun i => by have := axes i; linarith)]
  change (2 * (1 / 4 : ℝ) / 1 = 1 / 2) ∧ (2 * (1 / 4 : ℝ) / 3 = 1 / 6)
  norm_num

example : jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] (ellipsoidAxisPoint ![1, 2, 3] 0)) = 2 ∧
    jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] (ellipsoidAxisPoint ![1, 2, 3] 2)) = 6 := by
  simp only [ellipsoid_coth_axis _ _ (by norm_num : (0 : ℝ) < 1 / 4) axes]
  change (1 / (2 * (1 / 4 : ℝ)) = 2) ∧ (3 / (2 * (1 / 4 : ℝ)) = 6)
  norm_num

example : ∃ x ∈ ellipsoidJoint ![1, 2, 3], ∃ y ∈ ellipsoidJoint ![1, 2, 3],
    jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x) ≠
      jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] y) :=
  ellipsoid_angle_nonconstant _ _ (by norm_num) axes 0 2 (by change (1 : ℝ) ≠ 3; norm_num)
