import BoundaryDraft

/-!
Independent contracts for the general pointwise angle, finite canonical
surface target, local level charts, and non-collar remainder. These are not
regressions for a proved general deterministic limit: that theorem is open.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology MeasureTheory ENNReal
noncomputable section

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (x : JointSpace)
    (hx : x ∈ graphJoint h) :
    0 < ‖gradient (fun y : JointSpace => h y) x‖ ∧
      ‖gradient (fun y : JointSpace => h y) x‖ < 1 :=
  ⟨hh.graphSlope_pos x hx, hh.graphSlope_lt_one x hx.1⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (x : JointSpace)
    (hx : x ∈ graphJoint h) :
    0 < jointRapidity (graphSlope h x) ∧
    Real.cosh (jointRapidity (graphSlope h x)) /
      Real.sinh (jointRapidity (graphSlope h x)) = 1 / ‖graphGradient h x‖ :=
  ⟨(hh.graph_angle_identities x hx).1, (hh.graph_angle_identities x hx).2.2.2.2⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (x : JointSpace)
    (hx : x ∈ graphJoint h) :
    ‖graphInward h x‖ = 1 ∧ ‖graphOutward h x‖ = 1 ∧
    fderiv ℝ (fun y : JointSpace => h y) x (graphInward h x) = ‖graphGradient h x‖ :=
  ⟨hh.graphInward_norm x hx, hh.graphOutward_norm x hx, hh.graph_differential_inward x hx⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (x : JointSpace)
    (hx : x ∈ graphJoint h) :
    Module.finrank ℝ (LinearMap.ker (fderiv ℝ (fun y : JointSpace => h y) x)) = 2 :=
  hh.graphTangentSpace_finrank x hx

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (x : JointSpace)
    (hx : x ∈ graphJoint h) :
    ∃ e : PartialHomeomorph JointSpace (ℝ × graphTangentSpace h x),
      x ∈ e.source ∧ e x = (h x, 0) ∧ (∀ y, (e y).1 = h y) ∧
      HasStrictFDerivAt (fun z => e.symm (h x, z)) (graphTangentSpace h x).subtypeL 0 :=
  hh.exists_level_chart x hx.1 (hh.regular_zero x hx.1 hx.2)

-- The volume-to-surface factor is derived from differential constraints,
-- rather than introduced as a weight chosen to make coarea hold.
example (h : Spatial → ℝ) (x z v w : JointSpace)
    (hz : fderiv ℝ (fun y : JointSpace => h y) x z = 1)
    (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0)
    (hw : fderiv ℝ (fun y : JointSpace => h y) x w = 0) :
    |Matrix.det ![(z : Spatial), (v : Spatial), (w : Spatial)]| =
      Real.sqrt (‖v‖ ^ 2 * ‖w‖ ^ 2 - inner (𝕜 := ℝ) v w ^ 2) /
        ‖graphGradient h x‖ := by
  rw [← graphAreaJacobian_eq_sqrt_gram]
  exact graph_coarea_frame_jacobian h x z v w hz hv hw

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    (μH[2] : Measure JointSpace) (graphJoint h) < ∞ := hh.hausdorff_joint_lt_top

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    IsFiniteMeasure (graphSurfaceMeasure h) ∧
      Integrable (fun x => 1 / ‖gradient (fun y : JointSpace => h y) x‖)
        (graphSurfaceMeasure h) ∧
      Integrable (fun x => jointCoth (graphSlope h x)) (graphSurfaceMeasure h) :=
  ⟨hh.finite_graphSurfaceMeasure, hh.integrable_reciprocal_slope, hh.integrable_jointCoth⟩

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    (∫ x, 1 / ‖graphGradient h x‖ ∂graphSurfaceMeasure h) =
      ∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h :=
  hh.graphBoundaryIntegral_eq_angle

-- Arbitrary exterior zeros cannot supply spurious surface mass.
example : graphSurfaceMeasure (fun _ : Spatial => (0 : ℝ)) = 0 := by
  simp [graphSurfaceMeasure, graphJoint, graphClosedPositive]

-- Smoothness/regularity are unnecessary for the non-collar limit.
example (h : Spatial → ℝ) (hh : GraphCapData h) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ρ => ∫ x in {x | δ ≤ h x}, planeKernel ρ (h x)) atTop (𝓝 0) :=
  hh.tendsto_integral_kernel_superlevel δ hδ

example (h : Spatial → ℝ) (hh : GraphCapData h) (ρ δ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    continuumMean ρ (graphCapRegion h) =
      (∫ x in {x | 0 < h x ∧ h x < δ}, planeKernel ρ (h x)) +
      ∫ x in {x | δ ≤ h x}, planeKernel ρ (h x) :=
  hh.continuumMean_eq_collar_add_remainder ρ δ hρ hδ

-- The new gradient agrees with the original unequal-axis example.
example : graphSlope (ellipsoidProfile (1 / 4) ![1, 2, 3])
    (ellipsoidAxisPoint ![1, 2, 3] 0) = 1 / 2 := by
  change ‖graphGradient _ _‖ = _
  rw [graphGradient_ellipsoid]
  change ellipsoidSlope _ _ _ = _
  rw [ellipsoidSlope_axis _ _ (by norm_num) (by intro i; fin_cases i <;> norm_num)]
  norm_num

-- Recovery with the EXISTING parametric measure, not an assertion that the
-- canonical Hausdorff and parametric measures have already been identified.
example : (∫ x : ellipsoidJoint ![1, 2, 3],
    jointCoth (graphSlope (ellipsoidProfile (1 / 4) ![1, 2, 3]) x.val)
      ∂ellipsoidSurfaceMeasure ![1, 2, 3] (by intro i; fin_cases i <;> norm_num)) =
        48 * Real.pi := by
  simp only [graphSlope, graphGradient_ellipsoid]
  have he := integral_ellipsoid_coth (1 / 4) ![1, 2, 3]
    (by norm_num) (by intro i; fin_cases i <;> norm_num)
  norm_num [Fin.prod_univ_succ] at he
  convert he using 1
  ring
