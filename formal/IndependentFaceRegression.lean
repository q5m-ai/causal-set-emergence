import BoundaryDraft.IndependentFace
import BoundaryDraft.EllipsoidHausdorff

/-! Independent contracts for class E, including a genuinely steep instance,
null interval endpoints, empty regions with arbitrary exterior future data,
actual chart densities, the finite Poisson bridge, and the slope-less atlas.
No enlarged-class limit is asserted by these regressions. -/

open BoundaryDraft MeasureTheory Set
open scoped Topology ENNReal BigOperators
noncomputable section

example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) :
    AdmissibleIndependentTwoFace h f := hf.toIndependentTwoFace

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    IsOpen (twoFaceRegion h f) ∧ BoundedCausalRegion (twoFaceRegion h f) ∧
    IsCompact (twoFacePast h f) ∧ IsCompact (twoFaceFuture h f) ∧
    IsCompact (twoFaceJoint h f) ∧
    frontier (twoFaceRegion h f) = twoFacePast h f ∪ twoFaceFuture h f ∧
    twoFacePast h f ∩ twoFaceFuture h f = twoFaceJoint h f :=
  ⟨hf.isOpen_region, hf.boundedCausalRegion, hf.isCompact_past, hf.isCompact_future,
    hf.isCompact_joint, hf.frontier_region, AdmissibleIndependentTwoFace.past_inter_future⟩

-- Closed intervals, not only timelike interiors or straight segments.
example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (x y z : Spacetime) (hx : x ∈ twoFaceRegion h f) (hz : z ∈ twoFaceRegion h f)
    (hxy : y ∈ causalFuture x) (hyz : z ∈ causalFuture y) : y ∈ twoFaceRegion h f :=
  hf.causallyConvex_region x hx z hz ⟨hxy, hyz⟩

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (x y z : Spacetime) (hx : x ∈ twoFaceRegion h f) (hz : z ∈ twoFaceRegion h f)
    (ht : x 0 ≤ y 0) (hnull : spatialSeparationSq x y = (y 0 - x 0) ^ 2)
    (hyz : z ∈ causalFuture y) : y ∈ twoFaceRegion h f :=
  hf.causallyConvex_region x hx z hz ⟨⟨ht, hnull.le⟩, hyz⟩

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (ρ : ℝ) (hρ : 0 < ρ) :
    expectedBDGAction ρ (twoFaceRegion h f) = continuumMean ρ (twoFaceRegion h f) :=
  hf.expectedBDGAction_eq hρ

-- The existing normalized Hausdorff measure and induced metric are unchanged.
example (h f : Spatial → ℝ) :
    twoFaceProjectedArea h f =
      (ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure JointSpace).restrict (graphJoint h)).withDensity
        (fun x => ENNReal.ofReal (Real.sqrt (1 - ‖twoFaceTangentialGradient h f x‖ ^ 2))) := rfl

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    IsFiniteMeasure (twoFaceJointArea h f) ∧
    Integrable (twoFaceWeight h f) (twoFaceProjectedArea h f) :=
  ⟨hf.finite_jointArea, hf.integrable_weight⟩

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (x : JointSpace) (hx : x ∈ graphJoint h) (a b : ℝ)
    (he : a • twoFaceNormal (fun y => f y - h y) x + b • twoFaceNormal f x = 0) :
    a = 0 ∧ b = 0 := hf.normals_independent x hx a b he

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (c : SliceHeightChart h) (s : Set SurfacePlane) (hs : MeasurableSet s)
    (hsD : s ⊆ c.sliceDomain 0) :
    (twoFaceJointArea h f).restrict (c.jointChart f '' s) =
      Measure.map (c.jointChart f) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (jointGramDensity (c.jointFrame f u 0) (c.jointFrame f u 1)))) :=
  c.jointArea_chart_independent hf s hs hsD

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (c : SliceHeightChart h) (u : SurfacePlane) (hu : u ∈ c.sliceDomain 0) (i : Fin 2) :
    c.jointFrame f u i = fderiv ℝ (c.jointChart f) u (EuclideanSpace.basisFun (Fin 2) ℝ i) :=
  c.jointFrame_eq_fderiv_independent hf u hu i

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (x : JointSpace) (hx : x ∈ graphJoint h) :
    0 < jointAngle (twoFaceCosh h f x) ∧ 0 < twoFaceAreaDensity h f x :=
  ⟨(hf.angle_identities x hx).1, hf.areaDensity_pos x hx⟩

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f)
    (c d : SliceHeightChart h) (s t : Set SurfacePlane)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsD : s ⊆ c.sliceDomain 0) (htD : t ⊆ d.sliceDomain 0) :
    (Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))).restrict (d.jointChart f '' t) =
    (Measure.map (d.jointChart f) ((volume.restrict t).withDensity
      (fun u => ENNReal.ofReal (d.jointDensity f u)))).restrict (c.jointChart f '' s) :=
  c.jointArea_overlap_independent hf d s t hs ht hsD htD

-- The atlas and divergence prerequisites do not contain a causal slope premise.
example (h : Spatial → ℝ) (hh : RegularHeight h) : Nonempty (ControlledCollarAtlas h) :=
  hh.exists_controlledCollarAtlas

example (h : Spatial → ℝ) (hh : RegularHeight h) (A : ControlledCollarAtlas h)
    (w : JointSpace → ℝ) (hw : ContinuousOn w (graphClosedPositive h))
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 A.width)) :
    (∫ x in graphClosedCollar h A.width, g (h x) * w x) =
      ∫ t in Icc 0 A.width, g t * graphWeightedHeightDensity h w t :=
  A.integral_closedCollar_weighted hh w hw g hg

example (h : Spatial → ℝ) (hh : RegularHeight h) (x : JointSpace) (hx : x ∈ graphJoint h) :
    ∃ c : SliceHeightChart h, ∃ u ∈ c.sliceDomain 0, c.slice 0 u = x := hh.exists_jointChart x hx

example (h f : Spatial → ℝ) (hf : AdmissibleIndependentTwoFace h f) :
    (∫ x in {x : JointSpace | 0 < h x}, graphLaplacian f x) =
      -(∫ x, inner (𝕜 := ℝ) (graphGradient f x) (graphGradient h x) /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h) := hf.spatial_divergence

example : AdmissibleIndependentTwoFace steepCapsuleHeight steepCapsuleFuture := steepCapsule_admissible
example : ¬AdmissibleGraphCap steepCapsuleHeight := steepCapsule_not_old_cap
example : ¬AdmissibleTwoFace steepCapsuleHeight steepCapsuleFuture := steepCapsule_not_old_twoFace

example (x : JointSpace) : steepCapsuleHeight x = (3 / 4 : ℝ) * (1 - ‖x‖ ^ 2) :=
  steepCapsule_height x
example (x : Spatial) : steepCapsuleFuture x = steepCapsuleHeight x / 2 := steepCapsule_future x
example (x : JointSpace) (hx : ‖x‖ = 1) : graphSlope steepCapsuleHeight x = 3 / 2 :=
  steepCapsule_slope x hx

example : ∃ A : ControlledCollarAtlas steepCapsuleHeight, A.width < 3 / 4 ∧
    steepCapsuleHeight 0 = 3 / 4 ∧
    fderiv ℝ (fun x : JointSpace => steepCapsuleHeight x) 0 = 0 := by
  obtain ⟨A⟩ := steepCapsule_admissible.toRegularHeight.exists_controlledCollarAtlas
  refine ⟨A, ?_, steepCapsule_positive_critical⟩
  by_contra hn
  have hx : (0 : JointSpace) ∈ graphClosedPositive steepCapsuleHeight := by
    apply subset_closure
    change 0 < steepCapsuleHeight 0
    rw [steepCapsule_positive_critical.1]
    norm_num
  exact A.noncritical 0 ⟨hx, by
    change steepCapsuleHeight 0 ≤ A.width
    simpa only [steepCapsule_positive_critical.1] using le_of_not_gt hn⟩
    steepCapsule_positive_critical.2

-- Empty geometry is allowed; even global continuity of the raw future would
-- improperly strengthen this contract.
example (f : Spatial → ℝ) : AdmissibleIndependentTwoFace (fun _ => -1) f where
  bounded_positive := by norm_num
  smooth_near := fun _ _ => contDiffAt_const
  boundary_zero := by norm_num
  regular_zero := by norm_num
  smooth_future := by norm_num [graphClosedPositive]
  envelopes := ⟨fun _ => 0, fun _ => 0, ⟨0, le_rfl, zero_lt_one, by simp⟩,
    ⟨0, le_rfl, zero_lt_one, by simp⟩, by norm_num, by norm_num [graphClosedPositive]⟩

-- A genuinely nonplanar, variable-angle member of the enlarged symmetric family.
example : AdmissibleIndependentTwoFace (ellipsoidProfile (3 / 4) ![1, 2, 3])
      (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]) ∧
    ∃ x ∈ graphJoint (ellipsoidProfile (3 / 4) ![1, 2, 3]),
    ∃ y ∈ graphJoint (ellipsoidProfile (3 / 4) ![1, 2, 3]),
      jointAngle (twoFaceCosh (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]) x) ≠
      jointAngle (twoFaceCosh (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]) y) := by
  have hb : ∀ i : Fin 3, (3 / 4 : ℝ) < ![1, 2, 3] i := by
    intro i; fin_cases i <;> norm_num
  have hb0 : ∀ i : Fin 3, (0 : ℝ) < ![1, 2, 3] i := fun i => by linarith [hb i]
  have hf := symmetricEllipsoid_independent (3 / 4) ![1, 2, 3] (by norm_num) hb
  have hj (i : Fin 3) : ellipsoidAxisPoint ![1, 2, 3] i ∈
      graphJoint (ellipsoidProfile (3 / 4) ![1, 2, 3]) := by
    rw [graphJoint_ellipsoid_regular _ _ (by norm_num) hb0]
    exact ellipsoidAxisPoint_mem _ hb0 i
  have hc (i : Fin 3) :
      twoFaceCosh (ellipsoidProfile (3 / 4) ![1, 2, 3])
        (ellipsoidProfile ((3 / 4) / 2) ![1, 2, 3]) (ellipsoidAxisPoint ![1, 2, 3] i) =
      (1 + ((3 / 4 : ℝ) / ![1, 2, 3] i) ^ 2) /
        (1 - ((3 / 4 : ℝ) / ![1, 2, 3] i) ^ 2) := by
    rw [symmetricEllipsoid_cosh _ _ (by norm_num) hb _ (hj i).1, graphGradient_ellipsoid]
    change (1 + ellipsoidSlope _ _ _ ^ 2) / (1 - ellipsoidSlope _ _ _ ^ 2) = _
    rw [ellipsoidSlope_axis _ _ (by norm_num) hb0 i]
    norm_num
  refine ⟨hf, _, hj 0, _, hj 2, ?_⟩
  intro he
  have hcEq := congrArg Real.cosh he
  rw [(hf.angle_identities _ (hj 0)).2.1, (hf.angle_identities _ (hj 2)).2.1,
    hc 0, hc 2] at hcEq
  change (1 + ((3 / 4 : ℝ) / 1) ^ 2) / (1 - ((3 / 4 : ℝ) / 1) ^ 2) =
    (1 + ((3 / 4 : ℝ) / 3) ^ 2) / (1 - ((3 / 4 : ℝ) / 3) ^ 2) at hcEq
  norm_num at hcEq

private theorem axes : ∀ i : Fin 3, 2 * (1 / 4 : ℝ) < ![1, 2, 3] i := by
  intro i
  fin_cases i <;> norm_num

example : AdmissibleIndependentTwoFace (ellipsoidProfile (1 / 4) ![1, 2, 3]) (fun _ => 0) :=
  planarEllipsoid_independent _ _ (by norm_num) axes

-- Nonconstant angle weight on one unchanged unequal-axis joint, now in E.
example : ∃ x ∈ graphJoint (ellipsoidProfile (1 / 4) ![1, 2, 3]),
    ∃ y ∈ graphJoint (ellipsoidProfile (1 / 4) ![1, 2, 3]),
    twoFaceWeight (ellipsoidProfile (1 / 4) ![1, 2, 3]) (fun _ => 0) x ≠
      twoFaceWeight (ellipsoidProfile (1 / 4) ![1, 2, 3]) (fun _ => 0) y := by
  let hh := ellipsoid_admissible (1 / 4) ![1, 2, 3] (by norm_num) axes
  obtain ⟨x, hx, y, hy, hne⟩ := ellipsoid_angle_nonconstant (1 / 4) ![1, 2, 3]
    (by norm_num) axes 0 2 (by change (1 : ℝ) ≠ 3; norm_num)
  have hx' : x ∈ graphJoint (ellipsoidProfile (1 / 4) ![1, 2, 3]) := by
    rw [graphJoint_ellipsoid _ _ (by norm_num) axes]; exact hx
  have hy' : y ∈ graphJoint (ellipsoidProfile (1 / 4) ![1, 2, 3]) := by
    rw [graphJoint_ellipsoid _ _ (by norm_num) axes]; exact hy
  refine ⟨x, hx', y, hy', ?_⟩
  rw [hh.twoFaceWeight_planar x hx', hh.twoFaceWeight_planar y hy',
    graphGradient_ellipsoid, graphGradient_ellipsoid]
  simpa only [(jointRapidity_identities _
    (ellipsoidSlope_pos _ _ (by norm_num) (fun i => by have := axes i; linarith) x hx)
    (ellipsoidSlope_lt_one _ _ (by norm_num) axes x hx)).2.2.2.2,
    (jointRapidity_identities _
    (ellipsoidSlope_pos _ _ (by norm_num) (fun i => by have := axes i; linarith) y hy)
    (ellipsoidSlope_lt_one _ _ (by norm_num) axes y hy)).2.2.2.2] using hne

example : twoFaceBoundaryIntegral (ellipsoidProfile (1 / 4) ![1, 2, 3]) (fun _ => 0) =
    48 * Real.pi := by
  rw [(ellipsoid_admissible _ _ (by norm_num) axes).twoFaceBoundaryIntegral_planar,
    graphBoundaryIntegral_ellipsoid _ _ (by norm_num) axes]
  norm_num [Fin.prod_univ_succ]
  ring

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) :
    twoFaceProjectedArea h (fun _ => 0) = graphSurfaceMeasure h ∧
    twoFaceBoundaryIntegral h (fun _ => 0) = graphBoundaryIntegral h :=
  ⟨twoFaceProjectedArea_planar h, hh.twoFaceBoundaryIntegral_planar⟩
