import BoundaryDraft.JointTransport
import BoundaryDraft.EllipsoidHausdorff
import BoundaryDraft.TwoFaceExamples

/-!
Independent contracts for area/angle geometry, not for a new action limit.
The unequal-axis target is unchanged. A translated boost puts its joint at
nonconstant times; its actual tangent metric distinguishes Lorentzian area
from ambient four-dimensional Euclidean area.
-/

open BoundaryDraft MeasureTheory Set
open scoped Topology ENNReal BigOperators
noncomputable section
namespace JointSurfaceRegression

example : TwoFaceAreaGoal := twoFaceAreaGoal
example : TwoFacePlanarTargetGoal := twoFacePlanarTargetGoal

-- Restate the geometric conclusions without assuming an integral value.
example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ graphJoint h,
      1 + ε ≤ minkowskiInner (twoFaceNormal (fun y => f y - h y) x) (twoFaceNormal f x) ∧
        ε ≤ Real.sqrt (1 - ‖twoFaceTangentialGradient h f x‖ ^ 2)) ∧
    IsFiniteMeasure (twoFaceJointArea h f) ∧
    Integrable (twoFaceSpacetimeWeight h f) (twoFaceJointArea h f) :=
  ⟨hf.exists_joint_margins, hf.finite_jointArea, hf.integrable_spacetimeWeight⟩

example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f)
    (x : JointSpace) (hx : x ∈ graphJoint h) :
    0 < jointAngle (twoFaceCosh h f x) ∧
    Real.cosh (jointAngle (twoFaceCosh h f x)) / Real.sinh (jointAngle (twoFaceCosh h f x)) =
      minkowskiInner (twoFaceNormal (fun y => f y - h y) x) (twoFaceNormal f x) /
        Real.sqrt (minkowskiInner (twoFaceNormal (fun y => f y - h y) x)
          (twoFaceNormal f x) ^ 2 - 1) :=
  ⟨(hf.angle_identities x hx).1, (hf.angle_identities x hx).2.2.2⟩

example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f)
    (x : JointSpace) (hx : x ∈ graphJoint h) (v : JointSpace)
    (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0) (hne : v ≠ 0) :
    0 < -minkowskiInner (jointVector (fderiv ℝ (fun y : JointSpace => f y) x v) v)
      (jointVector (fderiv ℝ (fun y : JointSpace => f y) x v) v) ∧
    minkowskiInner (twoFaceNormal f x) (jointGraphTangent (graphGradient f x) v) = 0 ∧
    minkowskiInner (twoFaceNormal (fun y => f y - h y) x)
      (jointGraphTangent (graphGradient f x) v) = 0 := by
  simpa only [graph_differential_eq_inner, jointGraphTangent] using hf.joint_tangent_geometry x hx v hv hne

-- A chart density is the Gram determinant of the ACTUAL derivative. The
-- equality is a measure law on arbitrary measurable subsets of its domain.
example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) (c : SliceHeightChart h)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain 0) :
    (twoFaceJointArea h f).restrict (c.jointChart f '' s) =
      Measure.map (c.jointChart f) ((volume.restrict s).withDensity (fun u =>
        ENNReal.ofReal (jointGramDensity
          (fderiv ℝ (c.jointChart f) u (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ (c.jointChart f) u (EuclideanSpace.basisFun (Fin 2) ℝ 1))))) := by
  rw [c.jointArea_chart hf s hs hsD]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [SliceHeightChart.jointDensity, c.jointFrame_eq_fderiv hf u (hsD hu),
    c.jointFrame_eq_fderiv hf u (hsD hu)]

-- Orientation reversal on an overlap changes the signed determinant but
-- cannot change area. A non-unit shear/rescaling catches missing Jacobians.
example (v w : Spacetime) : jointGramDensity w v = jointGramDensity v w := by
  simp [jointGramDensity, minkowskiInner_symm w v, mul_comm]

example (v w : Spacetime) :
    jointGramDensity ((2 : ℝ) • v + w) (-w) = 2 * jointGramDensity v w := by
  convert jointGramDensity_change_frame v w 2 1 0 (-1) using 1 <;> simp

example (h f : Spatial → ℝ) (hf : AdmissibleTwoFace h f) (c d : SliceHeightChart h)
    (s t : Set SurfacePlane) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsD : s ⊆ c.sliceDomain 0) (htD : t ⊆ d.sliceDomain 0) :
    (Measure.map (c.jointChart f) ((volume.restrict s).withDensity
      (fun u => ENNReal.ofReal (c.jointDensity f u)))).restrict (d.jointChart f '' t) =
    (Measure.map (d.jointChart f) ((volume.restrict t).withDensity
      (fun u => ENNReal.ofReal (d.jointDensity f u)))).restrict (c.jointChart f '' s) :=
  c.jointArea_overlap hf d s t hs ht hsD htD

-- The old measure, all observables, and the old integral, not just a sphere.
example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (φ : JointSpace → ℝ) :
    twoFaceProjectedArea h (fun _ => 0) = graphSurfaceMeasure h ∧
    (∫ x, φ x ∂twoFaceProjectedArea h (fun _ => 0)) = ∫ x, φ x ∂graphSurfaceMeasure h ∧
    twoFaceBoundaryIntegral h (fun _ => 0) = graphBoundaryIntegral h := by
  simp only [twoFaceProjectedArea_planar, hh.twoFaceBoundaryIntegral_planar, and_self]

/-- A translated, time-oriented boost with spatial parity. Its linear map is
an involution, so the inverse is checked independently without assuming it. -/
def boost : PoincareEquiv where
  linear := LinearEquiv.ofInvolutive (lorentzReflection ![1, 3, 0, 0])
    (fun y => lorentzReflection_involutive _ y (by norm_num [minkowskiInner, Fin.sum_univ_succ]))
  translation := ![2, -1, 3, 0]
  preserves_inner := fun x y => lorentzReflection_minkowskiInner _ x y
    (by norm_num [minkowskiInner, Fin.sum_univ_succ])
  future_time := by
    change 0 < lorentzReflection ![1, 3, 0, 0] (timeAxis 1) 0
    norm_num [lorentzReflection_apply, minkowskiInner, Fin.sum_univ_succ, timeAxis]

theorem boost_coordinates (p : Spacetime) :
    boost p = ![5 / 4 * p 0 - 3 / 4 * p 1 + 2,
      3 / 4 * p 0 - 5 / 4 * p 1 - 1, p 2 + 3, p 3] := by
  ext i
  fin_cases i <;> simp [PoincareEquiv.apply_eq, boost, lorentzReflection_apply,
    minkowskiInner, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

example (p : Spacetime) : boost.symm p =
    ![5 / 4 * (p 0 - 2) - 3 / 4 * (p 1 + 1),
      3 / 4 * (p 0 - 2) - 5 / 4 * (p 1 + 1), p 2 - 3, p 3] := by
  change boost.linear.symm p - boost.linear.symm boost.translation = _
  rw [← map_sub]
  change lorentzReflection ![1, 3, 0, 0] (p - ![2, -1, 3, 0]) = _
  ext i
  fin_cases i <;> simp [boost, lorentzReflection_apply, minkowskiInner,
    Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

def height : Spatial → ℝ := ellipsoidProfile (1 / 4) ![1, 2, 3]

theorem admissible : AdmissibleGraphCap height := by
  apply ellipsoid_admissible (1 / 4) ![1, 2, 3] (by norm_num)
  intro i
  fin_cases i <;> norm_num

theorem planar_target : twoFaceBoundaryIntegral height (fun _ => 0) = 48 * Real.pi := by
  rw [admissible.twoFaceBoundaryIntegral_planar, height,
    graphBoundaryIntegral_ellipsoid (1 / 4) ![1, 2, 3] (by norm_num) (by
      intro i; fin_cases i <;> norm_num)]
  norm_num [Fin.prod_univ_succ]
  ring

-- Retain the unequal-axis value on the metric-computed boosted joint, not an
-- action limit substituted for an area computation.
example : (∫ p, twoFaceSpacetimeWeight height (fun _ => 0) (boost.symm p)
    ∂jointInducedArea admissible (boost ∘ twoFaceLift (fun _ => 0))) = 48 * Real.pi := by
  rw [boost.twoFace_boundaryIntegral admissible.twoFace_planar, planar_target]

example : (∫ p, twoFaceSpacetimeWeight height (fun _ => 0) ((2 : ℝ)⁻¹ • p)
    ∂jointInducedArea admissible (fun x => (2 : ℝ) • twoFaceLift (fun _ => 0) x)) =
      192 * Real.pi := by
  rw [admissible.twoFace_planar.boundaryIntegral_dilate (by norm_num), planar_target]
  ring

example : (∫ p, twoFaceSpacetimeWeight height (fun _ => 0) ((1 / 2 : ℝ)⁻¹ • p)
    ∂jointInducedArea admissible (fun x => (1 / 2 : ℝ) • twoFaceLift (fun _ => 0) x)) =
      12 * Real.pi := by
  rw [admissible.twoFace_planar.boundaryIntegral_dilate (by norm_num), planar_target]
  ring

-- The boosted joint is not in ANY constant-time plane.
example : ∃ p ∈ boost '' twoFaceJoint height (fun _ => 0),
    ∃ q ∈ boost '' twoFaceJoint height (fun _ => 0), p 0 ≠ q 0 := by
  let x : JointSpace := (WithLp.equiv 2 _).symm ![1, 0, 0]
  let y : JointSpace := (WithLp.equiv 2 _).symm ![-1, 0, 0]
  have hx : x ∈ graphJoint height := by
    rw [height, graphJoint_ellipsoid (1 / 4) ![1, 2, 3] (by norm_num) (by
      intro i; fin_cases i <;> norm_num)]
    norm_num [x, ellipsoidJoint, Fin.sum_univ_succ, Matrix.cons_val_two]
  have hy : y ∈ graphJoint height := by
    rw [height, graphJoint_ellipsoid (1 / 4) ![1, 2, 3] (by norm_num) (by
      intro i; fin_cases i <;> norm_num)]
    norm_num [y, ellipsoidJoint, Fin.sum_univ_succ, Matrix.cons_val_two]
  refine ⟨boost (twoFaceLift (fun _ => 0) x), ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
    boost (twoFaceLift (fun _ => 0) y), ⟨_, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
  norm_num [boost_coordinates, twoFaceLift, x, y]

/-- Ambient Euclidean Gram density: a deliberate negative control, in all
four coordinates, NOT the coordinate function-space supremum norm. -/
def euclideanDensity (v w : Spacetime) : ℝ :=
  Real.sqrt ((∑ i, v i ^ 2) * (∑ i, w i ^ 2) - (∑ i, v i * w i) ^ 2)

def e₁ : Spacetime := ![0, 1, 0, 0]
def e₂ : Spacetime := ![0, 0, 1, 0]

-- These two directions really are joint tangents at the unequal ellipsoid's
-- north pole, not arbitrarily chosen vectors disconnected from the example.
example : let x : JointSpace := (WithLp.equiv 2 _).symm ![0, 0, 3]
    x ∈ graphJoint height ∧
    fderiv ℝ (fun y : JointSpace => height y) x (EuclideanSpace.basisFun (Fin 3) ℝ 0) = 0 ∧
    fderiv ℝ (fun y : JointSpace => height y) x (EuclideanSpace.basisFun (Fin 3) ℝ 1) = 0 := by
  dsimp only
  constructor
  · rw [height, graphJoint_ellipsoid (1 / 4) ![1, 2, 3] (by norm_num) (by
      intro i; fin_cases i <;> norm_num)]
    norm_num [ellipsoidJoint, Fin.sum_univ_succ, Matrix.cons_val_two]
  · simp [graph_differential_eq_inner, height, graphGradient_ellipsoid,
      ellipsoidGradient, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_succ, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

example : jointGramDensity (boost.linear e₁) (boost.linear e₂) = 1 ∧
    euclideanDensity (boost.linear e₁) (boost.linear e₂) = Real.sqrt (17 / 8) ∧
    1 < euclideanDensity (boost.linear e₁) (boost.linear e₂) := by
  have hL : jointGramDensity (boost.linear e₁) (boost.linear e₂) = 1 := by
    rw [jointGramDensity_lorentz]
    norm_num [jointGramDensity, minkowskiInner, e₁, e₂, Fin.sum_univ_succ]
  have hE : euclideanDensity (boost.linear e₁) (boost.linear e₂) = Real.sqrt (17 / 8) := by
    norm_num [euclideanDensity, boost, lorentzReflection_apply, minkowskiInner,
      e₁, e₂, Fin.sum_univ_succ]
  refine ⟨hL, hE, ?_⟩
  rw [hE]
  exact (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

-- Also cover the existing genuinely curved-future example, not only boosts.
example : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    IsFiniteMeasure (twoFaceJointArea (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c)) ∧
    Integrable (twoFaceWeight (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c))
      (twoFaceProjectedArea (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c)) := by
  obtain ⟨c, hc, hf, _⟩ := twoFace_curved_nonvacuity
  exact ⟨c, hc, hf, hf.finite_jointArea, hf.integrable_weight⟩

end JointSurfaceRegression
