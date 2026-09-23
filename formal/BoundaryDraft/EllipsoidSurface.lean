import BoundaryDraft.EllipsoidAngle
import BoundaryDraft.EllipsoidLimit
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.CrossProduct

/-!
# A global parametric surface measure and the variable-angle integral

The parameter space is the entire Euclidean unit sphere, equipped with
mathlib's polar surface measure `volume.toSphere`. Axis scaling is a global
homeomorphism onto the joint. The density is its tangential area Jacobian,
verified below by the cross-product identity. Thus there are no angular chart
seams, discarded poles, or boundary replacements in this representation.
-/

open MeasureTheory Set
open scoped BigOperators Matrix
noncomputable section
namespace BoundaryDraft

abbrev JointSphere := Metric.sphere (0 : JointSpace) 1

/-- Ambient linear parameterization, also used for its tangent derivative. -/
def ellipsoidAxisLinear (b : Fin 3 → ℝ) : JointSpace →ₗ[ℝ] JointSpace where
  toFun x := (WithLp.equiv 2 _).symm (fun i => b i * x i)
  map_add' x y := by ext i; simp; ring
  map_smul' c x := by ext i; simp; ring

@[simp] theorem ellipsoidAxisLinear_apply (b : Fin 3 → ℝ) (x : JointSpace) (i : Fin 3) :
    ellipsoidAxisLinear b x i = b i * x i := rfl

theorem hasFDerivAt_ellipsoidAxisLinear (b : Fin 3 → ℝ) (x : JointSpace) :
    HasFDerivAt (ellipsoidAxisLinear b) (ellipsoidAxisLinear b).toContinuousLinearMap x :=
  (ellipsoidAxisLinear b).toContinuousLinearMap.hasFDerivAt

theorem jointSphere_sq (u : JointSphere) : ∑ i : Fin 3, u.val i ^ 2 = 1 := by
  have h := PiLp.norm_sq_eq_of_L2 _ u.val
  rw [show ‖u.val‖ = 1 from mem_sphere_zero_iff_norm.mp u.property] at h
  simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm

/-- A global parameterization with a checked inverse: no multiplicity factor. -/
def ellipsoidJointParam (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    JointSphere ≃ₜ ellipsoidJoint b where
  toFun u := ⟨ellipsoidAxisLinear b u.val, by
    simpa [ellipsoidJoint, mul_div_cancel_left₀ _ (hb _).ne'] using jointSphere_sq u⟩
  invFun x := ⟨(WithLp.equiv 2 _).symm (fun i => x.val i / b i), by
    have h : ‖((WithLp.equiv 2 _).symm (fun i => x.val i / b i) : JointSpace)‖ ^ 2 = 1 := by
      simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using x.property
    simp only [Metric.mem_sphere, dist_zero_right]
    nlinarith [norm_nonneg ((WithLp.equiv 2 _).symm (fun i => x.val i / b i) : JointSpace)]⟩
  left_inv u := by ext i; simp [ellipsoidAxisLinear, (hb i).ne']
  right_inv x := by ext i; exact mul_div_cancel₀ _ (hb i).ne'
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (ellipsoidAxisLinear b).continuous_of_finiteDimensional.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_equiv_symm 2 _).comp
    exact continuous_pi fun i => ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).div_const _

/-- The joint is a single connected surface, not a disjoint family of examples. -/
theorem isConnected_ellipsoidJoint (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    IsConnected (ellipsoidJoint b) := by
  have hs : IsConnected (Metric.sphere (0 : JointSpace) 1) :=
    isConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 (by norm_num)
  have hr : ellipsoidAxisLinear b '' Metric.sphere (0 : JointSpace) 1 = ellipsoidJoint b := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (ellipsoidJointParam b hb ⟨u, hu⟩).property
    · intro hx
      exact ⟨((ellipsoidJointParam b hb).symm ⟨x, hx⟩).val,
        ((ellipsoidJointParam b hb).symm ⟨x, hx⟩).property,
        congrArg Subtype.val ((ellipsoidJointParam b hb).apply_symm_apply ⟨x, hx⟩)⟩
  rw [← hr]
  exact hs.image _ (ellipsoidAxisLinear b).continuous_of_finiteDimensional.continuousOn

/-- Reciprocal-axis normal on the parameter sphere. -/
def ellipsoidReciprocal (b : Fin 3 → ℝ) (u : JointSpace) : JointSpace :=
  (WithLp.equiv 2 _).symm (fun i => u i / b i)

/-- Area density of the global parameterization. It is independent of `a`. -/
def ellipsoidSurfaceJacobian (b : Fin 3 → ℝ) (u : JointSphere) : ℝ :=
  (∏ i : Fin 3, b i) * ‖ellipsoidReciprocal b u.val‖

/-- The derivative's cross product is the cofactor action on the original
cross product. This proves the area Jacobian rather than assuming an ellipsoid
surface-area formula. -/
theorem ellipsoid_axis_cross (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (v w : JointSpace) :
    crossProduct (ellipsoidAxisLinear b v) (ellipsoidAxisLinear b w) =
      fun i => (∏ j : Fin 3, b j) * (crossProduct v w i / b i) := by
  ext i
  fin_cases i <;> simp [cross_apply, Fin.prod_univ_succ]
  all_goals field_simp [(hb 0).ne', (hb 1).ne', (hb 2).ne']; ring

/-- For an oriented unit-area tangent frame `v × w = u`, the norm of the
transformed cross product is exactly the declared area density. -/
theorem ellipsoid_tangent_jacobian (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (u : JointSphere) (v w : JointSpace) (hvw : crossProduct v w = (u.val : Spatial)) :
    ‖((WithLp.equiv 2 _).symm
      (crossProduct (ellipsoidAxisLinear b v) (ellipsoidAxisLinear b w)) : JointSpace)‖ =
        ellipsoidSurfaceJacobian b u := by
  rw [ellipsoid_axis_cross b hb, hvw]
  change ‖(∏ i : Fin 3, b i) • ellipsoidReciprocal b u.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Finset.prod_pos fun i _ => hb i)]
  rfl

/-- The area factor is the positive square root of the induced metric's
Gram determinant. This ties the density to the derivative's Euclidean metric,
not merely to a convenient integration weight. -/
theorem ellipsoid_surface_gram (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (u : JointSphere) (v w : JointSpace) (hvw : crossProduct v w = (u.val : Spatial)) :
    ellipsoidSurfaceJacobian b u ^ 2 =
      ‖ellipsoidAxisLinear b v‖ ^ 2 * ‖ellipsoidAxisLinear b w‖ ^ 2 -
        inner (𝕜 := ℝ) (ellipsoidAxisLinear b v) (ellipsoidAxisLinear b w) ^ 2 := by
  rw [← ellipsoid_tangent_jacobian b hb u v w hvw]
  have h := cross_dot_cross (ellipsoidAxisLinear b v : Spatial)
    (ellipsoidAxisLinear b w : Spatial) (ellipsoidAxisLinear b v : Spatial)
    (ellipsoidAxisLinear b w : Spatial)
  simp only [← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (crossProduct (ellipsoidAxisLinear b v) (ellipsoidAxisLinear b w)) ⬝ᵥ
    (crossProduct (ellipsoidAxisLinear b v) (ellipsoidAxisLinear b w)) = _
  rw [h]
  change (ellipsoidAxisLinear b v : Spatial) ⬝ᵥ ellipsoidAxisLinear b v *
      (ellipsoidAxisLinear b w : Spatial) ⬝ᵥ ellipsoidAxisLinear b w -
      (ellipsoidAxisLinear b v : Spatial) ⬝ᵥ ellipsoidAxisLinear b w *
        (ellipsoidAxisLinear b w : Spatial) ⬝ᵥ ellipsoidAxisLinear b v =
    (ellipsoidAxisLinear b v : Spatial) ⬝ᵥ ellipsoidAxisLinear b v *
      (ellipsoidAxisLinear b w : Spatial) ⬝ᵥ ellipsoidAxisLinear b w -
      ((ellipsoidAxisLinear b w : Spatial) ⬝ᵥ ellipsoidAxisLinear b v) ^ 2
  rw [dotProduct_comm (ellipsoidAxisLinear b v : Spatial) (ellipsoidAxisLinear b w)]
  ring

theorem ellipsoidSlope_param (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (u : JointSphere) :
    ellipsoidSlope a b (ellipsoidJointParam b hb u).val =
      2 * a * ‖ellipsoidReciprocal b u.val‖ := by
  have he : ellipsoidGradient a b (ellipsoidJointParam b hb u).val =
      (-2 * a) • ellipsoidReciprocal b u.val := by
    ext i
    change -2 * a * (b i * u.val i) / b i ^ 2 = (-2 * a) * (u.val i / b i)
    field_simp [(hb i).ne']
    ring
  rw [ellipsoidSlope, he, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith)]
  ring

theorem ellipsoidReciprocal_pos (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (u : JointSphere) :
    0 < ‖ellipsoidReciprocal b u.val‖ := by
  have h := ellipsoidSlope_pos 1 b (by norm_num) hb _ (ellipsoidJointParam b hb u).property
  rw [ellipsoidSlope_param 1 b (by norm_num) hb] at h
  linarith

theorem continuous_ellipsoidSurfaceJacobian (b : Fin 3 → ℝ) :
    Continuous (ellipsoidSurfaceJacobian b) := by
  unfold ellipsoidSurfaceJacobian ellipsoidReciprocal
  apply continuous_const.mul
  apply Continuous.norm
  apply (PiLp.continuous_equiv_symm 2 _).comp
  exact continuous_pi fun i => ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).div_const _

/-- Parametric induced area: the full sphere's polar area, multiplied by the
checked tangential Jacobian, transported by a global homeomorphism. -/
def ellipsoidSurfaceMeasure (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    Measure (ellipsoidJoint b) :=
  Measure.map (ellipsoidJointParam b hb)
    ((volume : Measure JointSpace).toSphere.withDensity
      (fun u => ENNReal.ofReal (ellipsoidSurfaceJacobian b u)))

/-- Sphere area is derived from polar disintegration and the three-ball volume. -/
theorem jointSphere_area : (volume : Measure JointSpace).toSphere.real univ = 4 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ]
  norm_num [Measure.real, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem ellipsoidSurfaceJacobian_pos (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (u : JointSphere) : 0 < ellipsoidSurfaceJacobian b u :=
  mul_pos (Finset.prod_pos fun i _ => hb i) (ellipsoidReciprocal_pos b hb u)

/-- Positive-branch induced area density. -/
theorem ellipsoidSurfaceJacobian_eq_sqrt_gram (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (u : JointSphere) (v w : JointSpace) (hvw : crossProduct v w = (u.val : Spatial)) :
    ellipsoidSurfaceJacobian b u =
      Real.sqrt (‖ellipsoidAxisLinear b v‖ ^ 2 * ‖ellipsoidAxisLinear b w‖ ^ 2 -
        inner (𝕜 := ℝ) (ellipsoidAxisLinear b v) (ellipsoidAxisLinear b w) ^ 2) := by
  rw [← ellipsoid_surface_gram b hb u v w hvw,
    Real.sqrt_sq (ellipsoidSurfaceJacobian_pos b hb u).le]

/-- The Jacobian cancels the *proved positive* Lorentzian weight pointwise. -/
theorem ellipsoid_angle_area_density (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) (u : JointSphere) :
    ellipsoidSurfaceJacobian b u *
      jointCoth (ellipsoidSlope a b (ellipsoidJointParam b
        (fun i => by linarith [hb i]) u).val) = (∏ i : Fin 3, b i) / (2 * a) := by
  have hb0 : ∀ i, 0 < b i := fun i => by linarith [hb i]
  rw [ellipsoid_coth_eq a b ha hb _ (ellipsoidJointParam b hb0 u).property]
  change ellipsoidSurfaceJacobian b u * (1 / ellipsoidSlope a b _) = _
  rw [ellipsoidSlope_param a b ha hb0, ellipsoidSurfaceJacobian]
  field_simp [(ellipsoidReciprocal_pos b hb0 u).ne']
  ring

/-- Exact global change of parameters for the declared surface measure. -/
theorem integral_ellipsoidSurfaceMeasure (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : ellipsoidJoint b → ℝ) :
    (∫ x, f x ∂ellipsoidSurfaceMeasure b hb) =
      ∫ u : JointSphere, ellipsoidSurfaceJacobian b u * f (ellipsoidJointParam b hb u)
        ∂(volume : Measure JointSpace).toSphere := by
  unfold ellipsoidSurfaceMeasure
  rw [show (ellipsoidJointParam b hb : JointSphere → ellipsoidJoint b) =
    (ellipsoidJointParam b hb).toMeasurableEquiv from rfl, integral_map_equiv]
  rw [integral_withDensity_eq_integral_toReal_smul
    ((continuous_ellipsoidSurfaceJacobian b).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [ENNReal.toReal_ofReal (ellipsoidSurfaceJacobian_pos b hb u).le, smul_eq_mul]

/-- Absolute integrability, established before evaluating the integral. -/
theorem integrable_ellipsoid_coth (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    Integrable (fun x : ellipsoidJoint b => jointCoth (ellipsoidSlope a b x.val))
      (ellipsoidSurfaceMeasure b (fun i => by linarith [hb i])) := by
  unfold ellipsoidSurfaceMeasure
  rw [show (ellipsoidJointParam b (fun i => by linarith [hb i]) :
    JointSphere → ellipsoidJoint b) =
    (ellipsoidJointParam b (fun i => by linarith [hb i])).toMeasurableEquiv from rfl,
    integrable_map_equiv]
  rw [integrable_withDensity_iff_integrable_smul'
    ((continuous_ellipsoidSurfaceJacobian b).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun u : JointSphere =>
      (ENNReal.ofReal (ellipsoidSurfaceJacobian b u)).toReal •
        jointCoth (ellipsoidSlope a b (ellipsoidJointParam b
          (fun i => by linarith [hb i]) u).val)) =
      fun _ => (∏ i : Fin 3, b i) / (2 * a) := by
    funext u
    rw [ENNReal.toReal_ofReal (ellipsoidSurfaceJacobian_pos b
      (fun i => by linarith [hb i]) u).le, smul_eq_mul]
    exact ellipsoid_angle_area_density a b ha hb u
  change Integrable (fun u : JointSphere =>
    (ENNReal.ofReal (ellipsoidSurfaceJacobian b u)).toReal •
      jointCoth (ellipsoidSlope a b (ellipsoidJointParam b
        (fun i => by linarith [hb i]) u).val)) _
  rw [he]
  exact integrable_const _

/-- The variable-angle boundary integral equals the deterministic limit constant. -/
theorem integral_ellipsoid_coth (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    (∫ x : ellipsoidJoint b, jointCoth (ellipsoidSlope a b x.val)
      ∂ellipsoidSurfaceMeasure b (fun i => by linarith [hb i])) =
        2 * Real.pi * (∏ i : Fin 3, b i) / a := by
  rw [integral_ellipsoidSurfaceMeasure]
  simp_rw [ellipsoid_angle_area_density a b ha hb]
  rw [integral_const, smul_eq_mul, jointSphere_area]
  ring

/-- Geometric interpretation of the existing limit, reused without reproving it. -/
theorem ellipsoid_limit_eq_joint_integral (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    Filter.Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b)))
      Filter.atTop (nhds (∫ x : ellipsoidJoint b, jointCoth (ellipsoidSlope a b x.val)
        ∂ellipsoidSurfaceMeasure b (fun i => by linarith [hb i]))) := by
  rw [integral_ellipsoid_coth a b ha hb]
  exact ellipsoidLimitGoal a b ha hb

/-- Positive endpoint of one principal axis. -/
def ellipsoidAxisPoint (b : Fin 3 → ℝ) (j : Fin 3) : JointSpace :=
  (WithLp.equiv 2 _).symm (Pi.single j (b j))

theorem ellipsoidAxisPoint_mem (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (j : Fin 3) :
    ellipsoidAxisPoint b j ∈ ellipsoidJoint b := by
  change (∑ i : Fin 3, ((Pi.single j (b j) : Spatial) i / b i) ^ 2) = 1
  rw [Finset.sum_eq_single j]
  · simp [(hb j).ne']
  · intro i _ hij
    simp [Pi.single_apply, hij]
  · simp

theorem ellipsoidSlope_axis (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (j : Fin 3) :
    ellipsoidSlope a b (ellipsoidAxisPoint b j) = 2 * a / b j := by
  have hs : ellipsoidSlope a b (ellipsoidAxisPoint b j) ^ 2 = (2 * a / b j) ^ 2 := by
    rw [ellipsoidSlope_sq]
    change (∑ i : Fin 3, (-2 * a * (Pi.single j (b j) : Spatial) i / b i ^ 2) ^ 2) = _
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
      field_simp [(hb j).ne']
      ring
    · intro i _ hij
      simp [Pi.single_apply, hij]
    · simp
  exact (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (by positivity) (hb j).le)).mp hs

theorem ellipsoid_coth_axis (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) (j : Fin 3) :
    jointCoth (ellipsoidSlope a b (ellipsoidAxisPoint b j)) = b j / (2 * a) := by
  have hb0 : ∀ i, 0 < b i := fun i => by linarith [hb i]
  rw [ellipsoid_coth_eq a b ha hb _ (ellipsoidAxisPoint_mem b hb0 j)]
  change 1 / ellipsoidSlope a b (ellipsoidAxisPoint b j) = _
  rw [ellipsoidSlope_axis a b ha hb0 j]
  field_simp

/-- Unequal axes give distinct weights on the same connected joint. -/
theorem ellipsoid_angle_nonconstant (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) (i j : Fin 3) (hij : b i ≠ b j) :
    ∃ x ∈ ellipsoidJoint b, ∃ y ∈ ellipsoidJoint b,
      jointCoth (ellipsoidSlope a b x) ≠ jointCoth (ellipsoidSlope a b y) := by
  have hb0 : ∀ i, 0 < b i := fun i => by linarith [hb i]
  refine ⟨ellipsoidAxisPoint b i, ellipsoidAxisPoint_mem b hb0 i,
    ellipsoidAxisPoint b j, ellipsoidAxisPoint_mem b hb0 j, ?_⟩
  rw [ellipsoid_coth_axis a b ha hb i, ellipsoid_coth_axis a b ha hb j]
  exact fun h => hij ((div_left_inj' (by positivity : 2 * a ≠ 0)).mp h)

end BoundaryDraft
