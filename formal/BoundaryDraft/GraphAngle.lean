import BoundaryDraft.GraphCollar
import BoundaryDraft.EllipsoidAngle

/-!
# Differential-derived normals and the general positive Lorentzian angle

Strict spacelikeness at the joint follows from the positive-part Lipschitz
bound on the open positive region, extended to its closure by continuity of
the actual differential. No global nonvanishing assumption is introduced.
This pointwise geometry does not assume or prove a coarea formula.
-/

open Set
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- Euclidean gradient obtained by Riesz duality from the actual differential. -/
def graphGradient (h : Spatial → ℝ) (x : JointSpace) : JointSpace :=
  gradient (fun y : JointSpace => h y) x

/-- The Euclidean slope used for the Lorentzian angle. -/
def graphSlope (h : Spatial → ℝ) (x : JointSpace) : ℝ := ‖graphGradient h x‖

theorem graphSlope_eq_norm_fderiv (h : Spatial → ℝ) (x : JointSpace) :
    graphSlope h x = ‖fderiv ℝ (fun y : JointSpace => h y) x‖ := by
  exact (InnerProductSpace.toDual ℝ JointSpace).symm.norm_map _

theorem graph_differential_eq_inner (h : Spatial → ℝ) (x v : JointSpace) :
    fderiv ℝ (fun y : JointSpace => h y) x v = inner (𝕜 := ℝ) (graphGradient h x) v := by
  change _ = (InnerProductSpace.toDual ℝ JointSpace)
    ((InnerProductSpace.toDual ℝ JointSpace).symm _) v
  rw [LinearIsometryEquiv.apply_symm_apply]

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- The same strict Lipschitz constant controls the differential throughout
the closed positive region, including the joint where the positive part is
not differentiable. Differentiation is only applied inside the positive set. -/
theorem exists_slope_bound : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧
    ∀ x ∈ graphClosedPositive h, graphSlope h x ≤ κ := by
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hh.lipschitz_positivePart
  have hopen : IsOpen {x : JointSpace | 0 < h x} :=
    hh.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)
  have hl : LipschitzOnWith ⟨κ, hκ⟩ (fun x : JointSpace => h x) {x | 0 < h x} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have he := hLip x y
    rw [max_eq_right hx.le, max_eq_right hy.le] at he
    change |h x - h y| ≤ κ * ‖y - x‖ at he
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using he
  have hbound : ∀ x ∈ {x : JointSpace | 0 < h x},
      ‖fderiv ℝ (fun y : JointSpace => h y) x‖ ≤ κ :=
    fun x hx => norm_fderiv_le_of_lipschitzOn ℝ (hopen.mem_nhds hx) hl
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro x hx
  rw [graphSlope_eq_norm_fderiv]
  exact le_on_closure hbound hh.continuousOn_fderiv_closedPositive.norm continuousOn_const hx

theorem graphSlope_lt_one (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    graphSlope h x < 1 := by
  obtain ⟨κ, _, hκ, hbound⟩ := hh.exists_slope_bound
  exact (hbound x hx).trans_lt hκ

theorem graphSlope_pos (x : JointSpace) (hx : x ∈ graphJoint h) :
    0 < graphSlope h x := by
  rw [graphSlope_eq_norm_fderiv]
  exact norm_pos_iff.mpr (hh.regular_zero x hx.1 hx.2)

theorem hasGradientAt (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    HasGradientAt (fun y : JointSpace => h y) (graphGradient h x) x :=
  ((hh.smooth_near x hx).differentiableAt (by norm_num)).hasGradientAt

end AdmissibleGraphCap

/-- Inward unit normal: increasing height enters the positive region. -/
def graphInward (h : Spatial → ℝ) (x : JointSpace) : JointSpace :=
  (graphSlope h x)⁻¹ • graphGradient h x

/-- Outward unit normal, opposite to the increasing-height direction. -/
def graphOutward (h : Spatial → ℝ) (x : JointSpace) : JointSpace :=
  -graphInward h x

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem graphInward_norm (x : JointSpace) (hx : x ∈ graphJoint h) :
    ‖graphInward h x‖ = 1 := by
  have hk := hh.graphSlope_pos x hx
  rw [graphInward, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk]
  exact inv_mul_cancel₀ hk.ne'

theorem graphOutward_norm (x : JointSpace) (hx : x ∈ graphJoint h) :
    ‖graphOutward h x‖ = 1 := by
  rw [graphOutward, norm_neg, hh.graphInward_norm x hx]

theorem graph_differential_inward (x : JointSpace) (hx : x ∈ graphJoint h) :
    fderiv ℝ (fun y : JointSpace => h y) x (graphInward h x) = graphSlope h x := by
  rw [graph_differential_eq_inner, graphInward, inner_smul_right, real_inner_self_eq_norm_sq]
  change (graphSlope h x)⁻¹ * graphSlope h x ^ 2 = _
  field_simp [(hh.graphSlope_pos x hx).ne']
  ring

theorem graph_differential_outward (x : JointSpace) (hx : x ∈ graphJoint h) :
    fderiv ℝ (fun y : JointSpace => h y) x (graphOutward h x) = -graphSlope h x := by
  rw [graphOutward, map_neg, hh.graph_differential_inward x hx]

/-- The rapidity is strictly positive, not a choice of sign from a squared
identity. The quotient is the actual `cosh θ / sinh θ`. -/
theorem graph_angle_identities (x : JointSpace) (hx : x ∈ graphJoint h) :
    0 < jointRapidity (graphSlope h x) ∧
    Real.cosh (jointRapidity (graphSlope h x)) = 1 / Real.sqrt (1 - graphSlope h x ^ 2) ∧
    Real.sinh (jointRapidity (graphSlope h x)) =
      graphSlope h x / Real.sqrt (1 - graphSlope h x ^ 2) ∧
    Real.tanh (jointRapidity (graphSlope h x)) = graphSlope h x ∧
    jointCoth (graphSlope h x) = 1 / ‖graphGradient h x‖ :=
  jointRapidity_identities _ (hh.graphSlope_pos x hx) (hh.graphSlope_lt_one x hx.1)

/-- The normalized graph-face direction and the plane-face inward direction
have the required Lorentzian angle. The graph direction is genuinely tangent
by `graph_differential_inward`. -/
theorem graph_face_cosh (x : JointSpace) (hx : x ∈ graphJoint h) :
    -minkowskiInner (Fin.cons 0 (graphInward h x))
      ((Real.sqrt (1 - graphSlope h x ^ 2))⁻¹ •
        (Fin.cons (-graphSlope h x) (graphInward h x) : Spacetime)) =
      Real.cosh (jointRapidity (graphSlope h x)) :=
  joint_face_cosh _ (hh.graphInward_norm x hx) _
    (hh.graphSlope_pos x hx) (hh.graphSlope_lt_one x hx.1)

theorem graph_face_unit (x : JointSpace) (hx : x ∈ graphJoint h) :
    minkowskiInner
      ((Real.sqrt (1 - graphSlope h x ^ 2))⁻¹ •
        (Fin.cons (-graphSlope h x) (graphInward h x) : Spacetime))
      ((Real.sqrt (1 - graphSlope h x ^ 2))⁻¹ •
        (Fin.cons (-graphSlope h x) (graphInward h x) : Spacetime)) = -1 :=
  joint_graph_unit _ (hh.graphInward_norm x hx) _
    (hh.graphSlope_pos x hx) (hh.graphSlope_lt_one x hx.1)

end AdmissibleGraphCap

/-- Both face directions are orthogonal to the kernel of the actual joint
differential. No presumed surface chart is needed for this linear fact. -/
theorem graph_face_joint_orthogonal (h : Spatial → ℝ) (x v : JointSpace)
    (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0) :
    minkowskiInner (Fin.cons 0 (graphInward h x)) (Fin.cons 0 v) = 0 ∧
    minkowskiInner (Fin.cons (-graphSlope h x) (graphInward h x)) (Fin.cons 0 v) = 0 := by
  rw [graph_differential_eq_inner] at hv
  have hi : inner (𝕜 := ℝ) (graphInward h x) v = 0 := by
    simp only [graphInward, inner_smul_left, RCLike.conj_to_real, hv, mul_zero]
  have hs : ∑ i : Fin 3, graphInward h x i * v i = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hi
  simp [minkowskiInner, hs]

/-- The general gradient recovers the original explicit ellipsoid gradient. -/
theorem graphGradient_ellipsoid (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) :
    graphGradient (ellipsoidProfile a b) x = ellipsoidGradient a b x :=
  (hasGradientAt_ellipsoidProfile a b x).gradient

end BoundaryDraft
