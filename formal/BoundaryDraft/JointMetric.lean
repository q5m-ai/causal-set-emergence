import BoundaryDraft.TwoFaceContract
import BoundaryDraft.Poincare
import BoundaryDraft.GraphJacobian

/-!
# Spacelike graph tangent metrics and future unit normals

Signature is (+---). The positive joint metric is minus the restricted
Minkowski form. No measure or asymptotic identity is a geometric hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace BoundaryDraft

/-- A vector with Euclidean spatial coordinates and an explicit time component. -/
def jointVector (t : ℝ) (v : JointSpace) : Spacetime := Fin.cons t v

@[simp] theorem minkowskiInner_jointVector (s t : ℝ) (v w : JointSpace) :
    minkowskiInner (jointVector s v) (jointVector t w) = s * t - inner (𝕜 := ℝ) v w := by
  simp [jointVector, minkowskiInner, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Future-directed unit normal to the graph with spatial gradient `v`. -/
def jointUnitNormal (v : JointSpace) : Spacetime :=
  (Real.sqrt (1 - ‖v‖ ^ 2))⁻¹ • jointVector 1 v

@[simp] theorem jointUnitNormal_inner (v w : JointSpace) :
    minkowskiInner (jointUnitNormal v) (jointUnitNormal w) =
      (1 - inner (𝕜 := ℝ) v w) /
        (Real.sqrt (1 - ‖v‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) := by
  simp only [jointUnitNormal, minkowskiInner_smul_left, minkowskiInner_smul_right,
    minkowskiInner_jointVector, one_mul]
  ring

theorem jointUnitNormal_future_unit {v : JointSpace} (hv : ‖v‖ < 1) :
    0 < jointUnitNormal v 0 ∧ minkowskiInner (jointUnitNormal v) (jointUnitNormal v) = 1 := by
  have hd : 0 < 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hs := Real.sqrt_pos.mpr hd
  constructor
  · simpa [jointUnitNormal, jointVector] using inv_pos.mpr hs
  · rw [jointUnitNormal_inner, real_inner_self_eq_norm_sq, ← pow_two, Real.sq_sqrt hd.le]
    exact div_self hd.ne'

/-- Strict reverse Cauchy--Schwarz for distinct graph slopes. Strictness comes
from transversality, not from a choice made after squaring the angle. -/
theorem jointUnitNormal_inner_gt_one {v w : JointSpace}
    (hv : ‖v‖ < 1) (hw : ‖w‖ < 1) (hne : v ≠ w) :
    1 < minkowskiInner (jointUnitNormal v) (jointUnitNormal w) := by
  have hv0 := norm_nonneg v
  have hw0 := norm_nonneg w
  have hdv : 0 < 1 - ‖v‖ ^ 2 := by nlinarith
  have hdw : 0 < 1 - ‖w‖ ^ 2 := by nlinarith
  have hsv := Real.sqrt_pos.mpr hdv
  have hsw := Real.sqrt_pos.mpr hdw
  have hprod : 0 < Real.sqrt (1 - ‖v‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2) := mul_pos hsv hsw
  have hn : 0 < 1 - inner (𝕜 := ℝ) v w := by
    have hi := real_inner_le_norm v w
    have hm : ‖v‖ * ‖w‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hv.le hw0 hw
    linarith
  have hdiff : 0 < ‖v - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hid : (1 - inner (𝕜 := ℝ) v w) ^ 2 -
      (1 - ‖v‖ ^ 2) * (1 - ‖w‖ ^ 2) =
      ‖v - w‖ ^ 2 * (1 - ‖w‖ ^ 2) + inner (𝕜 := ℝ) (v - w) w ^ 2 := by
    rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
    ring
  have hsq : (Real.sqrt (1 - ‖v‖ ^ 2) * Real.sqrt (1 - ‖w‖ ^ 2)) ^ 2 =
      (1 - ‖v‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hdv.le, Real.sq_sqrt hdw.le]
  rw [jointUnitNormal_inner, one_lt_div hprod]
  nlinarith [mul_pos hdiff hdw, sq_nonneg (inner (𝕜 := ℝ) (v - w) w)]

/-- The graph tangent corresponding to a spatial vector. -/
def jointGraphTangent (q v : JointSpace) : Spacetime := jointVector (inner (𝕜 := ℝ) q v) v

theorem jointUnitNormal_orthogonal (q v : JointSpace) :
    minkowskiInner (jointUnitNormal q) (jointGraphTangent q v) = 0 := by
  simp [jointUnitNormal, jointGraphTangent, minkowskiInner_smul_left]

/-- Positive definite restriction to every nonzero graph tangent. -/
theorem jointGraphTangent_spacelike {q v : JointSpace} (hq : ‖q‖ < 1) (hv : v ≠ 0) :
    0 < -minkowskiInner (jointGraphTangent q v) (jointGraphTangent q v) := by
  have hvp := norm_pos_iff.mpr hv
  have hcs := abs_real_inner_le_norm q v
  have hb : ‖q‖ * ‖v‖ < ‖v‖ := by nlinarith
  have hs : (inner (𝕜 := ℝ) q v) ^ 2 < ‖v‖ ^ 2 := by
    have := (sq_lt_sq₀ (abs_nonneg (inner (𝕜 := ℝ) q v)) (norm_nonneg v)).mpr
      (hcs.trans_lt hb)
    simpa only [sq_abs] using this
  simp only [jointGraphTangent, minkowskiInner_jointVector, real_inner_self_eq_norm_sq]
  nlinarith

/-- Positive-branch rapidity as a function of the invariant normal product. -/
def jointAngle (C : ℝ) : ℝ := Real.log (C + Real.sqrt (C ^ 2 - 1))

theorem jointAngle_identities {C : ℝ} (hC : 1 < C) :
    0 < jointAngle C ∧ Real.cosh (jointAngle C) = C ∧
    Real.sinh (jointAngle C) = Real.sqrt (C ^ 2 - 1) ∧
    Real.cosh (jointAngle C) / Real.sinh (jointAngle C) = C / Real.sqrt (C ^ 2 - 1) := by
  have hd : 0 < C ^ 2 - 1 := by nlinarith
  have hs := Real.sqrt_pos.mpr hd
  have hs2 := Real.sq_sqrt hd.le
  have hp : 0 < C + Real.sqrt (C ^ 2 - 1) := by linarith
  have hi : (C + Real.sqrt (C ^ 2 - 1))⁻¹ = C - Real.sqrt (C ^ 2 - 1) := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith
  have hc : Real.cosh (jointAngle C) = C := by
    rw [jointAngle, Real.cosh_log hp, hi]; ring
  have hh : Real.sinh (jointAngle C) = Real.sqrt (C ^ 2 - 1) := by
    rw [jointAngle, Real.sinh_log hp, hi]; ring
  exact ⟨Real.log_pos (by linarith), hc, hh, by rw [hc, hh]⟩

/-- The positive area density of a spacelike two-frame, computed only from
its restricted Lorentzian metric. -/
def jointGramDensity (v w : Spacetime) : ℝ :=
  Real.sqrt (minkowskiInner v v * minkowskiInner w w - minkowskiInner v w ^ 2)

@[simp] theorem jointGramDensity_lorentz (F : PoincareEquiv) (v w : Spacetime) :
    jointGramDensity (F.linear v) (F.linear w) = jointGramDensity v w := by
  simp only [jointGramDensity, F.preserves_inner]

/-- Positive dilation has the two-dimensional area factor, not volume's
fourth-power factor. -/
theorem jointGramDensity_smul (s : ℝ) (v w : Spacetime) :
    jointGramDensity (s • v) (s • w) = s ^ 2 * jointGramDensity v w := by
  simp only [jointGramDensity, minkowskiInner_smul_left, minkowskiInner_smul_right]
  have he : s * (s * minkowskiInner v v) * (s * (s * minkowskiInner w w)) -
      (s * (s * minkowskiInner v w)) ^ 2 =
      (s ^ 2) ^ 2 * (minkowskiInner v v * minkowskiInner w w - minkowskiInner v w ^ 2) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg s)]

/-- Euclidean cross product, retained only for the spatial area computation. -/
def jointCross (v w : JointSpace) : JointSpace :=
  (WithLp.equiv 2 _).symm (crossProduct v w)

private theorem joint_cross_resolution (n v w : JointSpace) :
    inner (𝕜 := ℝ) n n • jointCross v w +
      inner (𝕜 := ℝ) n v • jointCross w n +
      inner (𝕜 := ℝ) n w • jointCross n v =
        inner (𝕜 := ℝ) n (jointCross v w) • n := by
  ext i
  fin_cases i <;> simp [jointCross, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, cross_apply, dotProduct, Fin.sum_univ_succ,
    Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The cross product of two tangents is parallel to their unit normal. -/
theorem jointCross_parallel (n v w : JointSpace) (hn : ‖n‖ = 1)
    (hv : inner (𝕜 := ℝ) n v = 0) (hw : inner (𝕜 := ℝ) n w = 0) :
    jointCross v w = inner (𝕜 := ℝ) n (jointCross v w) • n := by
  simpa only [real_inner_self_eq_norm_sq, hn, one_pow, one_smul, hv, hw,
    zero_smul, add_zero] using joint_cross_resolution n v w

private theorem joint_graph_gram_algebra (q v w : JointSpace) :
    minkowskiInner (jointGraphTangent q v) (jointGraphTangent q v) *
        minkowskiInner (jointGraphTangent q w) (jointGraphTangent q w) -
      minkowskiInner (jointGraphTangent q v) (jointGraphTangent q w) ^ 2 =
        (1 - ‖q‖ ^ 2) * graphAreaJacobian v w ^ 2 +
          inner (𝕜 := ℝ) q (jointCross v w) ^ 2 := by
  rw [graphAreaJacobian_sq]
  simp only [jointGraphTangent, minkowskiInner_jointVector, ← real_inner_self_eq_norm_sq]
  simp [jointCross, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    cross_apply, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail]
  ring

/-- The induced Lorentzian two-dimensional Gram determinant in any spatial
tangent frame. This is the chart Jacobian, not ambient four-dimensional area. -/
theorem jointGraph_gram (q n v w : JointSpace) (hn : ‖n‖ = 1)
    (hv : inner (𝕜 := ℝ) n v = 0) (hw : inner (𝕜 := ℝ) n w = 0) :
    minkowskiInner (jointGraphTangent q v) (jointGraphTangent q v) *
        minkowskiInner (jointGraphTangent q w) (jointGraphTangent q w) -
      minkowskiInner (jointGraphTangent q v) (jointGraphTangent q w) ^ 2 =
        (1 - (‖q‖ ^ 2 - inner (𝕜 := ℝ) q n ^ 2)) * graphAreaJacobian v w ^ 2 := by
  have hp := jointCross_parallel n v w hn hv hw
  have hn2 : graphAreaJacobian v w ^ 2 = inner (𝕜 := ℝ) n (jointCross v w) ^ 2 := by
    change ‖jointCross v w‖ ^ 2 = _
    conv_lhs => rw [hp]
    rw [norm_smul, Real.norm_eq_abs, hn, mul_one, sq_abs]
  rw [joint_graph_gram_algebra, hn2]
  conv_lhs => arg 2; rw [hp, inner_smul_right]
  ring

/-- A change of tangent coordinates has the absolute determinant Jacobian,
including orientation-reversing overlaps. -/
theorem jointGramDensity_change_frame (v w : Spacetime) (a b c d : ℝ) :
    jointGramDensity (a • v + b • w) (c • v + d • w) =
      |a * d - b * c| * jointGramDensity v w := by
  simp only [jointGramDensity, minkowskiInner_add_left, minkowskiInner_add_right,
    minkowskiInner_smul_left, minkowskiInner_smul_right, minkowskiInner_symm w v]
  calc
    _ = Real.sqrt ((a * d - b * c) ^ 2 *
        (minkowskiInner v v * minkowskiInner w w - minkowskiInner v w ^ 2)) := by
      congr 1
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end BoundaryDraft
