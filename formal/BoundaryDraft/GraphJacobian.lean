import BoundaryDraft.GraphAngle
import Mathlib.LinearAlgebra.CrossProduct

/-!
# The local coarea Jacobian factor

For a height-coordinate frame `(z,v,w)` satisfying `dh z = 1` and
`dh v = dh w = 0`, its volume Jacobian is the induced tangential area
Jacobian divided by the actual gradient norm. This is a linear-algebra
identity, not yet a theorem transforming surface measures or integrals.
-/

open scoped Matrix
noncomputable section
namespace BoundaryDraft

private theorem cross_cofactor_resolution (g z v w : Spatial) :
    (g ⬝ᵥ z) • crossProduct v w + (g ⬝ᵥ v) • crossProduct w z +
      (g ⬝ᵥ w) • crossProduct z v = (z ⬝ᵥ crossProduct v w) • g := by
  ext i
  fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_succ,
    Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The tangential area Jacobian is the norm of the cross product in the
Euclidean metric, never the coordinate supremum norm. -/
def graphAreaJacobian (v w : JointSpace) : ℝ :=
  ‖((WithLp.equiv 2 _).symm (crossProduct v w) : JointSpace)‖

theorem graphAreaJacobian_sq (v w : JointSpace) :
    graphAreaJacobian v w ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 - inner (𝕜 := ℝ) v w ^ 2 := by
  have h := cross_dot_cross (v : Spatial) w v w
  simp only [graphAreaJacobian, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change (crossProduct v w) ⬝ᵥ (crossProduct v w) =
    (v : Spatial) ⬝ᵥ v * (w : Spatial) ⬝ᵥ w - ((w : Spatial) ⬝ᵥ v) ^ 2
  rw [h]
  rw [dotProduct_comm (v : Spatial) (w : Spatial)]
  ring

/-- The positive square-root branch of the induced metric determinant. -/
theorem graphAreaJacobian_eq_sqrt_gram (v w : JointSpace) :
    graphAreaJacobian v w =
      Real.sqrt (‖v‖ ^ 2 * ‖w‖ ^ 2 - inner (𝕜 := ℝ) v w ^ 2) := by
  rw [← graphAreaJacobian_sq]
  exact (Real.sqrt_sq (show 0 ≤ graphAreaJacobian v w from norm_nonneg _)).symm

/-- The determinant is that of the matrix whose columns are the three frame
vectors (transposing the displayed row matrix has the same determinant).
Every constraint is stated using the actual Fréchet differential. -/
theorem graph_coarea_frame_jacobian (h : Spatial → ℝ) (x z v w : JointSpace)
    (hz : fderiv ℝ (fun y : JointSpace => h y) x z = 1)
    (hv : fderiv ℝ (fun y : JointSpace => h y) x v = 0)
    (hw : fderiv ℝ (fun y : JointSpace => h y) x w = 0) :
    |Matrix.det ![(z : Spatial), (v : Spatial), (w : Spatial)]| =
      graphAreaJacobian v w / ‖graphGradient h x‖ := by
  have hd (a : JointSpace) : fderiv ℝ (fun y : JointSpace => h y) x a =
      (graphGradient h x : Spatial) ⬝ᵥ a := by
    rw [graph_differential_eq_inner]
    change (a : Spatial) ⬝ᵥ graphGradient h x = (graphGradient h x : Spatial) ⬝ᵥ a
    exact dotProduct_comm _ _
  rw [hd z] at hz
  rw [hd v] at hv
  rw [hd w] at hw
  have he := cross_cofactor_resolution (graphGradient h x) z v w
  simp only [hz, hv, hw, one_smul, zero_smul, add_zero, triple_product_eq_det] at he
  have hn : graphGradient h x ≠ 0 := by
    intro hg
    have heq : (graphGradient h x : Spatial) = 0 := congrArg (WithLp.equiv 2 _) hg
    rw [heq, zero_dotProduct] at hz
    norm_num at hz
  have hn' : ‖graphGradient h x‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  apply (eq_div_iff hn').mpr
  have he' : ((WithLp.equiv 2 _).symm (crossProduct v w) : JointSpace) =
      Matrix.det ![(z : Spatial), (v : Spatial), (w : Spatial)] • graphGradient h x := by
    exact congrArg (WithLp.equiv 2 _).symm he
  rw [graphAreaJacobian, he', norm_smul, Real.norm_eq_abs]

end BoundaryDraft
