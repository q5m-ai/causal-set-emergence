import BoundaryDraft

/-! Independent regularity, positive-branch, surface-integral, and variable-angle
regressions. The numerical example has one connected joint and weights 2 and 6.
The existing deterministic regression remains unchanged. -/

open BoundaryDraft MeasureTheory Set
open scoped BigOperators
noncomputable section

private theorem axes : ∀ i : Fin 3, 2 * (1 / 4 : ℝ) < ![1, 2, 3] i := by
  intro i
  fin_cases i <;> norm_num

example : IsConnected (ellipsoidJoint ![1, 2, 3]) :=
  isConnected_ellipsoidJoint _ (fun i => by have := axes i; linarith)

example (x : JointSpace) (hx : x ∈ ellipsoidJoint ![1, 2, 3]) :
    fderiv ℝ (fun y : JointSpace => ellipsoidProfile (1 / 4) ![1, 2, 3] y) x ≠ 0 :=
  ellipsoid_joint_regular _ _ (by norm_num) (fun i => by have := axes i; linarith) x hx

example (x : JointSpace) (hx : x ∈ ellipsoidJoint ![1, 2, 3]) :
    0 < jointRapidity (ellipsoidSlope (1 / 4) ![1, 2, 3] x) ∧
    Real.cosh (jointRapidity (ellipsoidSlope (1 / 4) ![1, 2, 3] x)) =
      1 / Real.sqrt (1 - ellipsoidSlope (1 / 4) ![1, 2, 3] x ^ 2) ∧
    Real.sinh (jointRapidity (ellipsoidSlope (1 / 4) ![1, 2, 3] x)) =
      ellipsoidSlope (1 / 4) ![1, 2, 3] x /
        Real.sqrt (1 - ellipsoidSlope (1 / 4) ![1, 2, 3] x ^ 2) ∧
    Real.tanh (jointRapidity (ellipsoidSlope (1 / 4) ![1, 2, 3] x)) =
      ellipsoidSlope (1 / 4) ![1, 2, 3] x ∧
    jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x) =
      1 / ellipsoidSlope (1 / 4) ![1, 2, 3] x :=
  jointRapidity_identities _
    (ellipsoidSlope_pos _ _ (by norm_num) (fun i => by have := axes i; linarith) x hx)
    (ellipsoidSlope_lt_one _ _ (by norm_num) axes x hx)

example : jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3]
    (ellipsoidAxisPoint ![1, 2, 3] 0)) = 2 := by
  rw [ellipsoid_coth_axis _ _ (by norm_num) axes]
  norm_num

example : jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3]
    (ellipsoidAxisPoint ![1, 2, 3] 2)) = 6 := by
  rw [ellipsoid_coth_axis _ _ (by norm_num) axes]
  change (3 : ℝ) / (2 * (1 / 4)) = 6
  norm_num

example : ellipsoidSlope (1 / 4) ![1, 2, 3] (ellipsoidAxisPoint ![1, 2, 3] 0) = 1 / 2 ∧
    ellipsoidSlope (1 / 4) ![1, 2, 3] (ellipsoidAxisPoint ![1, 2, 3] 2) = 1 / 6 := by
  simp only [ellipsoidSlope_axis _ _ (by norm_num : (0 : ℝ) < 1 / 4)
    (fun i => by have := axes i; linarith)]
  change (2 * (1 / 4 : ℝ) / 1 = 1 / 2) ∧ (2 * (1 / 4 : ℝ) / 3 = 1 / 6)
  norm_num

example : ∃ x ∈ ellipsoidJoint ![1, 2, 3], ∃ y ∈ ellipsoidJoint ![1, 2, 3],
    jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x) ≠
      jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] y) :=
  ellipsoid_angle_nonconstant _ _ (by norm_num) axes 0 2 (by change (1 : ℝ) ≠ 3; norm_num)

example : Integrable (fun x : ellipsoidJoint ![1, 2, 3] =>
    jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x.val))
      (ellipsoidSurfaceMeasure ![1, 2, 3] (fun i => by have := axes i; linarith)) :=
  integrable_ellipsoid_coth _ _ (by norm_num) axes

example : (∫ x : ellipsoidJoint ![1, 2, 3], jointCoth (ellipsoidSlope (1 / 4) ![1, 2, 3] x.val)
    ∂ellipsoidSurfaceMeasure ![1, 2, 3] (fun i => by have := axes i; linarith)) =
      48 * Real.pi := by
  rw [integral_ellipsoid_coth _ _ (by norm_num) axes]
  norm_num [Fin.prod_univ_succ]
  ring

-- The north-pole Jacobian is the product of the two transverse axes,
-- checked independently of the angle and integral theorems.
example : ellipsoidSurfaceJacobian ![1, 2, 3]
    ⟨(WithLp.equiv 2 _).symm ![0, 0, 1], by
      simp [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩ = 2 := by
  norm_num [ellipsoidSurfaceJacobian, ellipsoidReciprocal,
    EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.prod_univ_succ]
  rw [show Real.sqrt 9 = 3 by norm_num [Real.sqrt_eq_iff_mul_self_eq]]
  norm_num
