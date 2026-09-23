import BoundaryDraft.EllipsoidGeometry
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Regularity of the concrete ellipsoid joint

Gradients and unit normals use the Euclidean norm, not the coordinate sup norm.
The profile and axis hypotheses are those of `EllipsoidLimitGoal`.
-/

open Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

abbrev JointSpace := EuclideanSpace ℝ (Fin 3)

/-- The actual zero level, expressed independently of the height scale. -/
def ellipsoidJoint (b : Fin 3 → ℝ) : Set JointSpace :=
  {x | ∑ i : Fin 3, (x i / b i) ^ 2 = 1}

/-- Euclidean gradient of the existing profile (the sign is inward). -/
def ellipsoidGradient (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) : JointSpace :=
  (WithLp.equiv 2 _).symm (fun i => -2 * a * x i / b i ^ 2)

/-- Gradient norm, hence the slope appearing in the Lorentzian angle. -/
def ellipsoidSlope (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) : ℝ :=
  ‖ellipsoidGradient a b x‖

theorem ellipsoidJoint_eq_zero (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) :
    ellipsoidJoint b = {x : JointSpace | ellipsoidProfile a b x = 0} := by
  ext x
  simp only [ellipsoidJoint, mem_setOf_eq, ellipsoidProfile, mul_eq_zero,
    ha.ne', false_or, sub_eq_zero]
  exact eq_comm

theorem contDiff_ellipsoidProfile (a : ℝ) (b : Fin 3 → ℝ) :
    ContDiff ℝ ⊤ (fun x : JointSpace => ellipsoidProfile a b x) := by
  exact contDiff_const.mul (contDiff_const.sub (ContDiff.sum fun i _ =>
    (((EuclideanSpace.proj i (𝕜 := ℝ)).contDiff).div_const (b i)).pow 2))

theorem hasGradientAt_ellipsoidProfile (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) :
    HasGradientAt (fun y : JointSpace => ellipsoidProfile a b y)
      (ellipsoidGradient a b x) x := by
  let p := fun i : Fin 3 => EuclideanSpace.proj i (𝕜 := ℝ)
  have h := (hasFDerivAt_const a x).mul
    ((hasFDerivAt_const (1 : ℝ) x).sub
      (HasFDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
        (hasDerivAt_pow 2 (x i * (b i)⁻¹)).comp_hasFDerivAt x
          ((p i).hasFDerivAt.mul_const (b i)⁻¹)))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext v
  simp [InnerProductSpace.toDual_apply, ellipsoidGradient, p,
    PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum, Finset.sum_mul,
    div_pow, div_eq_mul_inv]
  congr 1
  funext i
  ring

theorem ellipsoidSlope_sq (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) :
    ellipsoidSlope a b x ^ 2 = ∑ i : Fin 3, (-2 * a * x i / b i ^ 2) ^ 2 := by
  simp only [ellipsoidSlope, ellipsoidGradient, PiLp.norm_sq_eq_of_L2,
    Real.norm_eq_abs, sq_abs]
  rfl

/-- Nonvanishing is proved at every joint point, not postulated as regularity. -/
theorem ellipsoidSlope_pos (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    0 < ellipsoidSlope a b x := by
  apply norm_pos_iff.mpr
  intro h
  have hz : ∀ i, x i = 0 := by
    intro i
    have hi := congrArg (fun v : JointSpace => v i) h
    change -2 * a * x i / b i ^ 2 = 0 at hi
    have : -2 * a * x i = 0 := (div_eq_zero_iff).mp hi |>.resolve_right (pow_ne_zero 2 (hb i).ne')
    rcases mul_eq_zero.mp this with h | h
    · nlinarith
    · exact h
  have := hx
  simp [ellipsoidJoint, hz] at this

/-- The original strict axis hypothesis gives strict spacelikeness at the joint. -/
theorem ellipsoidSlope_lt_one (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    ellipsoidSlope a b x < 1 := by
  obtain ⟨j, hj⟩ := Finite.exists_min b
  have hb0 : ∀ i, 0 < b i := fun i => by linarith [hb i]
  have hk : 0 < 2 * a / b j := div_pos (by positivity) (hb0 j)
  have hk1 : 2 * a / b j < 1 := (div_lt_one (hb0 j)).mpr (hb j)
  have hsq : ellipsoidSlope a b x ^ 2 ≤ (2 * a / b j) ^ 2 := by
    rw [ellipsoidSlope_sq]
    calc
      _ = ∑ i : Fin 3, (2 * a / b i) ^ 2 * (x i / b i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i : Fin 3, (2 * a / b j) ^ 2 * (x i / b i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply (sq_le_sq₀ (div_nonneg (by positivity) (hb0 i).le) hk.le).mpr
        exact div_le_div_of_nonneg_left (by positivity) (hb0 j) (hj i)
      _ = _ := by rw [← Finset.mul_sum, hx, mul_one]
  have hn : 0 ≤ ellipsoidSlope a b x := norm_nonneg _
  nlinarith

/-- Inward Euclidean unit normal; the outward normal is its negative. -/
def ellipsoidInward (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) : JointSpace :=
  (ellipsoidSlope a b x)⁻¹ • ellipsoidGradient a b x

theorem ellipsoidInward_norm (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    ‖ellipsoidInward a b x‖ = 1 := by
  have hk := ellipsoidSlope_pos a b ha hb x hx
  change ‖(ellipsoidSlope a b x)⁻¹ • ellipsoidGradient a b x‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk]
  exact inv_mul_cancel₀ hk.ne'

/-- Explicit outward unit normal, opposite to the increasing-height direction. -/
def ellipsoidOutward (a : ℝ) (b : Fin 3 → ℝ) (x : JointSpace) : JointSpace :=
  -ellipsoidInward a b x

theorem ellipsoidOutward_norm (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    ‖ellipsoidOutward a b x‖ = 1 := by
  rw [ellipsoidOutward, norm_neg, ellipsoidInward_norm a b ha hb x hx]

/-- The differential in the inward normal direction is strictly positive.
Consequently `(−k,n)` is tangent to the face `t = −h(x)`. -/
theorem ellipsoid_differential_inward (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    fderiv ℝ (fun y : JointSpace => ellipsoidProfile a b y) x (ellipsoidInward a b x) =
      ellipsoidSlope a b x := by
  rw [(hasGradientAt_ellipsoidProfile a b x).hasFDerivAt.fderiv]
  simp only [InnerProductSpace.toDual_apply, ellipsoidInward, inner_smul_right,
    real_inner_self_eq_norm_sq]
  change (ellipsoidSlope a b x)⁻¹ * ellipsoidSlope a b x ^ 2 = _
  field_simp [(ellipsoidSlope_pos a b ha hb x hx).ne']
  ring

/-- Regular level: the actual Fréchet differential is nonzero on the joint. -/
theorem ellipsoid_joint_regular (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    fderiv ℝ (fun y : JointSpace => ellipsoidProfile a b y) x ≠ 0 := by
  intro h
  have he := ellipsoid_differential_inward a b ha hb x hx
  rw [h, ContinuousLinearMap.zero_apply] at he
  exact (ellipsoidSlope_pos a b ha hb x hx).ne' he.symm

/-- Outward motion decreases height, with the same strictly positive magnitude. -/
theorem ellipsoid_differential_outward (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    fderiv ℝ (fun y : JointSpace => ellipsoidProfile a b y) x (ellipsoidOutward a b x) =
      -ellipsoidSlope a b x := by
  rw [ellipsoidOutward, map_neg, ellipsoid_differential_inward a b ha hb x hx]

end BoundaryDraft
