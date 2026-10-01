import BoundaryDraft.ConformalAction
import BoundaryDraft.GraphExamples

/-!
# A nonconstant controlled conformal example

Omega(t,x) = 1 + t^2 is smooth and positive. On a fixed time slab it has
explicit bounds 1 and 1 + T^2. The example uses an original admissible planar
member of the two-face class; the spacetime metric, not just a face, is curved.
The independent Christoffel/Ricci calculation in `conformal_geometry.py`
gives scalar curvature -12/(1+t^2)^3 in the convention documented there.
This module checks admissibility and nonconstancy, not a curvature formalism.
-/

open Set
noncomputable section
namespace BoundaryDraft

def quadraticConformalFactor (p : Spacetime) : ℝ := 1 + p 0 ^ 2

theorem quadraticConformalFactor_pos (p : Spacetime) : 0 < quadraticConformalFactor p := by
  unfold quadraticConformalFactor
  positivity

theorem quadraticConformalFactor_smooth : ContDiff ℝ ⊤ quadraticConformalFactor := by
  exact contDiff_const.add ((contDiff_apply ℝ ℝ (0 : Fin 4)).pow 2)

/-- Every bounded original region admits this one fixed nonconstant factor.
The chosen time slab and its upper bound do not depend on sprinkling density. -/
theorem quadraticConformalFactor_controlled {M : Set Spacetime} (hM : Bornology.IsBounded M) :
    ControlledConformalFactor quadraticConformalFactor M := by
  obtain ⟨T, hT, hb⟩ := hM.closure.exists_pos_norm_lt
  refine ⟨quadraticConformalFactor_smooth.continuous.measurable,
    {p | |p 0| < T}, isOpen_lt (by fun_prop) continuous_const, ?_,
    quadraticConformalFactor_smooth.contDiffOn, 1, 1 + T ^ 2, by norm_num, ?_⟩
  · intro p hp
    exact (show |p 0| ≤ ‖p‖ from norm_le_pi_norm p 0).trans_lt (hb p hp)
  · intro p hp
    change |p 0| < T at hp
    constructor
    · dsimp [quadraticConformalFactor]; nlinarith [sq_nonneg (p 0)]
    · dsimp [quadraticConformalFactor]
      have hs := (sq_le_sq₀ (abs_nonneg (p 0)) hT.le).mpr hp.le
      simpa only [sq_abs] using add_le_add_left hs 1

/-- Concrete nonempty original region: height 1/4 and all three axes 4. -/
theorem conformalExample_admissible :
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0) :=
  (ellipsoid_admissible (1 / 4) (fun _ => 4) (by norm_num) (fun _ => by norm_num)).twoFace_planar

theorem conformalExample_controlled :
    ControlledConformalFactor quadraticConformalFactor
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0)) :=
  quadraticConformalFactor_controlled conformalExample_admissible.boundedCausalRegion.bounded

/-- Nonconstancy occurs inside the sprinkled region, not only outside it. -/
theorem conformalExample_nonconstant :
    ∃ p q : Spacetime,
      p ∈ twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0) ∧
      q ∈ twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0) ∧
      quadraticConformalFactor p ≠ quadraticConformalFactor q := by
  refine ⟨![-1/8, 0, 0, 0], ![-1/16, 0, 0, 0], ?_, ?_, ?_⟩ <;>
    norm_num [twoFaceRegion, ellipsoidProfile, spatialPart, Fin.sum_univ_succ,
      quadraticConformalFactor, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]

/-- Exact expectation for the nonconstant pilot, at every positive density. -/
theorem conformalExample_expectation {ρ : ℝ} (hρ : 0 < ρ) :
    conformalExpectedAction quadraticConformalFactor ρ
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0)) =
    conformalAction quadraticConformalFactor ρ
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0)) :=
  conformalExample_admissible.conformal_expectedAction_eq conformalExample_controlled hρ

end BoundaryDraft
