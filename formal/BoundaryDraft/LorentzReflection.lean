import BoundaryDraft.CausalInterval
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Audited Lorentz reflection for timelike interval reduction

A rank-one Lorentzian Householder reflection maps the standard time axis to
an arbitrary future timelike displacement.  Its determinant is computed by
the matrix determinant lemma, so preservation of four-dimensional Lebesgue
measure is a theorem rather than an assumed Lorentz-invariance principle.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

/-- Minkowski bilinear form with signature `(+---)`. -/
def minkowskiInner (x y : Spacetime) : ℝ :=
  x 0 * y 0 - ∑ i : Fin 3, x i.succ * y i.succ

/-- Coordinate covector associated to the Minkowski bilinear form. -/
def minkowskiCovector (x : Spacetime) : Spacetime :=
  Fin.cons (x 0) (fun i => -x i.succ)

@[simp] theorem minkowskiCovector_zero (x : Spacetime) :
    minkowskiCovector x 0 = x 0 := by simp [minkowskiCovector]

@[simp] theorem minkowskiCovector_succ (x : Spacetime) (i : Fin 3) :
    minkowskiCovector x i.succ = -x i.succ := by simp [minkowskiCovector]

theorem minkowskiInner_eq_dotProduct (x y : Spacetime) :
    minkowskiInner x y = minkowskiCovector x ⬝ᵥ y := by
  simp [minkowskiInner, dotProduct, Fin.sum_univ_succ]
  ring

theorem minkowskiInner_symm (x y : Spacetime) :
    minkowskiInner x y = minkowskiInner y x := by
  unfold minkowskiInner
  rw [mul_comm (x 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem minkowskiInner_add_left (x y z : Spacetime) :
    minkowskiInner (x + y) z = minkowskiInner x z + minkowskiInner y z := by
  unfold minkowskiInner
  simp only [Pi.add_apply]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

theorem minkowskiInner_add_right (x y z : Spacetime) :
    minkowskiInner x (y + z) = minkowskiInner x y + minkowskiInner x z := by
  rw [minkowskiInner_symm, minkowskiInner_add_left]
  rw [minkowskiInner_symm y x, minkowskiInner_symm z x]

theorem minkowskiInner_smul_left (c : ℝ) (x y : Spacetime) :
    minkowskiInner (c • x) y = c * minkowskiInner x y := by
  unfold minkowskiInner
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem minkowskiInner_smul_right (c : ℝ) (x y : Spacetime) :
    minkowskiInner x (c • y) = c * minkowskiInner x y := by
  rw [minkowskiInner_symm, minkowskiInner_smul_left, minkowskiInner_symm]

theorem minkowskiInner_neg_left (x y : Spacetime) :
    minkowskiInner (-x) y = -minkowskiInner x y := by
  simpa only [neg_one_smul, neg_one_mul] using minkowskiInner_smul_left (-1) x y

theorem minkowskiInner_sub_left (x y z : Spacetime) :
    minkowskiInner (x - y) z = minkowskiInner x z - minkowskiInner y z := by
  rw [sub_eq_add_neg, minkowskiInner_add_left, minkowskiInner_neg_left, sub_eq_add_neg]

 theorem minkowskiInner_sub_right (x y z : Spacetime) :
    minkowskiInner x (y - z) = minkowskiInner x y - minkowskiInner x z := by
  rw [minkowskiInner_symm, minkowskiInner_sub_left,
    minkowskiInner_symm y x, minkowskiInner_symm z x]

theorem minkowskiInner_self (x : Spacetime) :
    minkowskiInner x x = intervalSq 0 x := by
  simp [minkowskiInner, intervalSq, spatialSeparationSq]
  ring

theorem intervalSq_eq_minkowski_sub (x y : Spacetime) :
    intervalSq x y = minkowskiInner (y - x) (y - x) := by
  unfold intervalSq spatialSeparationSq minkowskiInner
  simp only [Pi.sub_apply]
  ring

private def reflectionRow (n : Spacetime) : Spacetime :=
  fun j => -(2 / minkowskiInner n n) * minkowskiCovector n j

/-- Matrix of the Lorentzian Householder reflection in the hyperplane
orthogonal to a non-null vector `n`. -/
def lorentzReflectionMatrix (n : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  1 + Matrix.replicateCol (Fin 1) n *
    Matrix.replicateRow (Fin 1) (reflectionRow n)

/-- The rank-one determinant is exactly `-1`. -/
theorem det_lorentzReflectionMatrix (n : Spacetime)
    (hn : minkowskiInner n n ≠ 0) :
    Matrix.det (lorentzReflectionMatrix n) = -1 := by
  rw [lorentzReflectionMatrix,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : reflectionRow n ⬝ᵥ n = -2 := by
    unfold reflectionRow
    simp only [dotProduct]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum,
      show (∑ i, minkowskiCovector n i * n i) = minkowskiInner n n by
        exact (minkowskiInner_eq_dotProduct n n).symm]
    field_simp
  rw [hdot]
  ring

/-- Linear reflection map. -/
def lorentzReflection (n : Spacetime) : Spacetime →ₗ[ℝ] Spacetime :=
  Matrix.toLin' (lorentzReflectionMatrix n)

/-- Explicit reflection formula, including its normalization. -/
theorem lorentzReflection_apply (n y : Spacetime) :
    lorentzReflection n y =
      y - (2 * minkowskiInner y n / minkowskiInner n n) • n := by
  ext i
  simp only [lorentzReflection, lorentzReflectionMatrix, Matrix.toLin'_apply,
    Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  rw [show (Matrix.replicateCol (Fin 1) n *
      Matrix.replicateRow (Fin 1) (reflectionRow n)).mulVec y i =
      n i * (reflectionRow n ⬝ᵥ y) by
        simp [Matrix.mulVec, Matrix.mul_apply, dotProduct,
          Matrix.replicateCol_apply, Matrix.replicateRow_apply,
          Fin.sum_univ_succ]
        ring]
  rw [show reflectionRow n ⬝ᵥ y =
      -(2 / minkowskiInner n n) * minkowskiInner y n by
        unfold reflectionRow
        simp only [dotProduct]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum,
          show (∑ j, minkowskiCovector n j * y j) = minkowskiInner n y by
            exact (minkowskiInner_eq_dotProduct n y).symm,
          minkowskiInner_symm n y]]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The reflection preserves the full bilinear form, not merely the norm. -/
theorem lorentzReflection_minkowskiInner (n y z : Spacetime)
    (hn : minkowskiInner n n ≠ 0) :
    minkowskiInner (lorentzReflection n y) (lorentzReflection n z) =
      minkowskiInner y z := by
  rw [lorentzReflection_apply, lorentzReflection_apply,
    minkowskiInner_sub_left, minkowskiInner_sub_right,
    minkowskiInner_smul_left, minkowskiInner_smul_right,
    minkowskiInner_sub_right, minkowskiInner_smul_right,
    minkowskiInner_symm n z]
  field_simp
  ring

/-- Applying the reflection twice is the identity. -/
theorem lorentzReflection_involutive (n y : Spacetime)
    (hn : minkowskiInner n n ≠ 0) :
    lorentzReflection n (lorentzReflection n y) = y := by
  rw [lorentzReflection_apply, lorentzReflection_apply,
    minkowskiInner_sub_left, minkowskiInner_smul_left]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The reflection is injective, as witnessed by its checked involution. -/
theorem lorentzReflection_injective (n : Spacetime)
    (hn : minkowskiInner n n ≠ 0) : Function.Injective (lorentzReflection n) := by
  intro x y h
  have := congrArg (lorentzReflection n) h
  simpa only [lorentzReflection_involutive n x hn,
    lorentzReflection_involutive n y hn] using this

/-- Its determinant computation gives preservation of product Lebesgue measure. -/
theorem lorentzReflection_measurePreserving (n : Spacetime)
    (hn : minkowskiInner n n ≠ 0) :
    MeasurePreserving (lorentzReflection n) := by
  refine ⟨(lorentzReflection n).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [lorentzReflection, Real.map_matrix_volume_pi_eq_smul_volume_pi
    (by rw [det_lorentzReflectionMatrix n hn]; norm_num),
    det_lorentzReflectionMatrix n hn]
  simp

end BoundaryDraft
