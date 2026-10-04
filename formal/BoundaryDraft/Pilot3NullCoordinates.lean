import BoundaryDraft.Pilot3ActionSplit
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Three-dimensional displacement coordinates

The angular measure is the ordinary full-circle polar measure, not a probability
measure. The proper-time-square Jacobian uses spatial dimension TWO. No 4D
radial coefficient or analytic response is imported into these definitions.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

abbrev Pilot3Circle := Metric.sphere (0 : Pilot3Space) 1

def pilot3CircleMeasure : Measure Pilot3Circle := (volume : Measure Pilot3Space).toSphere

instance : IsFiniteMeasure pilot3CircleMeasure :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure Pilot3Space).toSphere)

theorem pilot3Circle_mass : pilot3CircleMeasure.real univ = 2 * Real.pi := by
  rw [pilot3CircleMeasure, Measure.toSphere_real_apply_univ]
  norm_num [Measure.real, EuclideanSpace.volume_ball_fin_two, Real.pi_pos.le]

/-- Future displacement in null coordinates; the spatial factor is Euclidean. -/
def pilot3NullPoint (ω : Pilot3Circle) (v σ : ℝ) : Pilot3Spacetime :=
  ((v + σ / v) / 2, ((v - σ / v) / 2) • ω.val)

/-- The 3D radial/polar Jacobian, before full-circle integration. -/
def pilot3NullJacobian (v σ : ℝ) : ℝ := (1 - σ / v ^ 2) / 4

theorem pilot3NullJacobian_eq {v : ℝ} (hv : v ≠ 0) (σ : ℝ) :
    pilot3NullJacobian v σ = (v - σ / v) / (4 * v) := by
  unfold pilot3NullJacobian
  field_simp
  ring

theorem pilot3NullJacobian_bounds {v σ : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    0 ≤ pilot3NullJacobian v σ ∧ pilot3NullJacobian v σ ≤ 1 / 4 := by
  have hq : 0 ≤ σ / v ^ 2 := div_nonneg hσ.1 (sq_nonneg _)
  have hq1 : σ / v ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hv)).mpr hσ.2
  unfold pilot3NullJacobian
  constructor <;> linarith

theorem pilot3NullPoint_norm_le (ω : Pilot3Circle) {v σ : ℝ}
    (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) : ‖pilot3NullPoint ω v σ‖ ≤ v := by
  have hq : 0 ≤ σ / v := div_nonneg hσ.1 hv.le
  have hqv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith only [hσ.2])
  simp only [pilot3NullPoint, Prod.norm_def, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, max_le_iff]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem pilot3NullPoint_causal (ω : Pilot3Circle) {v σ : ℝ}
    (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖(pilot3NullPoint ω v σ).2‖ ≤ (pilot3NullPoint ω v σ).1 := by
  have hq : 0 ≤ σ / v := div_nonneg hσ.1 hv.le
  have hqv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith only [hσ.2])
  simp only [pilot3NullPoint, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one]
  rw [abs_of_nonneg (by linarith : 0 ≤ (v - σ / v) / 2)]
  linarith

end BoundaryDraft
