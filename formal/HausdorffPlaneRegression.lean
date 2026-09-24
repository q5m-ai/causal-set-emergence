import BoundaryDraft.HausdorffPlane

/-!
# Euclidean planar normalization regression contracts

These statements have no measurability or finiteness hypotheses. The norm
calculation distinguishes the Euclidean plane from the coordinate supremum norm.
-/

open BoundaryDraft MeasureTheory Set Metric
open scoped ENNReal

-- The two independently proved inequalities combine on every set.
example (s : Set (EuclideanSpace ℝ (Fin 2))) :
    ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure SurfacePlane) s = volume s :=
  le_antisymm (normalized_hausdorff_plane_le_volume s) (volume_le_normalized_hausdorff_plane s)

-- Equality of measures, not just equality on compact or measurable sets.
example : ENNReal.ofReal (Real.pi / 4) •
    (μH[2] : Measure (EuclideanSpace ℝ (Fin 2))) = volume :=
  normalized_hausdorff_plane_eq_volume

-- The closed Euclidean unit disk has normalized measure pi.
example : ENNReal.ofReal (Real.pi / 4) *
    (μH[2] : Measure SurfacePlane) (closedBall 0 1) = ENNReal.ofReal Real.pi := by
  rw [normalized_hausdorff_plane_eq_volume_apply, EuclideanSpace.volume_closedBall_fin_two]
  norm_num

-- In the supremum norm this squared norm would instead be one.
example : ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![1, 1] : SurfacePlane)‖ ^ 2 = 2 := by
  norm_num [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

-- Infinite measure is included in the final equality.
example : ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure SurfacePlane) univ = ∞ := by
  rw [normalized_hausdorff_plane_eq_volume_apply]
  exact measure_univ_of_isAddLeftInvariant volume

-- The arbitrary-set diameter bound is available independently of normalization.
example (s : Set (EuclideanSpace ℝ (Fin 2))) :
    volume s ≤ ENNReal.ofReal (Real.pi / 4) * EMetric.diam s ^ (2 : ℝ) :=
  volume_le_pi_div_four_mul_ediam_sq s
