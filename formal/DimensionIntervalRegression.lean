import BoundaryDraft.DimensionIntervalCompatibility

/-! Independent contracts and degeneracy/calibration checks for issue #91. -/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft

-- Every physical integer dimension, not just a finite calibration table.
example (n : ℕ) (hn : 0 < n) (x y : ℝ × EuclideanSpace ℝ (Fin n))
    (hxy : ‖y.2 - x.2‖ ≤ y.1 - x.1) :
    volume {z : ℝ × EuclideanSpace ℝ (Fin n) |
      ‖z.2 - x.2‖ ≤ z.1 - x.1 ∧ ‖y.2 - z.2‖ ≤ y.1 - z.1} =
      ENNReal.ofReal (dimensionSphereArea (n + 1) /
        ((2 : ℝ) ^ n * (n + 1) * n) *
          ((y.1 - x.1) ^ 2 - ‖y.2 - x.2‖ ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
  have h := volume_dimensionCausalInterval hn x y hxy
  rw [dimensionIntervalCoefficient_eq_sphere (n + 1) (by omega)] at h
  simpa only [dimensionCausalInterval, dimensionCausalFuture, dimensionIntervalSq,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

example (n : ℕ) : MeasurableSet
    {p : ((DimensionSpacetime n × DimensionSpacetime n) × DimensionSpacetime n) |
      ‖p.2.2 - p.1.1.2‖ ≤ p.2.1 - p.1.1.1 ∧
      ‖p.1.2.2 - p.2.2‖ ≤ p.1.2.1 - p.2.1} :=
  measurableSet_dimensionCausalInterval_joint

example (n : ℕ) (M : Set (DimensionSpacetime n)) (hM : MeasurableSet M) :
    Measurable (fun p : DimensionSpacetime n × DimensionSpacetime n =>
      volume (({z | ‖z.2 - p.1.2‖ ≤ z.1 - p.1.1 ∧ ‖p.2.2 - z.2‖ ≤ p.2.1 - z.1} \
        {p.1, p.2}) ∩ M)) :=
  measurable_dimensionRestrictedIntervalVolume hM

example (n : ℕ) (hn : 0 < n) (M : Set (DimensionSpacetime n))
    (hM : ∀ x ∈ M, ∀ y ∈ M, dimensionCausalInterval x y ⊆ M)
    (x y : DimensionSpacetime n) (hx : x ∈ M) (hy : y ∈ M)
    (hxy : y ∈ dimensionCausalFuture x) :
    volume (dimensionCausalIntervalInterior x y ∩ M) =
      ENNReal.ofReal (dimensionIntervalCoefficient (n + 1) *
        dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2)) :=
  dimensionRestrictedIntervalVolume_eq_properTime hn hM hx hy hxy

-- A non-convex region with timelike endpoints has restricted volume zero,
-- whereas its ambient interval has volume two. Convexity cannot be omitted.
example : dimensionRestrictedIntervalVolume ({0, (2, 0)} : Set (DimensionSpacetime 1))
    0 (2, 0) = 0 := by
  have he : dimensionCausalIntervalInterior (0 : DimensionSpacetime 1) (2, 0) ∩ {0, (2, 0)} = ∅ := by
    ext z
    simp [dimensionCausalIntervalInterior]
  rw [dimensionRestrictedIntervalVolume, he, measure_empty]

example : volume (dimensionCausalInterval (0 : DimensionSpacetime 1) (2, 0)) = 2 := by
  rw [volume_dimensionStandardInterval 1 (by omega) 2 (by norm_num), dimensionIntervalCoefficient_two]
  norm_num

-- Rest-frame calibration in dimensions 2, 3, 4 at a non-unit duration.
example : volume (dimensionCausalInterval (0 : DimensionSpacetime 1) (3, 0)) =
    ENNReal.ofReal (9 / 2 : ℝ) := by
  rw [volume_dimensionStandardInterval 1 (by omega) 3 (by norm_num), dimensionIntervalCoefficient_two]
  norm_num

example : volume (dimensionCausalInterval (0 : DimensionSpacetime 2) (3, 0)) =
    ENNReal.ofReal (9 * Real.pi / 4) := by
  rw [volume_dimensionStandardInterval 2 (by omega) 3 (by norm_num), dimensionIntervalCoefficient_three]
  congr 1
  norm_num
  ring

example : volume (dimensionCausalInterval (0 : DimensionSpacetime 3) (3, 0)) =
    ENNReal.ofReal (27 * Real.pi / 8) := by
  rw [volume_dimensionStandardInterval 3 (by omega) 3 (by norm_num), dimensionIntervalCoefficient_four]
  congr 1
  norm_num
  ring

private def line (r : ℝ) : DimensionSpatial 1 := (WithLp.equiv 2 _).symm (fun _ => r)

private theorem norm_line (r : ℝ) : ‖line r‖ = |r| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  simp [line, PiLp.norm_sq_eq_of_L2]

-- A genuine null intermediate point is in the exclusive order interval.
-- It is not chronological, despite the interval's zero ambient volume.
example : (1, line 1) ∈ dimensionCausalIntervalInterior (0 : DimensionSpacetime 1) (2, line 2) ∧
    (1, line 1) ∉ dimensionChronologicalFuture (0 : DimensionSpacetime 1) := by
  have hsub : line 2 - line 1 = line 1 := by ext i; norm_num [line]
  norm_num [dimensionCausalIntervalInterior, dimensionCausalInterval, dimensionCausalFuture,
    dimensionChronologicalFuture, norm_line, hsub]

example : volume (dimensionCausalInterval (0 : DimensionSpacetime 1) (2, line 2)) = 0 := by
  apply volume_dimensionCausalInterval_null (by omega)
  norm_num [dimensionIntervalSq, norm_line]

example (n : ℕ) (hn : 0 < n) (x : DimensionSpacetime n) :
    volume (dimensionCausalInterval x x) = 0 := by
  apply volume_dimensionCausalInterval_null hn
  simp [dimensionIntervalSq]

example (n : ℕ) : volume {p : DimensionSpacetime n × DimensionSpacetime n | p.1 = p.2} = 0 :=
  volume_dimensionDiagonal

-- A translated, non-rest timelike interval: proper duration four, volume eight.
example (x : DimensionSpacetime 1) :
    volume (dimensionCausalInterval x (x + (5, line 3))) = 8 := by
  have hc : x + (5, line 3) ∈ dimensionCausalFuture x := by
    norm_num [dimensionCausalFuture, norm_line]
  rw [volume_dimensionCausalInterval_two x _ hc]
  norm_num [dimensionIntervalSq, norm_line]

-- The rest-frame witness has no measure-preservation or volume hypotheses.
example : ∃ F : DimensionPoincareEquiv 1, F.translation = 0 ∧ F (4, 0) = (5, line 3) := by
  apply exists_dimensionRestFrame (5, line 3) 4 (by norm_num) (by norm_num)
  norm_num [dimensionMinkowski_apply, line]

-- Exact coordinate measure and action conversion into the unchanged 4D APIs.
example (x y : DimensionSpacetime 3) :
    volume (causalIntervalInterior (dimensionSpacetimeCoordinates 3 x)
      (dimensionSpacetimeCoordinates 3 y)) = volume (dimensionCausalIntervalInterior x y) := by
  rw [← dimensionSpacetimeCoordinates_intervalInterior, dimensionSpacetimeCoordinates_volume_image]

example (ρ : ℝ) (M : Set (DimensionSpacetime 3)) :
    dimensionWeightedAction 3 (4 / Real.sqrt 6) (4 / Real.sqrt 6) (Real.pi / 24) ρ M (fun _ => 1) =
      continuumMean ρ (dimensionSpacetimeCoordinates 3 '' M) := by
  simpa only [dimensionPointCoefficient_four, dimensionPairCoefficient_four,
    dimensionIntervalCoefficient_four] using dimensionWeightedAction_four_eq_continuumMean ρ M

end BoundaryDraft
