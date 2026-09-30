import BoundaryDraft.DimensionActionTransport
import BoundaryDraft.TimelikeInterval
import BoundaryDraft.SpacetimeSprinkling

/-!
# Low-dimensional interval calibration and unchanged 4D coordinates

The coordinate equivalence preserves canonical volume; there is no implicit
Euclidean/supremum-norm measure conversion. The old four-dimensional causal
order, exclusive intervals and proper-time law are unchanged.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft

private def dimensionSpatialCoordinates (n : ℕ) : DimensionSpatial n ≃ᵐ (Fin n → ℝ) :=
  { WithLp.equiv 2 _ with
    measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin n => ℝ)).measurable
    measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin n => ℝ)).measurable }

/-- Time first, then orthonormal Euclidean spatial coordinates. -/
def dimensionSpacetimeCoordinates (n : ℕ) : DimensionSpacetime n ≃ᵐ (Fin (n + 1) → ℝ) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (dimensionSpatialCoordinates n)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm

theorem dimensionSpacetimeCoordinates_apply (n : ℕ) (x : DimensionSpacetime n) :
    dimensionSpacetimeCoordinates n x = Fin.cons x.1 (fun i => x.2 i) := by
  simp [dimensionSpacetimeCoordinates, dimensionSpatialCoordinates,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  constructor <;> rfl

/-- Product Lebesgue normalization is identical in every coordinate dimension. -/
theorem dimensionSpacetimeCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (dimensionSpacetimeCoordinates n) := by
  have hp : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (dimensionSpatialCoordinates n)) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (PiLp.volume_preserving_equiv (Fin n))
  exact ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _).comp hp

theorem dimensionSpacetimeCoordinates_volume_image (n : ℕ) (M : Set (DimensionSpacetime n)) :
    volume (dimensionSpacetimeCoordinates n '' M) = volume M := by
  have h := (dimensionSpacetimeCoordinates_measurePreserving n).measure_preimage_emb
    (dimensionSpacetimeCoordinates n).measurableEmbedding (dimensionSpacetimeCoordinates n '' M)
  rw [(dimensionSpacetimeCoordinates n).injective.preimage_image] at h
  exact h.symm

/-- The unchanged 4D squared proper time agrees pointwise, even outside the cone. -/
theorem dimensionSpacetimeCoordinates_intervalSq (x y : DimensionSpacetime 3) :
    intervalSq (dimensionSpacetimeCoordinates 3 x) (dimensionSpacetimeCoordinates 3 y) =
      dimensionIntervalSq x y := by
  simp only [dimensionSpacetimeCoordinates_apply, intervalSq, spatialSeparationSq,
    Fin.cons_zero, Fin.cons_succ, dimensionIntervalSq]
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

/-- Closed causal order, including null and diagonal pairs, agrees in old coordinates. -/
theorem dimensionSpacetimeCoordinates_causal (x y : DimensionSpacetime 3) :
    dimensionSpacetimeCoordinates 3 y ∈ causalFuture (dimensionSpacetimeCoordinates 3 x) ↔
      y ∈ dimensionCausalFuture x := by
  have hq := dimensionSpacetimeCoordinates_intervalSq x y
  have ht : (dimensionSpacetimeCoordinates 3 x) 0 = x.1 ∧
      (dimensionSpacetimeCoordinates 3 y) 0 = y.1 := by
    simp [dimensionSpacetimeCoordinates_apply]
  change (_ ≤ _ ∧ _ ≤ _) ↔ _
  rw [← sub_nonneg (b := spatialSeparationSq _ _)]
  change (_ ≤ _ ∧ 0 ≤ intervalSq _ _) ↔ _
  rw [ht.1, ht.2, hq, dimensionCausalFuture_iff_sub, dimensionCausalFuture_zero_iff,
    ← dimensionIntervalSq_eq_minkowski]
  simp only [Prod.fst_sub, sub_nonneg]

theorem dimensionSpacetimeCoordinates_interval (x y : DimensionSpacetime 3) :
    dimensionSpacetimeCoordinates 3 '' dimensionCausalInterval x y =
      causalInterval (dimensionSpacetimeCoordinates 3 x) (dimensionSpacetimeCoordinates 3 y) := by
  ext z
  obtain ⟨w, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective z
  simp only [(dimensionSpacetimeCoordinates 3).injective.mem_set_image,
    dimensionCausalInterval, causalInterval, causalPast, mem_inter_iff, mem_setOf_eq,
    dimensionSpacetimeCoordinates_causal]
  rw [dimensionSpacetimeCoordinates_causal]

theorem dimensionSpacetimeCoordinates_intervalInterior (x y : DimensionSpacetime 3) :
    dimensionSpacetimeCoordinates 3 '' dimensionCausalIntervalInterior x y =
      causalIntervalInterior (dimensionSpacetimeCoordinates 3 x) (dimensionSpacetimeCoordinates 3 y) := by
  rw [dimensionCausalIntervalInterior, Set.image_diff (dimensionSpacetimeCoordinates 3).injective,
    dimensionSpacetimeCoordinates_interval, Set.image_pair, causalIntervalInterior]

/-- Calibration at physical dimension two, with the two radial directions. -/
theorem volume_dimensionCausalInterval_two (x y : DimensionSpacetime 1)
    (hxy : y ∈ dimensionCausalFuture x) :
    volume (dimensionCausalInterval x y) = ENNReal.ofReal ((1 / 2 : ℝ) * dimensionIntervalSq x y) := by
  simpa only [dimensionIntervalCoefficient_two, Nat.reduceAdd, Nat.cast_ofNat,
    div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using
      volume_dimensionCausalInterval (by omega : 0 < 1) x y hxy

/-- Odd physical dimension retains the real `3/2` power. -/
theorem volume_dimensionCausalInterval_three (x y : DimensionSpacetime 2)
    (hxy : y ∈ dimensionCausalFuture x) :
    volume (dimensionCausalInterval x y) =
      ENNReal.ofReal ((Real.pi / 12) * dimensionIntervalSq x y ^ (3 / 2 : ℝ)) := by
  simpa only [Nat.reduceAdd, dimensionIntervalCoefficient_three, Nat.cast_ofNat] using
    volume_dimensionCausalInterval (by omega : 0 < 2) x y hxy

/-- The new all-dimension theorem recovers the unchanged 4D Alexandrov law. -/
theorem volume_dimensionCausalInterval_four (x y : DimensionSpacetime 3)
    (hxy : y ∈ dimensionCausalFuture x) :
    volume (dimensionCausalInterval x y) = ENNReal.ofReal ((Real.pi / 24) * dimensionIntervalSq x y ^ 2) := by
  simpa only [Nat.reduceAdd, dimensionIntervalCoefficient_four, Nat.cast_ofNat,
    show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two] using
      volume_dimensionCausalInterval (by omega : 0 < 3) x y hxy

/-- Measure-level recovery in the original coordinates, not merely equality of
constants or of totalized real volumes. -/
theorem volume_oldCausalInterval_eq_dimension (x y : DimensionSpacetime 3) :
    volume (causalInterval (dimensionSpacetimeCoordinates 3 x) (dimensionSpacetimeCoordinates 3 y)) =
      volume (dimensionCausalInterval x y) := by
  rw [← dimensionSpacetimeCoordinates_interval, dimensionSpacetimeCoordinates_volume_image]

/-- Signed coordinate substitution, with no numerical Jacobian guess. -/
theorem integral_dimensionSpacetimeCoordinates_image (n : ℕ) (M : Set (DimensionSpacetime n))
    (f : (Fin (n + 1) → ℝ) → ℝ) :
    (∫ y in dimensionSpacetimeCoordinates n '' M, f y) =
      ∫ x in M, f (dimensionSpacetimeCoordinates n x) :=
  (dimensionSpacetimeCoordinates_measurePreserving n).setIntegral_image_emb
    (dimensionSpacetimeCoordinates n).measurableEmbedding f M

theorem dimensionSpacetimeCoordinates_future_inter (M : Set (DimensionSpacetime 3))
    (x : DimensionSpacetime 3) :
    dimensionSpacetimeCoordinates 3 '' (M ∩ dimensionCausalFuture x) =
      dimensionSpacetimeCoordinates 3 '' M ∩ causalFuture (dimensionSpacetimeCoordinates 3 x) := by
  ext z
  obtain ⟨y, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective z
  simp only [(dimensionSpacetimeCoordinates 3).injective.mem_set_image, mem_inter_iff]
  rw [dimensionSpacetimeCoordinates_causal]

/-- Recovery of the entire unchanged finite-density 4D action, not just its
rest-frame volume or reduced kernel. -/
theorem dimensionWeightedAction_four_eq_continuumMean (ρ : ℝ) (M : Set (DimensionSpacetime 3)) :
    dimensionWeightedAction 3 (dimensionPointCoefficient 4) (dimensionPairCoefficient 4)
      (dimensionIntervalCoefficient 4) ρ M (fun _ => 1) =
        continuumMean ρ (dimensionSpacetimeCoordinates 3 '' M) := by
  have hp : ρ ^ (2 / ((3 + 1 : ℕ) : ℝ)) = Real.sqrt ρ := by
    norm_num [Real.sqrt_eq_rpow]
  unfold dimensionWeightedAction continuumMean
  rw [dimensionPointCoefficient_four, dimensionPairCoefficient_four, dimensionIntervalCoefficient_four,
    hp, integral_dimensionSpacetimeCoordinates_image, integral_dimensionSpacetimeCoordinates_image]
  simp_rw [← dimensionSpacetimeCoordinates_future_inter, integral_dimensionSpacetimeCoordinates_image,
    dimensionSpacetimeCoordinates_intervalSq]
  norm_num only [dimensionBilocalKernel, Nat.reduceAdd, Nat.cast_ofNat, dimensionKernel_four,
    show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two, one_mul]
  ring

end BoundaryDraft
