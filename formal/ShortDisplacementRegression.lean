import BoundaryDraft.ShortDisplacement
import BoundaryDraft.TwoFaceExamples

/-! Independent exact-identity regressions; no curved-face limit is asserted. -/

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace ShortDisplacementRegression
open BoundaryDraft

-- Expanded original point/pair normalization, not a shorthand limit goal.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    continuumMean ρ (twoFaceRegion h f) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        (volume.real (twoFaceRegion h f) - ρ * ∫ z in
          {z | z ∈ causalFuture 0 ∧ z 0 + spatialDistance 0 (spatialPart z) < δ},
          bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
            translatedOverlap (twoFaceRegion h f) z) -
      (4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ σ : ℝ,
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) * longOverlapDensity (twoFaceRegion h f) δ σ := by
  simpa only [shortContinuumMean, shortFuture_eq] using
    hf.continuumMean_eq_short_sub_density hδ ρ

-- Cutoff equality, including null pairs, is never in both domains.
example (δ : ℝ) (z : Spacetime) (hz : z ∈ causalFuture 0)
    (he : z 0 + spatialDistance 0 (spatialPart z) = δ) :
    z ∈ longFuture δ ∧ z ∉ shortFuture δ := by
  constructor
  · exact ⟨hz, he.ge⟩
  · rw [shortFuture_eq]
    simp only [mem_setOf_eq, he, lt_self_iff_false, and_false, not_false_eq_true]

-- All original planar hypotheses, not a stronger class.
example {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    continuumMean ρ (graphCapRegion h) = shortContinuumMean ρ δ (graphCapRegion h) -
      (4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ σ : ℝ,
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) * longOverlapDensity (graphCapRegion h) δ σ := by
  simpa only [twoFaceRegion_planar] using hh.twoFace_planar.continuumMean_eq_short_sub_density hδ ρ

-- Two completely overlapping, nonzero weights: partition sources, not partners.
example {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M) (ρ : ℝ) :
    continuumMean ρ M = ∑ _i : Fin 2, weightedContinuumMean ρ M (fun _ => (1 : ℝ)/2) := by
  apply continuumMean_eq_sum_source_weights Finset.univ hm hb ρ
    (fun _i : Fin 2 => fun _ => (1 : ℝ)/2) (fun _ => continuous_const)
  intro x _
  norm_num [Fin.sum_univ_two]

-- A negative source weight and its complement are retained, with all partners.
example {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M) (ρ : ℝ) :
    weightedContinuumMean ρ M (fun _ => (-1 : ℝ)) =
      continuumMean ρ M - weightedContinuumMean ρ M (fun _ => (2 : ℝ)) := by
  convert weightedContinuumMean_complement hm hb ρ
    (w := fun _ => (-1 : ℝ)) continuous_const using 1
  norm_num

end ShortDisplacementRegression
