import BoundaryDraft.ShortDisplacement
import BoundaryDraft.TwoFaceLongNull
import BoundaryDraft.TwoFaceSurface
import BoundaryDraft.GraphLimit

/-!
# Fixed-cutoff assembly interface

Unconditional asymptotic equivalences for the unchanged two-face class. The
long term is discharged by geometry, not supplied by a caller. These results
are NOT a proof of `TwoFaceLimitGoal`: the general short-limit argument remains
a conventional proof in `notes/curved-face-stability.md`. In particular no
short limit is inserted into admissibility or silently asserted here.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft
namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- At each fixed positive cutoff the actual full-minus-short action vanishes.
This retains the signed long contribution, including both density factors. -/
theorem tendsto_continuumMean_sub_short {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f) -
      shortContinuumMean ρ δ (twoFaceRegion h f)) atTop (𝓝 0) := by
  apply (hf.tendsto_normalized_longOverlap hδ).congr'
  filter_upwards with ρ
  rw [continuumMean_eq_short_sub_long hf.measurableSet_region hf.isBounded_region]
  ring

/-- The same target at one fixed cutoff is necessary and sufficient. Neither
side is assumed proved for a general curved future face. -/
theorem tendsto_continuumMean_iff_short {δ L : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop (𝓝 L) ↔
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop (𝓝 L) := by
  have hd := hf.tendsto_continuumMean_sub_short hδ
  constructor
  · intro hc
    have ht := hc.sub hd
    simpa only [sub_zero, sub_sub_cancel] using ht
  · intro hs
    have ht := hd.add hs
    simpa only [zero_add, sub_add_cancel] using ht

/-- Cutoff independence is an asymptotic difference, not uniformity in cutoff
and not a limit for a density-dependent cutoff. -/
theorem tendsto_short_sub_short {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f) -
      shortContinuumMean ρ ε (twoFaceRegion h f)) atTop (𝓝 0) := by
  have ht := (hf.tendsto_continuumMean_sub_short hε).sub
    (hf.tendsto_continuumMean_sub_short hδ)
  simp only [sub_self] at ht
  apply ht.congr'
  filter_upwards with ρ
  ring

/-- Reuse the positive-density expectation bridge, not a random-convergence
assumption. This transfers any deterministic limit only after it is proved. -/
theorem tendsto_expectedBDGAction_iff {L : ℝ} :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop (𝓝 L) ↔
      Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop (𝓝 L) := by
  have he : (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) =ᶠ[atTop]
      (fun ρ => continuumMean ρ (twoFaceRegion h f)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact hf.boundedCausalRegion.expectedBDGAction_eq hρ
  exact tendsto_congr' he

end AdmissibleTwoFace

/-- This is a checked reduction of the unchanged open Lean goal, NOT its
proof. Existence of ONE positive fixed cutoff suffices; no shrinking cutoff
or uniform long-null bound is needed. -/
theorem twoFaceLimitGoal_iff_exists_short_limit :
    TwoFaceLimitGoal ↔ ∀ h f, AdmissibleTwoFace h f → ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
        (𝓝 (twoFaceBoundaryIntegral h f)) := by
  constructor
  · intro hlimit h f hf
    exact ⟨1, zero_lt_one, (hf.tendsto_continuumMean_iff_short zero_lt_one).mp
      (hlimit h f hf)⟩
  · intro hshort h f hf
    obtain ⟨δ, hδ, hs⟩ := hshort h f hf
    exact (hf.tendsto_continuumMean_iff_short hδ).mpr hs

/-- Equivalence of the two unchanged goals, not a proof of either. -/
theorem twoFaceExpectedLimitGoal_iff_limit :
    TwoFaceExpectedLimitGoal ↔ TwoFaceLimitGoal := by
  constructor <;> intro hl h f hf
  · exact hf.tendsto_expectedBDGAction_iff.mp (hl h f hf)
  · exact hf.tendsto_expectedBDGAction_iff.mpr (hl h f hf)

/-- An unconditional calibration from the original planar theorem, with its
original admissibility hypotheses (including interior critical points). -/
theorem AdmissibleGraphCap.shortContinuumMean_limit {h : Spatial → ℝ}
    (hh : AdmissibleGraphCap h) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (graphCapRegion h)) atTop
      (𝓝 (graphBoundaryIntegral h)) := by
  have ht := (hh.twoFace_planar.tendsto_continuumMean_iff_short hδ).mp
    (by simpa only [twoFaceRegion_planar] using hh.graphCapLimit)
  simpa only [twoFaceRegion_planar] using ht

end BoundaryDraft
