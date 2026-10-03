import BoundaryDraft.IndependentShortLimit
import BoundaryDraft.IndependentFaceLongNull

/-!
# Unconditional deterministic and expected limits for exactly class E

Choose one positive cutoff from the actual short producer and use the actual
long theorem at that SAME fixed cutoff. The exact signed partition recovers
the unchanged full action and intrinsic target; no cutoff is sent to zero.
Only then is the separately proved positive-density Poisson bridge applied.
No old-class cap theorem, analytic premise, rate or sample-wise limit is used.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The enlarged deterministic contract, leaving `TwoFaceLimitGoal` unchanged. -/
def IndependentTwoFaceLimitGoal : Prop :=
  ∀ h f, AdmissibleIndependentTwoFace h f →
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f))

/-- Expectation of the original unsmeared action under its restricted Poisson
law, not convergence of individual configurations. -/
def IndependentTwoFaceExpectedLimitGoal : Prop :=
  ∀ h f, AdmissibleIndependentTwoFace h f →
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f))

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- Exact finite-density partition with the ACTUAL long density and original
signed kernel. The cutoff equality belongs to the long part; only the null
proper-time endpoint is removed in the density integral. -/
theorem continuumMean_eq_short_sub_density {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    continuumMean ρ (twoFaceRegion h f) = shortContinuumMean ρ δ (twoFaceRegion h f) -
      (4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
        longOverlapDensity (twoFaceRegion h f) δ σ *
          bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) := by
  rw [continuumMean_eq_short_sub_long hf.measurableSet_region hf.isBounded_region,
    hf.integral_longOverlap_bdg_Ioi hδ]

/-- Every fixed positive cutoff has a vanishing full-minus-short difference,
with the negative long prefactor and both density factors retained. -/
theorem tendsto_continuumMean_sub_short {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f) -
      shortContinuumMean ρ δ (twoFaceRegion h f)) atTop (𝓝 0) := by
  apply (hf.tendsto_normalized_longOverlap hδ).congr'
  filter_upwards with ρ
  rw [continuumMean_eq_short_sub_long hf.measurableSet_region hf.isBounded_region]
  ring

/-- Fixed-cutoff equivalence, derived from geometric long cancellation. -/
theorem tendsto_continuumMean_iff_short {δ L : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop (𝓝 L) ↔
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop (𝓝 L) := by
  have hd := hf.tendsto_continuumMean_sub_short hδ
  constructor
  · intro hc
    simpa only [sub_zero, sub_sub_cancel] using hc.sub hd
  · intro hs
    simpa only [zero_add, sub_add_cancel] using hd.add hs

/-- The full deterministic class-E theorem. The short producer supplies one
positive bound; its endpoint is itself an allowed fixed cutoff. The long
proof works at that very cutoff, without a limit or uniformity in cutoff. -/
theorem twoFaceLimit :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) := by
  obtain ⟨δ, hδ, hs⟩ := hf.exists_shortContinuumMean_limit
  exact (hf.tendsto_continuumMean_iff_short hδ).mpr (hs δ hδ le_rfl)

/-- After full assembly, every fixed positive cutoff has the same short limit,
not only the sufficiently small cutoffs used to prove the theorem. -/
theorem shortContinuumMean_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) :=
  (hf.tendsto_continuumMean_iff_short hδ).mp hf.twoFaceLimit

/-- Two fixed cutoffs are asymptotically equivalent. This is not a
shrinking-cutoff statement or uniform control over the cutoff. -/
theorem tendsto_short_sub_short {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f) -
      shortContinuumMean ρ ε (twoFaceRegion h f)) atTop (𝓝 0) := by
  simpa only [sub_self] using (hf.shortContinuumMean_limit hδ).sub
    (hf.shortContinuumMean_limit hε)

/-- Unconditional expected-action limit, transferred only after the
unconditional deterministic theorem. Region measurability, boundedness and
closed-interval causal convexity were derived from class E, not assumed. -/
theorem expectedBDGAction_limit :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) := by
  apply hf.twoFaceLimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hf.expectedBDGAction_eq hρ).symm

end AdmissibleIndependentTwoFace

/-- Proof of the enlarged deterministic contract, with no analytic premise. -/
theorem independentTwoFaceLimitGoal : IndependentTwoFaceLimitGoal :=
  fun _ _ hf => hf.twoFaceLimit

/-- Proof of the enlarged expectation contract, not a sample-wise claim. -/
theorem independentTwoFaceExpectedLimitGoal : IndependentTwoFaceExpectedLimitGoal :=
  fun _ _ hf => hf.expectedBDGAction_limit

end BoundaryDraft
