import BoundaryDraft.TwoFaceShortLimit

/-!
# The original deterministic and expected two-face limits

The original action, region, boundary target, and `AdmissibleTwoFace` hypotheses
are unchanged. Short geometry and the fixed-cutoff long cancellation are
proved separately and assembled here. The Poisson bridge transfers the
result to expectations only; no sample-wise convergence or rate is claimed.
-/

open Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- The deterministic limit for the entire original admissible two-graph
class, including genuinely curved future faces and interior critical points. -/
theorem twoFaceLimit :
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) :=
  (hf.tendsto_continuumMean_iff_short (δ := 1) zero_lt_one).mpr
    (hf.shortContinuumMean_limit zero_lt_one)

/-- Expectation convergence of the unchanged unsmeared discrete BDG action.
The independently proved positive-density Poisson bridge is reused. -/
theorem expectedBDGAction_limit :
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) :=
  hf.tendsto_expectedBDGAction_iff.mpr hf.twoFaceLimit

end AdmissibleTwoFace

/-- Proof of the original deterministic goal, with no short-limit premise. -/
theorem twoFaceLimitGoal : TwoFaceLimitGoal := fun _ _ hf => hf.twoFaceLimit

/-- Proof of the original expectation-only goal, not a sample-wise theorem. -/
theorem twoFaceExpectedLimitGoal : TwoFaceExpectedLimitGoal := fun _ _ hf => hf.expectedBDGAction_limit

end BoundaryDraft
