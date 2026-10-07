import BoundaryDraft.TwoDShortAssembly

/-!
# Unconditional smooth flat 2D deterministic limit, then expectation transfer

The short producer selects ONE positive cutoff. The checked long theorem
works at that same cutoff. The original whole-region action is split once,
without componentwise bilocal additivity or any omitted null partner.
Expectation is transferred only AFTER the deterministic limit is proved.
Neither statement is sample-wise convergence or independent human review.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- The canonical, unchanged 2D deterministic observable converges to its
independently normal-defined canonical all-endpoint boundary integral. -/
theorem tendsto_action :
    Tendsto (fun ρ : ℝ => twoDAction ρ h f) atTop (𝓝 (twoDBoundaryIntegral h f)) := by
  obtain ⟨δ, hδ, hs⟩ := hf.exists_shortAction_limit
  have hl := hf.tendsto_longAction hδ
  have ht := hs.add hl
  simp only [add_zero] at ht
  exact ht.congr' (Eventually.of_forall fun ρ => (hf.action_eq_short_add_long ρ δ).symm)

end SmoothTwoD

/-- An unconditional proof term of the pre-existing deterministic contract. -/
theorem twoDDeterministicGoal : TwoDDeterministicGoal :=
  fun _ _ hf => hf.tendsto_action

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- Separate transfer through the independently proved Poisson-expectation
bridge. No claim of convergence for individual samples is made. -/
theorem tendsto_expectedAction :
    Tendsto (fun ρ : ℝ => dimensionExpectedAction 1 ρ (twoDRegion h f))
      atTop (𝓝 (twoDBoundaryIntegral h f)) := by
  apply hf.tendsto_action.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hf.expectedAction_eq hρ).symm

end SmoothTwoD

/-- An unconditional proof term of the separately stated expectation contract. -/
theorem twoDExpectedGoal : TwoDExpectedGoal :=
  fun _ _ hf => hf.tendsto_expectedAction

end BoundaryDraft
