import BoundaryDraft.Pilot3ShortLimit
import BoundaryDraft.Pilot3LongNull

/-!
# Full deterministic and expected limits for exactly SmoothPilot3

The actual short producer supplies one fixed positive cutoff. The actual long
producer applies at that same cutoff, and the exact signed action partition
then proves the unchanged deterministic goal. Only afterwards is the separate
positive-density Poisson identity used. No planar-base theorem, analytic
admissibility field, shrinking cutoff or sample-wise limit is introduced.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

/-- The complete action differs from its short part by a vanishing signed
long contribution at every fixed positive cutoff. -/
theorem tendsto_action_sub_short {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => pilot3Action ρ h f - pilot3ShortAction ρ δ h f)
      atTop (𝓝 0) := by
  apply (hf.tendsto_longAction hδ).congr'
  filter_upwards with ρ
  rw [hf.action_eq_short_add_long ρ δ, add_sub_cancel_left]

/-- Fixed-cutoff equivalence from the actual geometric long theorem, not a
hypothesis on an abstract density. -/
theorem tendsto_action_iff_short {δ L : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => pilot3Action ρ h f) atTop (𝓝 L) ↔
      Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop (𝓝 L) := by
  have hd := hf.tendsto_action_sub_short hδ
  constructor
  · intro ha
    simpa only [sub_zero, sub_sub_cancel] using ha.sub hd
  · intro hs
    simpa only [zero_add, sub_add_cancel] using hd.add hs

/-- Unconditional full deterministic limit on the original smooth 3D pilot.
The endpoint of the short producer's positive bound is itself an allowed
fixed cutoff. No limit or uniformity in the cutoff is needed. -/
theorem action_limit :
    Tendsto (fun ρ => pilot3Action ρ h f) atTop (𝓝 (pilot3BoundaryIntegral h f)) := by
  obtain ⟨δ, hδ, hs⟩ := hf.exists_shortAction_limit
  exact (hf.tendsto_action_iff_short hδ).mpr (hs δ hδ le_rfl)

/-- After full assembly, every fixed positive cutoff has the same short
limit, even outside the local Taylor radius used to prove the theorem. -/
theorem shortAction_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop
      (𝓝 (pilot3BoundaryIntegral h f)) :=
  (hf.tendsto_action_iff_short hδ).mp hf.action_limit

/-- Two arbitrary fixed positive cutoffs give asymptotically equal short
parts. This is not a density-dependent or shrinking-cutoff statement. -/
theorem tendsto_short_sub_short {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Tendsto (fun ρ => pilot3ShortAction ρ δ h f - pilot3ShortAction ρ ε h f)
      atTop (𝓝 0) := by
  simpa only [sub_self] using (hf.shortAction_limit hδ).sub (hf.shortAction_limit hε)

/-- Expected limit under the independently constructed finite Poisson law.
The positive-density identity is applied only after the full deterministic
limit; no assertion about individual sprinklings follows. -/
theorem expectedAction_limit :
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region h f)) atTop
      (𝓝 (pilot3BoundaryIntegral h f)) := by
  apply hf.action_limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hf.expectedAction_eq hρ).symm

/-- The same deterministic limit on the actual intrinsic spacetime joint.
Its measure/angle identification is the independent geometry theorem. -/
theorem action_limit_joint :
    Tendsto (fun ρ => pilot3Action ρ h f) atTop
      (𝓝 (∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f)) := by
  simpa only [hf.boundaryIntegral_eq_joint] using hf.action_limit

/-- The expectation has the same independently defined intrinsic joint target. -/
theorem expectedAction_limit_joint :
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region h f)) atTop
      (𝓝 (∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f)) := by
  simpa only [hf.boundaryIntegral_eq_joint] using hf.expectedAction_limit

end SmoothPilot3

/-- Proof of the original deterministic goal, without changing its contract. -/
theorem pilot3DeterministicGoal : Pilot3DeterministicGoal :=
  fun _ _ hf => hf.action_limit

/-- Proof of the original expectation goal, not sample-wise convergence. -/
theorem pilot3ExpectedGoal : Pilot3ExpectedGoal :=
  fun _ _ hf => hf.expectedAction_limit

end BoundaryDraft
