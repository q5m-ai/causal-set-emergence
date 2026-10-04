import BoundaryDraft.Pilot3ShortLimit
import BoundaryDraft.Pilot3LongNull
import BoundaryDraft.Pilot3Annulus

/-! Shared-interface regression for both actual producers. A single fixed
cutoff satisfies both contracts. No global or expectation assembly theorem is
introduced here; that remains issue #80's obligation. -/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

example (ρ δ : ℝ) (h f : Pilot3Space → ℝ) :
    pilot3LongAction ρ δ h f = -pilot3LongPairAction ρ δ h f :=
  pilot3LongAction_eq_neg_pair ρ δ h f

example (v σ : ℝ) : pilot3ShortNullJacobian v σ = pilot3NullJacobian σ v := rfl

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (ρ δ : ℝ) :
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f + pilot3LongAction ρ δ h f ∧
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f - pilot3LongPairAction ρ δ h f :=
  ⟨hf.action_eq_short_add_long ρ δ, hf.action_eq_short_sub_long ρ δ⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop (𝓝 (pilot3BoundaryIntegral h f)) ∧
      Tendsto (fun ρ => pilot3LongAction ρ δ h f) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hs⟩ := hf.exists_shortAction_limit
  exact ⟨δ₀, hδ₀, fun δ hδ hb => ⟨hs δ hδ hb, hf.tendsto_longAction hδ⟩⟩

-- Both canonical analytic producers apply to the entire curved annular member.
example : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => pilot3ShortAction ρ δ pilot3AnnularHeight pilot3SineFuture) atTop
      (𝓝 (pilot3BoundaryIntegral pilot3AnnularHeight pilot3SineFuture)) ∧
    Tendsto (fun ρ => pilot3LongAction ρ δ pilot3AnnularHeight pilot3SineFuture) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, hs⟩ := pilot3AnnularSine_admissible.exists_shortAction_limit
  exact ⟨δ₀, hδ₀, fun δ hδ hb =>
    ⟨hs δ hδ hb, pilot3AnnularSine_admissible.tendsto_longAction hδ⟩⟩
