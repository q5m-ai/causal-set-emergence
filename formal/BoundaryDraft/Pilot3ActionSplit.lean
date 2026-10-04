import BoundaryDraft.Pilot3Displacement

/-!
# Compatibility for the exact three-dimensional action split

The merged long producer owns the canonical displacement definitions. This
module retains the short producer's positive long-pair/subtraction convention
without duplicating the action, overlap or integration declarations.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Norm form of the canonical strict short cone. -/
theorem pilot3ShortFuture_eq_norm (δ : ℝ) : pilot3ShortFuture δ =
    {z | ‖z.2‖ ≤ z.1 ∧ z.1 + ‖z.2‖ < δ} := by
  simpa only [dimensionCausalFuture, mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero] using pilot3ShortFuture_eq δ

/-- The positive signed pair contribution; the full action subtracts it. -/
def pilot3LongPairAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPairCoefficient 3 * ρ * ∫ z in pilot3LongFuture δ,
    pilot3DisplacementKernel ρ z * pilot3Overlap h f z)

/-- Exact bridge between the two existing long sign conventions. -/
theorem pilot3LongAction_eq_neg_pair (ρ δ : ℝ) (h f : Pilot3Space → ℝ) :
    pilot3LongAction ρ δ h f = -pilot3LongPairAction ρ δ h f := by
  unfold pilot3LongAction pilot3LongPairAction
  ring

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

/-- Restrict the canonical globally integrable displacement observable. -/
theorem integrableOn_overlap_weight (w : Pilot3Spacetime → ℝ) (hw : Continuous w) :
    IntegrableOn (fun z => w z * pilot3Overlap h f z) (dimensionCausalFuture 0) :=
  (hf.integrable_overlap_weight w hw).integrableOn

/-- Preserve the short producer's exact finite-density consumer contract. -/
theorem action_eq_short_sub_long (ρ δ : ℝ) :
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f - pilot3LongPairAction ρ δ h f := by
  rw [hf.action_eq_short_add_long, pilot3LongAction_eq_neg_pair, sub_eq_add_neg]

end SmoothPilot3
end BoundaryDraft
