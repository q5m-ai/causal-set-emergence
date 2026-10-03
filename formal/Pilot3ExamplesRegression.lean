import BoundaryDraft.Pilot3Examples
import BoundaryDraft.Pilot3Components

/-! Concrete nonvacuity and all-component/exterior controls. The separated
maximum identities are set identities, not an additive-action assertion or a
claim that all raw maxima satisfy the smooth pilot. -/

open BoundaryDraft MeasureTheory Set
noncomputable section

example : SmoothPilot3 pilot3BallHeight pilot3SineFuture := pilot3BallSine_admissible
example : SmoothPilot3 pilot3BallHeight (fun _ => 0) := pilot3BallPlanar_admissible

example : (-1 / 8, (0 : Pilot3Space)) ∈ pilot3Region pilot3BallHeight pilot3SineFuture :=
  pilot3BallSine_nonempty

example : deriv (deriv (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0]))) (1 / 2) ≠ 0 :=
  pilot3SineFuture_curved.1

example : 0 < pilot3BallHeight 0 ∧ fderiv ℝ pilot3BallHeight 0 = 0 := pilot3BallHeight_critical

example : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
    ∀ x ∈ pilot3ClosedPositive pilot3BallHeight, pilot3BallHeight x ≤ δ →
      fderiv ℝ pilot3BallHeight x ≠ 0 := by
  obtain ⟨δ, hδ, hb⟩ := pilot3BallHeight_regular.exists_noncritical_band
  exact ⟨δ, hδ, pilot3BallHeight_band_below_critical hb, hb⟩

example : pilot3SpatialJoint pilot3BallHeight = Metric.sphere 0 1 := pilot3BallHeight_joint

example (ρ : ℝ) (hρ : 0 < ρ) :
    dimensionExpectedAction 2 ρ (pilot3Region pilot3BallHeight pilot3SineFuture) =
      pilot3Action ρ pilot3BallHeight pilot3SineFuture := pilot3BallSine_admissible.expectedAction_eq hρ

example {h₁ h₂ : Pilot3Space → ℝ} (hh₁ : Pilot3RegularHeight h₁) (hh₂ : Pilot3RegularHeight h₂)
    (hd : Disjoint (pilot3ClosedPositive h₁) (pilot3ClosedPositive h₂)) :
    pilot3SpatialJoint (fun x => max (h₁ x) (h₂ x)) = pilot3SpatialJoint h₁ ∪ pilot3SpatialJoint h₂ :=
  pilot3SpatialJoint_max hh₁ hh₂ hd

example {h : Pilot3Space → ℝ} {x : Pilot3Space} (hx : x ∉ pilot3ClosedPositive h) :
    x ∉ pilot3SpatialJoint h := pilot3SpatialJoint_excludes_exterior hx

example : SmoothPilot3 (fun _ => 0) (fun _ => 0) := pilot3Empty_admissible

example : pilot3Region (fun _ => 0) (fun _ => 0) = ∅ ∧
    pilot3SpatialJoint (fun _ => 0) = ∅ ∧
    pilot3ProjectedArea (fun _ => 0) (fun _ => 0) = 0 ∧
    pilot3BoundaryIntegral (fun _ => 0) (fun _ => 0) = 0 := by
  refine ⟨?_, ?_⟩
  · apply eq_empty_iff_forall_not_mem.mpr
    intro p hp
    have hl : 0 < p.1 := by simpa using hp.1
    exact (not_lt_of_ge hl.le) hp.2
  · simp [pilot3SpatialJoint, pilot3ClosedPositive, pilot3SurfaceMeasure, pilot3BoundaryIntegral]
