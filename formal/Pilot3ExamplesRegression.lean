import BoundaryDraft.Pilot3Examples
import BoundaryDraft.Pilot3Components
import BoundaryDraft.Pilot3Annulus

/-! Concrete nonvacuity and all-component/exterior controls. The disconnected
and annular examples now have proved admissibility and integration. No bilocal
action additivity or smoothness of arbitrary raw maxima is asserted. -/

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

example : SmoothPilot3 pilot3DisconnectedHeight pilot3SineFuture := pilot3DisconnectedSine_admissible
example : SmoothPilot3 pilot3AnnularHeight pilot3SineFuture := pilot3AnnularSine_admissible
example : SmoothPilot3 pilot3AnnularHeight (fun _ => 0) := pilot3AnnularPlanar_admissible

example : pilot3SpatialJoint pilot3DisconnectedHeight =
    Metric.sphere (0 : Pilot3Space) 1 ∪ Metric.sphere pilot3OtherCenter 1 := pilot3Disconnected_joint

example : (0 < pilot3DisconnectedHeight 0 ∧ fderiv ℝ pilot3DisconnectedHeight 0 = 0) ∧
    (0 < pilot3DisconnectedHeight pilot3OtherCenter ∧ fderiv ℝ pilot3DisconnectedHeight pilot3OtherCenter = 0) :=
  pilot3Disconnected_both_critical

example : pilot3SpatialJoint pilot3AnnularHeight =
    Metric.sphere (0 : Pilot3Space) 1 ∪ Metric.sphere (0 : Pilot3Space) 2 := pilot3Annular_joint

example : ∃ x : Pilot3Space, 0 < pilot3AnnularHeight x ∧ fderiv ℝ pilot3AnnularHeight x = 0 :=
  pilot3Annular_critical_nonempty

example : ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 δ) →
    IntegrableOn (fun x => g (pilot3AnnularHeight x)) (pilot3ClosedCollar pilot3AnnularHeight δ) ∧
    (∫ x in pilot3ClosedCollar pilot3AnnularHeight δ, g (pilot3AnnularHeight x)) =
      ∫ t in Icc 0 δ, g t * pilot3HeightDensity pilot3AnnularHeight t := pilot3Annular_collar_coarea

example : ∃ δ : ℝ, 0 < δ ∧ ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 δ) →
    IntegrableOn (fun x => g (pilot3DisconnectedHeight x)) (pilot3ClosedCollar pilot3DisconnectedHeight δ) ∧
    (∫ x in pilot3ClosedCollar pilot3DisconnectedHeight δ, g (pilot3DisconnectedHeight x)) =
      ∫ t in Icc 0 δ, g t * pilot3HeightDensity pilot3DisconnectedHeight t := pilot3Disconnected_collar_coarea

-- Negative heights vanish; the proved boundary-density limit is right-sided.
example (t : ℝ) (ht : t < 0) : pilot3HeightDensity pilot3AnnularHeight t = 0 :=
  pilot3Annular_regular.heightDensity_eq_zero_of_neg t ht

example : (∫ x in {x | 0 < pilot3AnnularHeight x}, pilot3Laplacian pilot3SineFuture x) =
    -(∫ x, inner (𝕜 := ℝ) (pilot3Gradient pilot3SineFuture x) (pilot3Gradient pilot3AnnularHeight x) /
      ‖pilot3Gradient pilot3AnnularHeight x‖ ∂pilot3SurfaceMeasure pilot3AnnularHeight) := pilot3Annular_spatial_divergence
