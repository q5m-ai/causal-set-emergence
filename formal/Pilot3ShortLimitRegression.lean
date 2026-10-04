import BoundaryDraft.Pilot3ShortLimit
import BoundaryDraft.Pilot3Examples
import BoundaryDraft.Pilot3Annulus

/-!
Standalone actual short-producer contracts. The expanded observable retains
all causal partners, the physical point term and the independently defined
Hausdorff-one target. These tests do not prove or assume the long, global or
expected-action limit.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

-- Unconditional contract: the only geometric premise is the original class.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => pilot3ShortAction ρ δ h f) atTop
        (𝓝 (pilot3BoundaryIntegral h f)) := hf.exists_shortAction_limit

-- Independently expand the normalization, strict short cutoff and fixed target.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => ρ ^ (2 / 3 : ℝ) *
        (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
          dimensionPairCoefficient 3 * ρ * ∫ z : Pilot3Spacetime in
            {z | ‖z.2‖ ≤ z.1 ∧ z.1 + ‖z.2‖ < δ},
              dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ 0 z *
                pilot3Overlap h f z)) atTop
        (𝓝 (∫ x, pilot3Weight h f x ∂(pilot3SurfaceMeasure h).withDensity
          (fun x => ENNReal.ofReal (pilot3AreaDensity h f x)))) := by
  simpa only [pilot3ShortAction, pilot3ShortFuture_eq_norm, pilot3DisplacementKernel,
    pilot3BoundaryIntegral, pilot3ProjectedArea] using hf.exists_shortAction_limit

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (ρ δ : ℝ) :
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f - pilot3LongPairAction ρ δ h f :=
  hf.action_eq_short_sub_long ρ δ

-- Equality belongs only to long, including a null displacement.
example (ω : Pilot3Circle) {δ : ℝ} (hδ : 0 < δ) :
    (δ / 2, (δ / 2) • ω.val) ∈ pilot3LongFuture δ ∧
      (δ / 2, (δ / 2) • ω.val) ∉ pilot3ShortFuture δ := by
  have hn : ‖(δ / 2) • ω.val‖ = δ / 2 := by
    rw [norm_smul, mem_sphere_zero_iff_norm.mp ω.property, mul_one,
      Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
  rw [pilot3ShortFuture_eq_norm]
  simp only [pilot3LongFuture, dimensionCausalFuture, mem_setOf_eq, Prod.fst_zero,
    Prod.snd_zero, sub_zero, hn]
  constructor
  · constructor <;> linarith
  · intro h
    linarith [h.2]

example : pilot3CircleMeasure.real univ = 2 * Real.pi := pilot3Circle_mass
example (v σ : ℝ) : pilot3NullJacobian σ v = (1 - σ / v ^ 2) / 4 := rfl

example : (∫ u : ℝ in Ioi 0,
    u ^ (1 / 2 : ℝ) * dimensionKernel 3 (u ^ (3 / 2 : ℝ))) = -1 / 12 :=
  Pilot3ShortMoments.moment_half
example : (∫ u : ℝ in Ioi 0,
    u ^ (3 / 2 : ℝ) * dimensionKernel 3 (u ^ (3 / 2 : ℝ))) = Real.Gamma (5 / 3) / 4 :=
  Pilot3ShortMoments.moment_three_halves

-- The exact sharp time/radius fibres have different signs in the response.
example {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, Pilot3ShortBasis.Ftt δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 (1 / Real.pi)) := Pilot3ShortResponse.Ftt_action_limit hδ
example {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, Pilot3ShortBasis.Frr δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 (-2 / Real.pi)) := Pilot3ShortResponse.Frr_action_limit hδ

example (δ V ℓ α β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * V - dimensionPairCoefficient 3 * ρ *
      ∫ σ : ℝ in Ioi 0, Pilot3ShortResponse.modelGerm δ V ℓ α β σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) =
      (α - 2 * β) / Real.pi :=
  Pilot3ShortResponse.modelGerm_point_cancellation δ V ℓ α β hρ

-- The true direct-origin square and all bulk terms survive before averaging.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (z : Pilot3Spacetime) :
    pilot3AbsoluteShortPolynomial h f z =
      volume.real (pilot3Region h f) - z.1 * volume.real {x | 0 < h x} +
      (∫ x in {x | 0 < h x}, inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) +
      (1 / 2 : ℝ) * (∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x z.2 z.2) +
      (1 / 2 : ℝ) * (∫ x, (z.1 - inner (𝕜 := ℝ) (pilot3Gradient f x) z.2) ^ 2 /
        ‖pilot3Gradient h x‖ ∂pilot3SurfaceMeasure h) := hf.absoluteShortPolynomial_eq_expanded z

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    (pilot3ShortTimeCoefficient h - 2 * pilot3ShortSpaceCoefficient h f) / Real.pi =
      ∫ p, pilot3Weight h f p.2 ∂pilot3JointArea h f := by
  rw [hf.shortCoefficient_identification, hf.boundaryIntegral_eq_joint]

-- Curved future and its retained positive-height critical point.
example : (0 < pilot3BallHeight 0 ∧ fderiv ℝ pilot3BallHeight 0 = 0) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => pilot3ShortAction ρ δ pilot3BallHeight pilot3SineFuture) atTop
        (𝓝 (pilot3BoundaryIntegral pilot3BallHeight pilot3SineFuture)) :=
  ⟨pilot3BallHeight_critical, pilot3BallSine_admissible.exists_shortAction_limit⟩

-- Planar recovery is an instance, not an auxiliary analytic premise.
example : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => pilot3ShortAction ρ δ pilot3BallHeight (fun _ => 0)) atTop
      (𝓝 (∫ x, 1 / ‖pilot3Gradient pilot3BallHeight x‖ ∂pilot3SurfaceMeasure pilot3BallHeight)) := by
  simpa only [pilot3BoundaryIntegral_planar pilot3BallPlanar_admissible] using
    pilot3BallPlanar_admissible.exists_shortAction_limit

-- The whole disconnected region, not a sum of separately restricted pair terms.
example : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => pilot3ShortAction ρ δ pilot3DisconnectedHeight pilot3SineFuture) atTop
      (𝓝 (pilot3BoundaryIntegral pilot3DisconnectedHeight pilot3SineFuture)) :=
  pilot3DisconnectedSine_admissible.exists_shortAction_limit

-- Both annular boundary components and all positive-height critical points remain.
example : (∃ x : Pilot3Space, 0 < pilot3AnnularHeight x ∧ fderiv ℝ pilot3AnnularHeight x = 0) ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => pilot3ShortAction ρ δ pilot3AnnularHeight pilot3SineFuture) atTop
        (𝓝 (pilot3BoundaryIntegral pilot3AnnularHeight pilot3SineFuture)) :=
  ⟨pilot3Annular_critical_nonempty, pilot3AnnularSine_admissible.exists_shortAction_limit⟩

example : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    Tendsto (fun ρ => pilot3ShortAction ρ δ (fun _ => 0) (fun _ => 0)) atTop (𝓝 0) := by
  simpa [pilot3BoundaryIntegral, pilot3ProjectedArea, pilot3SurfaceMeasure,
    pilot3SpatialJoint, pilot3ClosedPositive] using pilot3Empty_admissible.exists_shortAction_limit
