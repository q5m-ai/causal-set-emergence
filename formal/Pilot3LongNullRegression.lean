import BoundaryDraft.Pilot3LongNull
import BoundaryDraft.Pilot3Annulus

/-!
Standalone regressions of the actual 3D density and signed long producer.
The full action/expectation limit is not asserted. Normalization is expanded
independently, and contacts/critical points remain in the geometric examples.
-/

open BoundaryDraft MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
noncomputable section
namespace Pilot3LongNullRegression

-- Physical dimension THREE: full circle mass and the radial exponent ONE.
example : pilot3CircleMeasure.real univ = 2 * Real.pi := pilot3Circle_mass
example (v : ℝ) : pilot3NullJacobian 0 v = 1 / 4 := by simp [pilot3NullJacobian]
example {v : ℝ} (hv : v ≠ 0) : pilot3NullJacobian (v ^ 2) v = 0 := by
  simp [pilot3NullJacobian, pow_ne_zero 2 hv]
example {σ v : ℝ} (hv : v ≠ 0) :
    (1 / (2 * v)) * ((v - σ / v) / 2) = (1 - σ / v ^ 2) / 4 :=
  (pilot3NullJacobian_eq hv).symm

-- No radial-symmetry assumption is required for the actual measure transport.
example {δ : ℝ} (hδ : 0 < δ) (F : Pilot3Spacetime → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in {z : Pilot3Spacetime | ‖z.2‖ ≤ z.1 ∧ δ ≤ z.1 + ‖z.2‖}, F z) =
      ∫⁻ ω, (∫⁻ p in properTimeDomain δ, ENNReal.ofReal ((1 - p 0 / p 1 ^ 2) / 4) *
        F ((p 1 + p 0 / p 1) / 2, ((p 1 - p 0 / p 1) / 2) • ω.val)) ∂pilot3CircleMeasure := by
  simpa only [pilot3LongFuture, dimensionCausalFuture, Prod.fst_zero, Prod.snd_zero, sub_zero,
    pilot3NullJacobian, pilot3RayDisplacement] using lintegral_pilot3LongFuture_properTime hδ F hF

-- Equality at the sharp cutoff belongs to long, even on a null ray.
example (ω : Pilot3Circle) {δ : ℝ} (hδ : 0 < δ) :
    pilot3RayDisplacement ω.val 0 δ ∈ pilot3LongFuture δ ∧
      pilot3RayDisplacement ω.val 0 δ ∉ pilot3ShortFuture δ := by
  have hw : ‖ω.val‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hp := pilot3RayDisplacement_parameters hw hδ ⟨le_rfl, sq_nonneg δ⟩
  have hc := pilot3RayDisplacement_causal hw hδ ⟨le_rfl, sq_nonneg δ⟩
  have hl : pilot3RayDisplacement ω.val 0 δ ∈ pilot3LongFuture δ :=
    ⟨by simpa [dimensionCausalFuture] using hc, hp.1.ge⟩
  exact ⟨hl, fun hs => hs.2 hl⟩

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (ρ δ : ℝ) :
    dimensionWeightedAction 2 (dimensionPointCoefficient 3) (dimensionPairCoefficient 3)
      (dimensionIntervalCoefficient 3) ρ (pilot3Region h f) (fun _ => 1) =
      ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
        dimensionPairCoefficient 3 * ρ * ∫ z in pilot3ShortFuture δ,
          dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ *
            (z.1 ^ 2 - ‖z.2‖ ^ 2) ^ (3 / 2 : ℝ)) * pilot3Overlap h f z) +
      (-(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ * ∫ z in pilot3LongFuture δ,
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ *
          (z.1 ^ 2 - ‖z.2‖ ^ 2) ^ (3 / 2 : ℝ)) * pilot3Overlap h f z) := by
  simpa only [pilot3Action, pilot3ShortAction, pilot3LongAction, pilot3DisplacementKernel,
    dimensionBilocalKernel, dimensionIntervalSq, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Nat.reduceAdd, Nat.cast_ofNat] using hf.action_eq_short_add_long ρ δ

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (pilot3LongDensity h f δ) ∧ HasCompactSupport (pilot3LongDensity h f δ) ∧
      Integrable (pilot3LongDensity h f δ) ∧
      (∀ σ, pilot3LongDensityENN h f δ σ < ⊤) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |pilot3LongDensity h f δ σ| ≤ C :=
  ⟨hf.measurable_longDensity δ, hf.hasCompactSupport_longDensity hδ, hf.integrable_longDensity hδ,
    hf.longDensityENN_lt_top hδ, hf.bounded_longDensity hδ⟩

-- Signed transport is not justified by cancellation. It holds for any
-- continuous signed test weight, including negative ones, at finite density.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ)
    (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable (fun σ => w σ * pilot3LongDensity h f δ σ) ∧
      (∫ z in pilot3LongFuture δ, w (dimensionIntervalSq 0 z) * pilot3Overlap h f z) =
        ∫ σ : ℝ, w σ * pilot3LongDensity h f δ σ :=
  ⟨hf.integrable_longDensity_weight hδ w hw, hf.integral_longOverlap hδ w hw⟩

-- Independently expand the finite-density signed density relation.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    -(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ *
      (∫ z in pilot3LongFuture δ, dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ *
        (z.1 ^ 2 - ‖z.2‖ ^ 2) ^ (3 / 2 : ℝ)) * pilot3Overlap h f z) =
      -(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ *
        ∫ σ : ℝ, dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
          pilot3LongDensity h f δ σ := by
  simpa only [pilot3LongAction, pilot3DisplacementKernel, dimensionBilocalKernel, dimensionIntervalSq,
    Prod.fst_zero, Prod.snd_zero, sub_zero, Nat.reduceAdd, Nat.cast_ofNat] using hf.longAction_eq_density hδ ρ

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ σ ∈ Ioc 0 ε,
      |pilot3LongDensity h f δ σ - (b0 + b1 * σ)| ≤ C * σ ^ 2 :=
  hf.longDensity_linear_quadratic_bound hδ

-- The exponent is REAL 3/2, not the inadequate integer first-order jet.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b0 b1 : ℝ, (fun σ => pilot3LongDensity h f δ σ - (b0 + b1 * σ))
      =o[𝓝[>] 0] (fun σ => σ ^ (3 / 2 : ℝ)) := hf.longDensity_right_linear_jet hδ

-- No density, jet, cancellation or limit hypothesis beyond unchanged geometry.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ *
      ∫ z in {z : Pilot3Spacetime | ‖z.2‖ ≤ z.1 ∧ δ ≤ z.1 + ‖z.2‖},
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ *
          (z.1 ^ 2 - ‖z.2‖ ^ 2) ^ (3 / 2 : ℝ)) * pilot3Overlap h f z) atTop (𝓝 0) := by
  simpa only [pilot3LongAction, pilot3DisplacementKernel, dimensionBilocalKernel, dimensionIntervalSq,
    pilot3LongFuture, dimensionCausalFuture, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Nat.reduceAdd, Nat.cast_ofNat] using hf.tendsto_longAction hδ

-- Genuinely curved future, nonempty region, retained positive-height critical point.
example {δ : ℝ} (hδ : 0 < δ) :
    (-1 / 8, (0 : Pilot3Space)) ∈ pilot3Region pilot3BallHeight pilot3SineFuture ∧
    deriv (deriv (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0]))) (1 / 2) ≠ 0 ∧
    (0 < pilot3BallHeight 0 ∧ fderiv ℝ pilot3BallHeight 0 = 0) ∧
    Tendsto (fun ρ => pilot3LongAction ρ δ pilot3BallHeight pilot3SineFuture) atTop (𝓝 0) :=
  ⟨pilot3BallSine_nonempty, pilot3SineFuture_curved.1, pilot3BallHeight_critical,
    pilot3BallSine_admissible.tendsto_longAction hδ⟩

-- A contact at the retained critical center, in EVERY direction.
theorem exact_contact (ω : Pilot3Circle) :
    pilot3RayGap pilot3BallHeight (fun _ => 0) 0 ω.val 0 (1 / 2) = 0 ∧
    fderiv ℝ pilot3BallHeight 0 = 0 ∧
    (∀ σ v : ℝ, 0 ≤ σ → 1 / 2 ≤ v →
      max 0 (pilot3RayGap pilot3BallHeight (fun _ => 0) 0 ω.val σ v) = 0) ∧
    Tendsto (fun ρ => pilot3LongAction ρ (1 / 2) pilot3BallHeight (fun _ => 0)) atTop (𝓝 0) := by
  have hg : pilot3RayGap pilot3BallHeight (fun _ => 0) 0 ω.val 0 (1 / 2) = 0 := by
    norm_num [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, pilot3BallHeight]
  refine ⟨hg, pilot3BallHeight_critical.2, ?_, pilot3BallPlanar_admissible.tendsto_longAction (by norm_num)⟩
  obtain ⟨κ, η, C⟩ := pilot3BallPlanar_admissible.exists_slopeControl
  intro σ v hσ hv
  exact max_eq_left (C.rayGap_nonpos_of_cutoff_nonpos (by norm_num) hv hσ 0 ω.val
    (mem_sphere_zero_iff_norm.mp ω.property) hg.le)

private def approachingSource (t : ℝ) : Pilot3Space :=
  (WithLp.equiv 2 _).symm ![Real.sqrt (1 / 2 - 2 * t), 0]

private theorem approaching_height {t : ℝ} (ht : t ∈ Ioc 0 (1 / 4)) :
    pilot3BallHeight (approachingSource t) = 1 / 8 + t / 2 := by
  have hs : 0 ≤ (1 : ℝ) / 2 - 2 * t := by linarith [ht.2]
  simp only [pilot3BallHeight, approachingSource, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  norm_num [Real.sq_sqrt hs, ← pow_two]
  ring

-- Roots approach the SAME fixed cutoff. This is not a shrinking-cutoff limit.
theorem approaching_contact :
    (∀ t ∈ Ioc 0 (1 / 4), ∀ ω : Pilot3Circle, 1 / 4 < 1 / 4 + t ∧
      pilot3RayGap pilot3BallHeight (fun _ => 0) (approachingSource t) ω.val 0 (1 / 4 + t) = 0) ∧
    Tendsto (fun t : ℝ => 1 / 4 + t) (𝓝[>] 0) (𝓝 (1 / 4)) ∧
    Tendsto (fun ρ => pilot3LongAction ρ (1 / 4) pilot3BallHeight (fun _ => 0)) atTop (𝓝 0) := by
  refine ⟨?_, ?_, pilot3BallPlanar_admissible.tendsto_longAction (by norm_num)⟩
  · intro t ht ω
    refine ⟨by linarith [ht.1], ?_⟩
    simp only [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, approaching_height ht,
      zero_div, sub_zero, add_zero, max_eq_right (show 0 ≤ (1 : ℝ) / 8 + t / 2 by linarith [ht.1])]
    ring
  · simpa using (tendsto_const_nhds (x := (1 : ℝ) / 4)).add
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))

-- The whole previously positive fibre can close, not just a negligible level.
example {t : ℝ} (ht : t ∈ Ioc 0 (1 / 4)) (ω : Pilot3Circle) :
    0 < pilot3RayGap pilot3BallHeight (fun _ => 0) (approachingSource t) ω.val 0 (1 / 4) ∧
    ∀ v : ℝ, 1 / 4 ≤ v →
      max 0 (pilot3RayGap pilot3BallHeight (fun _ => 0) (approachingSource t) ω.val (t / 4) v) = 0 := by
  have hh := approaching_height ht
  have hpos : 0 ≤ (1 : ℝ) / 8 + t / 2 := by linarith [ht.1]
  constructor
  · simp only [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, hh, max_eq_right hpos,
      zero_div, add_zero, sub_zero]
    linarith [ht.1]
  · intro v hv
    apply max_eq_left
    simp only [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, hh, max_eq_right hpos,
      add_zero, sub_zero]
    have hv0 : 0 < v := by linarith
    have hprod : 0 ≤ (v - 1 / 4) * (v - t) := mul_nonneg (by linarith) (by linarith [ht.2])
    have hdiv : t / 4 / v * v = t / 4 := div_mul_cancel₀ _ hv0.ne'
    nlinarith

-- Entire disconnected and annular regions, NOT sums of componentwise actions.
example {δ : ℝ} (hδ : 0 < δ) :
    (0 < pilot3DisconnectedHeight 0 ∧ fderiv ℝ pilot3DisconnectedHeight 0 = 0) ∧
    (0 < pilot3DisconnectedHeight pilot3OtherCenter ∧ fderiv ℝ pilot3DisconnectedHeight pilot3OtherCenter = 0) ∧
    Tendsto (fun ρ => pilot3LongAction ρ δ pilot3DisconnectedHeight pilot3SineFuture) atTop (𝓝 0) :=
  ⟨pilot3Disconnected_both_critical.1, pilot3Disconnected_both_critical.2,
    pilot3DisconnectedSine_admissible.tendsto_longAction hδ⟩

example {δ : ℝ} (hδ : 0 < δ) :
    (∃ x : Pilot3Space, 0 < pilot3AnnularHeight x ∧ fderiv ℝ pilot3AnnularHeight x = 0) ∧
    Tendsto (fun ρ => pilot3LongAction ρ δ pilot3AnnularHeight pilot3SineFuture) atTop (𝓝 0) :=
  ⟨pilot3Annular_critical_nonempty, pilot3AnnularSine_admissible.tendsto_longAction hδ⟩

example {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => pilot3LongAction ρ δ (fun _ => 0) (fun _ => 0)) atTop (𝓝 0) :=
  pilot3Empty_admissible.tendsto_longAction hδ

end Pilot3LongNullRegression
