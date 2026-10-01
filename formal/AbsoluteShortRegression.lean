import BoundaryDraft.AbsoluteShortModel

/-!
Independent absolute-overlap analytic contracts for partial work on #97.
These regressions do not instantiate class E or assert a new geometric limit.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section

-- The densities come from the actual moving lower endpoint, not integration
-- from zero, which would be singular at positive proper time.
example {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hs : σ ≤ δ ^ 2) :
    (∫ v in (Real.sqrt σ)..δ, (v - σ / v) ^ 2 / (8 * v)) =
      δ ^ 2 / 16 - σ / 4 * Real.log δ - σ ^ 2 / (16 * δ ^ 2) + σ / 8 * Real.log σ := by
  rw [← shortRadialConstant_eq_integral hδ hσ hs, shortRadialConstant, if_pos ⟨hσ.le, hs⟩]

example {σ : ℝ} (hσ : 0 < σ) :
    Real.sqrt σ ^ 3 / 48 - σ * Real.sqrt σ / 16 + σ ^ 2 / 16 * (Real.sqrt σ)⁻¹ -
      σ ^ 3 / 48 * (Real.sqrt σ ^ 3)⁻¹ = 0 := shortRadialTimePrimitive_sqrt hσ

example {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hs : σ ≤ δ ^ 2) :
    (∫ v in (Real.sqrt σ)..δ,
      ((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2)) =
      δ ^ 3 / 48 - σ * δ / 16 + σ ^ 2 / (16 * δ) - σ ^ 3 / (48 * δ ^ 3) := by
  rw [← shortRadialTime_eq_integral hδ hσ hs, shortRadialTime, if_pos ⟨hσ.le, hs⟩]

example {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hs : σ ≤ δ ^ 2) :
    (∫ v in (Real.sqrt σ)..δ,
      ((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2) ^ 2) =
      δ ^ 4 / 128 - σ ^ 2 / 16 * Real.log δ - σ ^ 4 / (128 * δ ^ 4) +
        σ ^ 2 / 32 * Real.log σ := by
  rw [← shortRadialTimeSquare_eq_integral hδ hσ hs, shortRadialTimeSquare, if_pos ⟨hσ.le, hs⟩]

-- Vertex, moving-endpoint contact, and empty support are retained.
example (δ : ℝ) : shortRadialConstant δ 0 = δ ^ 2 / 16 := by
  simp [shortRadialConstant, sq_nonneg]

example : shortRadialConstant 2 4 = 0 := by
  have hl : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num [shortRadialConstant, hl]
  ring

example : shortRadialConstant 2 5 = 0 ∧ shortRadialTime 2 5 = 0 ∧
    shortRadialTimeSquare 2 5 = 0 := by
  norm_num [shortRadialConstant, shortRadialTime, shortRadialTimeSquare]

-- Signed coefficients and arbitrary positive scales are allowed.
example (k : ℝ) (hk : 0 < k) :
    (∫ σ : ℝ in Ioi 0, σ * Real.log σ * bdgKernel ((k * σ) ^ 2)) = k⁻¹ ^ 2 / 12 :=
  integral_bdgKernel_transverse_scaled_log_one k hk

example (δ V : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ * (V - ρ * (4 * Real.pi * V) *
      ∫ σ : ℝ in Ioi 0, shortRadialConstantModel δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) = 0 :=
  shortRadialConstantModel_point_cancellation δ V hρ

-- A true sharp-cutoff limit, not just the uncut model's exact response.
example {δ : ℝ} (hδ : 0 < δ) (V : ℝ) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (V - ρ * (4 * Real.pi * V) * ∫ σ : ℝ in Ioi 0,
        shortRadialConstant δ σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)))
      atTop (𝓝 0) := shortRadialConstant_point_limit hδ V

example {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
      shortRadialTime δ σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) atTop (𝓝 0) :=
  shortRadialTime_limit hδ (by positivity)

-- Neither quadratic component may be omitted or given the other's sign.
example {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * (Real.sqrt ρ * ρ *
      ∫ σ : ℝ in Ioi 0, shortRadialTimeSquare δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))) atTop (𝓝 (1 / (2 * Real.pi))) :=
  bdg_shortRadialTimeSquare_action_limit hδ

-- The complete model has the right coefficient, but a model is not a region.
example {δ : ℝ} (hδ : 0 < δ) (V ℓ α β : ℝ) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (V - ρ * ∫ σ : ℝ in Ioi 0,
        ((4 * Real.pi * V) * shortRadialConstant δ σ + ℓ * shortRadialTime δ σ +
          α * shortRadialTimeSquare δ σ + β * shortRadialQuadratic δ σ) *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))) atTop (𝓝 ((α - 3 * β) / (2 * Real.pi))) :=
  AbsoluteShortModel.action_limit hδ V ℓ α β

-- A global bound includes the truncated model's entire omitted tail, and
-- does not ask the kernel to be positive.
example {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ σ, 0 < σ →
    ‖shortRadialConstant δ σ - shortRadialConstantModel δ σ‖ ≤ C * σ ^ 3 :=
  shortRadialConstant_model_cubic_bound hδ

-- The remainder transfer remains explicitly conditional on primitive
-- derivative control and the exact ABSOLUTE density decomposition.
example {δ T : ℝ} (hδ : 0 < δ) {R : ShortNullRemainder.Space → ℝ} (hR : Measurable R)
    (hb : ShortNullRemainder.CubicBounds R δ T) (B : ℝ → ℝ) (V ℓ α β : ℝ)
    (hB : ∀ σ, 0 < σ → B σ = AbsoluteShortModel.density δ V ℓ α β σ +
      ShortNullRemainder.density R δ σ) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (V - ρ * ∫ σ : ℝ in Ioi 0, B σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)))
      atTop (𝓝 ((α - 3 * β) / (2 * Real.pi))) :=
  AbsoluteShortModel.action_limit_of_remainder hδ hR hb B V ℓ α β hB
