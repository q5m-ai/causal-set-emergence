import BoundaryDraft.ShortRadialAbsolute
import BoundaryDraft.ShortOverlapAsymptotics

/-!
# The direct-origin analytic backend

This is a polynomial overlap MODEL and a conditional remainder theorem, not a
new geometric action or a proof for class E. Geometry must separately produce
the actual absolute density decomposition and primitive derivative bounds.
No model, jet, remainder or limit is inserted into geometric admissibility.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace AbsoluteShortModel

/-- Sphere-averaged quadratic overlap coefficients. `V` is the point volume;
the other three coefficients already include the full angular measure. -/
def density (δ V ℓ α β σ : ℝ) : ℝ :=
  (4 * Real.pi * V) * shortRadialConstant δ σ + ℓ * shortRadialTime δ σ +
    α * shortRadialTimeSquare δ σ + β * shortRadialQuadratic δ σ

/-- Exact signed integration of all four basis terms, after establishing each
one's absolute integrability. The cutoff is fixed and strictly positive. -/
theorem integral_density {δ c ρ : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ)
    (V ℓ α β : ℝ) :
    (∫ σ : ℝ in Ioi 0, density δ V ℓ α β σ * bdgKernel (c * ρ * σ ^ 2)) =
      (4 * Real.pi * V) * (∫ σ : ℝ in Ioi 0, shortRadialConstant δ σ * bdgKernel (c * ρ * σ ^ 2)) +
      ℓ * (∫ σ : ℝ in Ioi 0, shortRadialTime δ σ * bdgKernel (c * ρ * σ ^ 2)) +
      α * (∫ σ : ℝ in Ioi 0, shortRadialTimeSquare δ σ * bdgKernel (c * ρ * σ ^ 2)) +
      β * (∫ σ : ℝ in Ioi 0, shortRadialQuadratic δ σ * bdgKernel (c * ρ * σ ^ 2)) := by
  have h₀ := (integrableOn_shortRadialConstant hδ hc hρ).const_mul (4 * Real.pi * V)
  have h₁ := (integrableOn_shortRadialTime hδ hc hρ).const_mul ℓ
  have h₂ := (integrableOn_shortRadialTimeSquare hδ hc hρ).const_mul α
  have h₃ := (integrableOn_shortRadialQuadratic hδ hc hρ).const_mul β
  have he (σ : ℝ) : density δ V ℓ α β σ * bdgKernel (c * ρ * σ ^ 2) =
      (4 * Real.pi * V) * (shortRadialConstant δ σ * bdgKernel (c * ρ * σ ^ 2)) +
      ℓ * (shortRadialTime δ σ * bdgKernel (c * ρ * σ ^ 2)) +
      α * (shortRadialTimeSquare δ σ * bdgKernel (c * ρ * σ ^ 2)) +
      β * (shortRadialQuadratic δ σ * bdgKernel (c * ρ * σ ^ 2)) := by unfold density; ring
  simp_rw [he]
  have he₀ := integral_add h₀ h₁
  have he₁ := integral_add (h₀.add h₁) h₂
  have he₂ := integral_add ((h₀.add h₁).add h₂) h₃
  simp only [Pi.add_apply] at he₀ he₁ he₂
  rw [he₂, he₁, he₀]
  simp only [integral_const_mul]

theorem integrable_density {δ c ρ : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ)
    (V ℓ α β : ℝ) :
    IntegrableOn (fun σ : ℝ => density δ V ℓ α β σ * bdgKernel (c * ρ * σ ^ 2)) (Ioi 0) := by
  have hi := ((((integrableOn_shortRadialConstant hδ hc hρ).const_mul (4 * Real.pi * V)).add
    ((integrableOn_shortRadialTime hδ hc hρ).const_mul ℓ)).add
      ((integrableOn_shortRadialTimeSquare hδ hc hρ).const_mul α)).add
        ((integrableOn_shortRadialQuadratic hδ hc hρ).const_mul β)
  apply hi.congr
  exact Eventually.of_forall fun σ => by dsimp [density]; ring

/-- Unconditional analytic response of the complete quadratic overlap model.
It retains the volume/point cancellation, time-linear mode, and both quadratic
modes with the unchanged signed BDG kernel and physical density powers. -/
theorem action_limit {δ : ℝ} (hδ : 0 < δ) (V ℓ α β : ℝ) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (V - ρ * ∫ σ : ℝ in Ioi 0, density δ V ℓ α β σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))) atTop (𝓝 ((α - 3 * β) / (2 * Real.pi))) := by
  have hc : 0 < Real.pi / 24 := by positivity
  have h₀ := shortRadialConstant_point_limit hδ V
  have h₁ := (shortRadialTime_limit hδ hc).const_mul (-(4 / Real.sqrt 6) * ℓ)
  have h₂ := (bdg_shortRadialTimeSquare_action_limit hδ).const_mul α
  have h₃ := (bdg_shortRadialQuadratic_action_limit hδ).const_mul β
  have hl := ((h₀.add h₁).add h₂).add h₃
  have he : ((0 + (-(4 / Real.sqrt 6) * ℓ) * 0) + α * (1 / (2 * Real.pi))) +
      β * (-3 / (2 * Real.pi)) = (α - 3 * β) / (2 * Real.pi) := by ring
  rw [he] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  rw [integral_density hδ hc hρ]
  ring

/-- A conditional analytic transfer with derivative-controlled remainder.
The decomposition is an explicit analytic INPUT, not a geometric hypothesis or
an assertion that the class-E overlap has been connected to this backend. -/
theorem action_limit_of_remainder {δ T : ℝ} (hδ : 0 < δ)
    {R : ShortNullRemainder.Space → ℝ} (hR : Measurable R)
    (hb : ShortNullRemainder.CubicBounds R δ T)
    (B : ℝ → ℝ) (V ℓ α β : ℝ)
    (hB : ∀ σ, 0 < σ → B σ = density δ V ℓ α β σ + ShortNullRemainder.density R δ σ) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (V - ρ * ∫ σ : ℝ in Ioi 0, B σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)))
      atTop (𝓝 ((α - 3 * β) / (2 * Real.pi))) := by
  have hc : 0 < Real.pi / 24 := by positivity
  have hr := (hb.normalized_density_limit hR hc).const_mul (-(4 / Real.sqrt 6))
  simp only [mul_zero] at hr
  have hl := (action_limit hδ V ℓ α β).add hr
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hiM := integrable_density hδ hc hρ V ℓ α β
  have hiR := ShortOverlapAsymptotics.integrableOn_remainder_density_kernel hb hR hc hρ
  have he : (∫ σ : ℝ in Ioi 0, B σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) =
      (∫ σ : ℝ in Ioi 0, density δ V ℓ α β σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) +
      ∫ σ : ℝ in Ioi 0, ShortNullRemainder.density R δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) := by
    rw [← integral_add hiM hiR]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro σ hσ
    dsimp only
    rw [hB σ hσ, add_mul]
  rw [he]
  ring

end AbsoluteShortModel
end BoundaryDraft
