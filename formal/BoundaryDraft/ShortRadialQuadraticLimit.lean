import BoundaryDraft.NullTransverseLogMoments
import BoundaryDraft.ShortRadialQuadratic

/-!
# Universal signed response of the radial quadratic short density

Positive rescaling preserves the vanishing polynomial moments. The second
logarithmic moment supplies the exact model response, and the global cubic
error bound transfers its limit to the actual fixed-cutoff radial density.
This is one analytic basis response, not the general short-displacement limit.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft

private theorem scaled_log_two_expand {k : ℝ} (hk : k ≠ 0) (z : ℝ) :
    (k⁻¹ * z) ^ 2 * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2) =
      k⁻¹ ^ 2 * (z ^ 2 * Real.log z * bdgKernel (z ^ 2)) -
        (k⁻¹ ^ 2 * Real.log k) * (z ^ 2 * bdgKernel (z ^ 2)) := by
  by_cases hz : z = 0
  · simp [hz]
  rw [Real.log_mul (inv_ne_zero hk) hz, Real.log_inv]
  ring

/-- Absolute integrability of the second logarithmic moment at positive scale. -/
theorem integrableOn_bdgKernel_transverse_scaled_log_two (k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => s ^ 2 * Real.log s * bdgKernel ((k * s) ^ 2))
      (Ioi 0) := by
  have hi : IntegrableOn (fun z : ℝ =>
      (k⁻¹ * z) ^ 2 * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2)) (Ioi 0) := by
    simp_rw [scaled_log_two_expand hk.ne']
    exact (integrableOn_bdgKernel_transverse_log_two.const_mul (k⁻¹ ^ 2)).sub
      ((integrableOn_bdgKernel_transverse_moment 2).const_mul (k⁻¹ ^ 2 * Real.log k))
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun z : ℝ => (k⁻¹ * z) ^ 2 * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2)) 0 hk).2
      (by simpa using hi)
  simpa only [inv_mul_cancel_left₀ hk.ne'] using hs

/-- The scale-dependent logarithm cancels against the zero second moment. -/
theorem integral_bdgKernel_transverse_scaled_log_two (k : ℝ) (hk : 0 < k) :
    (∫ s : ℝ in Ioi 0, s ^ 2 * Real.log s * bdgKernel ((k * s) ^ 2)) =
      k⁻¹ ^ 3 * (-Real.sqrt Real.pi / 12) := by
  have hs := integral_comp_mul_left_Ioi
    (fun z : ℝ => (k⁻¹ * z) ^ 2 * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  rw [hs]
  simp_rw [scaled_log_two_expand hk.ne']
  rw [integral_sub (integrableOn_bdgKernel_transverse_log_two.const_mul (k⁻¹ ^ 2))
    ((integrableOn_bdgKernel_transverse_moment 2).const_mul (k⁻¹ ^ 2 * Real.log k))]
  rw [integral_const_mul, integral_const_mul, integral_bdgKernel_transverse_log_two,
    integral_bdgKernel_transverse_two]
  ring

/-- The whole rescaled quadratic polynomial is absolutely integrable. -/
theorem integrableOn_bdgKernel_transverse_scaled_quadratic (b₀ b₁ b₂ k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => (b₀ + b₁ * s + b₂ * s ^ 2) *
      bdgKernel ((k * s) ^ 2)) (Ioi 0) := by
  have hi := (((integrableOn_bdgKernel_transverse_scaled_moment 0 k hk).const_mul b₀).add
    ((integrableOn_bdgKernel_transverse_scaled_moment 1 k hk).const_mul b₁)).add
      ((integrableOn_bdgKernel_transverse_scaled_moment 2 k hk).const_mul b₂)
  apply hi.congr
  exact Eventually.of_forall fun s => by dsimp; ring

/-- Polynomial cancellation holds at every positive scale, on the entire half-line. -/
theorem integral_bdgKernel_transverse_scaled_quadratic (b₀ b₁ b₂ k : ℝ) (hk : 0 < k) :
    (∫ s : ℝ in Ioi 0, (b₀ + b₁ * s + b₂ * s ^ 2) * bdgKernel ((k * s) ^ 2)) = 0 := by
  have hs := integral_comp_mul_left_Ioi
    (fun z : ℝ => (b₀ + b₁ * (k⁻¹ * z) + b₂ * (k⁻¹ * z) ^ 2) * bdgKernel (z ^ 2)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  rw [hs]
  have he (z : ℝ) : b₀ + b₁ * (k⁻¹ * z) + b₂ * (k⁻¹ * z) ^ 2 =
      b₀ + (b₁ * k⁻¹) * z + (b₂ * k⁻¹ ^ 2) * z ^ 2 := by ring
  simp_rw [he, integral_bdgKernel_transverse_quadratic, mul_zero]

/-- Absolute integrability of the full polynomial/logarithmic model at every
positive density; the model requires no sign condition on its cutoff parameter. -/
theorem integrableOn_shortRadialQuadraticModel (δ : ℝ) {c ρ : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => shortRadialQuadraticModel δ s *
      bdgKernel (c * ρ * s ^ 2)) (Ioi 0) := by
  let k := Real.sqrt (c * ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have he (s : ℝ) : c * ρ * s ^ 2 = (k * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he]
  have hi := (integrableOn_bdgKernel_transverse_scaled_quadratic
    (δ ^ 4 / 128) (-δ ^ 2 / 16) (3 / 16 * Real.log δ) k hk).add
      ((integrableOn_bdgKernel_transverse_scaled_log_two k hk).const_mul (-3 / 32))
  apply hi.congr
  exact Eventually.of_forall fun s => by dsimp [shortRadialQuadraticModel]; ring

/-- The model's normalized response is exactly independent of density and cutoff. -/
theorem shortRadialQuadraticModel_response (δ : ℝ) {c ρ : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) :
    Real.sqrt ρ * ρ * (∫ s : ℝ in Ioi 0, shortRadialQuadraticModel δ s *
      bdgKernel (c * ρ * s ^ 2)) = (Real.sqrt c)⁻¹ ^ 3 * Real.sqrt Real.pi / 128 := by
  let k := Real.sqrt (c * ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have he (s : ℝ) : c * ρ * s ^ 2 = (k * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he]
  have hexpand (s : ℝ) : shortRadialQuadraticModel δ s * bdgKernel ((k * s) ^ 2) =
      (δ ^ 4 / 128 + (-δ ^ 2 / 16) * s + (3 / 16 * Real.log δ) * s ^ 2) *
        bdgKernel ((k * s) ^ 2) +
          (-3 / 32) * (s ^ 2 * Real.log s * bdgKernel ((k * s) ^ 2)) := by
    unfold shortRadialQuadraticModel
    ring
  simp_rw [hexpand]
  rw [integral_add (integrableOn_bdgKernel_transverse_scaled_quadratic
    (δ ^ 4 / 128) (-δ ^ 2 / 16) (3 / 16 * Real.log δ) k hk)
      ((integrableOn_bdgKernel_transverse_scaled_log_two k hk).const_mul (-3 / 32)),
    integral_bdgKernel_transverse_scaled_quadratic _ _ _ k hk, integral_const_mul,
    integral_bdgKernel_transverse_scaled_log_two k hk, zero_add]
  have hsp : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hr : Real.sqrt ρ * ρ = Real.sqrt ρ ^ 3 := by
    nlinarith only [congrArg (fun t : ℝ => Real.sqrt ρ * t) (Real.sq_sqrt hρ.le)]
  dsimp only [k]
  rw [Real.sqrt_mul hc.le, hr]
  field_simp [hsp.ne', hsc.ne']
  ring

/-- The actual radial density is absolutely integrable against the signed kernel,
using the cubic error envelope and the already-integrable full model. -/
theorem integrableOn_shortRadialQuadratic {δ c ρ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => shortRadialQuadratic δ s * bdgKernel (c * ρ * s ^ 2))
      (Ioi 0) := by
  obtain ⟨C, hC⟩ := shortRadialQuadratic_model_cubic_bound hδ
  have hi := integrableOn_bdgKernel_mul_cubic_bound
    (fun s => shortRadialQuadratic δ s - shortRadialQuadraticModel δ s)
    ((measurable_shortRadialQuadratic δ).sub (by unfold shortRadialQuadraticModel; fun_prop))
    C hC hc hρ
  apply (hi.add (integrableOn_shortRadialQuadraticModel δ hc hρ)).congr
  exact Eventually.of_forall fun s => by dsimp; ring

/-- Universal radial-square response for every fixed positive cutoff and interval
coefficient. No shrinking-cutoff uniformity or geometric short-limit claim is made. -/
theorem shortRadialQuadratic_limit {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ s : ℝ in Ioi 0,
      shortRadialQuadratic δ s * bdgKernel (c * ρ * s ^ 2)) atTop
        (𝓝 ((Real.sqrt c)⁻¹ ^ 3 * Real.sqrt Real.pi / 128)) := by
  have hlim := (shortRadialQuadratic_model_error_limit hδ hc).add_const
    ((Real.sqrt c)⁻¹ ^ 3 * Real.sqrt Real.pi / 128)
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  simp_rw [sub_mul]
  rw [integral_sub (integrableOn_shortRadialQuadratic hδ hc hρ)
    (integrableOn_shortRadialQuadraticModel δ hc hρ),
    ← shortRadialQuadraticModel_response δ hc hρ]
  ring

private theorem shortRadialQuadratic_bdg_constant :
    (Real.sqrt (Real.pi / 24))⁻¹ ^ 3 * Real.sqrt Real.pi / 128 =
      3 * Real.sqrt 6 / (8 * Real.pi) := by
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h6 : 0 < Real.sqrt (6 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h24 : Real.sqrt (24 : ℝ) = 2 * Real.sqrt 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hp3 : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    calc
      _ = Real.sqrt Real.pi ^ 2 * Real.sqrt Real.pi := by ring
      _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]
  have h63 : Real.sqrt (6 : ℝ) ^ 3 = 6 * Real.sqrt 6 := by
    calc
      _ = Real.sqrt (6 : ℝ) ^ 2 * Real.sqrt 6 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  rw [Real.sqrt_div Real.pi_pos.le, h24]
  field_simp [hπ.ne', h6.ne', Real.pi_ne_zero]
  rw [mul_pow, hp3, h63]
  ring

/-- The physical interval coefficient gives the fixed-cutoff radial response. -/
theorem bdg_shortRadialQuadratic_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ s : ℝ in Ioi 0,
      shortRadialQuadratic δ s * bdgKernel ((Real.pi / 24) * ρ * s ^ 2)) atTop
        (𝓝 (3 * Real.sqrt 6 / (8 * Real.pi))) := by
  simpa only [shortRadialQuadratic_bdg_constant] using
    shortRadialQuadratic_limit hδ (by positivity : 0 < Real.pi / 24)

/-- Including the signed BDG action prefactor gives the coefficient of the
radial-square basis term, without asserting the full geometric short limit. -/
theorem bdg_shortRadialQuadratic_action_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * (Real.sqrt ρ * ρ *
      ∫ s : ℝ in Ioi 0, shortRadialQuadratic δ s *
        bdgKernel ((Real.pi / 24) * ρ * s ^ 2))) atTop (𝓝 (-3 / (2 * Real.pi))) := by
  convert (bdg_shortRadialQuadratic_limit hδ).const_mul (-(4 / Real.sqrt 6)) using 1
  have h6 : Real.sqrt (6 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne'
  field_simp [h6, Real.pi_ne_zero]
  ring

end BoundaryDraft
