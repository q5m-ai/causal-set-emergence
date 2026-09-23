import BoundaryDraft.AnalyticCore
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Normalized half-line Gaussian concentration

The kernel has unit mass on the positive half-line. Its rescaling limit is
proved by integrable domination, not by assuming localization. These results
are analytic components; no spacetime reduction is assumed or asserted here.
-/
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Unit-mass Gaussian associated with the BDG null-cap density. -/
def nullGaussian (u : ℝ) : ℝ :=
  (Real.sqrt 6)⁻¹ * Real.exp (-(Real.pi / 24) * u^2)

theorem integrableOn_nullGaussian : IntegrableOn nullGaussian (Ioi (0:ℝ)) :=
  ((integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 24)).const_mul
    (Real.sqrt 6)⁻¹).integrableOn

theorem integral_nullGaussian : (∫ u in Ioi (0:ℝ), nullGaussian u) = 1 := by
  unfold nullGaussian
  rw [integral_const_mul, integral_gaussian_Ioi,
    show Real.pi / (Real.pi / 24) = 4*6 by field_simp; ring,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hs4]
  field_simp

theorem nullGaussian_rescaling_limit (B : ℝ → ℝ) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ x, ‖B x‖ ≤ C) :
    Tendsto (fun ε : ℝ => ∫ u in Ioi (0:ℝ), nullGaussian u * B (ε*u))
      (𝓝 0) (𝓝 (B 0)) :=
  signed_rescaling_limit_unit_mass _ _ _ integrableOn_nullGaussian hB C hbound
    integral_nullGaussian

/-- Absolute integrability of the full fixed-domain rescaled integrand. -/
theorem integrableOn_nullGaussian_rescaled (B : ℝ → ℝ) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ x, ‖B x‖ ≤ C) (ε : ℝ) :
    IntegrableOn (fun u => nullGaussian u * B (ε*u)) (Ioi (0:ℝ)) := by
  apply (integrableOn_nullGaussian.norm.mul_const C).mono'
    (integrableOn_nullGaussian.aestronglyMeasurable.mul
      (hB.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun u => by
    change ‖nullGaussian u * B (ε*u)‖ ≤ ‖nullGaussian u‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound (ε*u)) (norm_nonneg _)

/-- The null density rescales with `ρ⁻¹ᐟ²`, not the graph-cap `ρ⁻¹ᐟ⁴`. -/
theorem tendsto_nullGaussian_width :
    Tendsto (fun ρ : ℝ => (Real.sqrt ρ)⁻¹) atTop (𝓝 0) := by
  simpa only [Real.sqrt_inv, Real.sqrt_zero] using
    (tendsto_inv_atTop_zero : Tendsto (fun ρ : ℝ => ρ⁻¹) atTop (𝓝 0)).sqrt

/-- Exact change of scale of the original density; the prefactor has mass four. -/
theorem nullGaussian_density_rescaling (ρ : ℝ) (hρ : 0 < ρ) (B : ℝ → ℝ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ σ in Ioi (0:ℝ), Real.exp (-(Real.pi / 24)*ρ*σ^2) * B σ) =
      4 * ∫ u in Ioi (0:ℝ), nullGaussian u * B ((Real.sqrt ρ)⁻¹*u) := by
  have hk : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  have hs := integral_comp_mul_left_Ioi
    (fun u => nullGaussian u * B ((Real.sqrt ρ)⁻¹*u)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  have he (σ : ℝ) : nullGaussian (Real.sqrt ρ*σ) * B σ =
      (Real.sqrt 6)⁻¹ * (Real.exp (-(Real.pi / 24)*ρ*σ^2)*B σ) := by
    unfold nullGaussian
    rw [mul_pow, Real.sq_sqrt hρ.le,
      show -(Real.pi / 24) * (ρ * σ^2) = -(Real.pi / 24)*ρ*σ^2 by ring]
    ring
  simp_rw [he, integral_const_mul] at hs
  have he' := congrArg (fun x : ℝ => 4 * Real.sqrt ρ * x) hs
  convert he' using 1 <;> field_simp
  ring

/-- Gaussian concentration for every bounded continuous weight, including the
whole finite-support null weight after a continuous left extension. -/
theorem nullGaussian_density_limit (B : ℝ → ℝ) (hB : Continuous B)
    (C : ℝ) (hbound : ∀ x, ‖B x‖ ≤ C) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ σ in Ioi (0:ℝ), Real.exp (-(Real.pi / 24)*ρ*σ^2)*B σ))
      atTop (𝓝 (4 * B 0)) := by
  have h := ((nullGaussian_rescaling_limit B hB C hbound).comp
    tendsto_nullGaussian_width).const_mul 4
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with ρ hρ
  exact (nullGaussian_density_rescaling ρ hρ B).symm

end BoundaryDraft
