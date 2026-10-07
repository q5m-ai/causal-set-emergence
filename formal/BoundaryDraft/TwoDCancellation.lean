import BoundaryDraft.TwoDShortDensityJet
import BoundaryDraft.TwoDLongJet
import BoundaryDraft.DimensionCancellation

/-! # Genuine 2D signed cancellation for derived affine remainder and long jets -/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft

theorem twoD_affine_cancellation (D : ℝ → ℝ) (hm : Measurable D) (C : ℝ)
    (hbound : ∀ σ, 0 < σ → ‖D σ‖ ≤ C) (a₀ a₁ : ℝ)
    (hj : (fun σ => D σ - (a₀ + a₁ * σ)) =o[𝓝[>] 0] (fun σ => σ)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ 2 * ∫ σ : ℝ in Ioi 0, D σ * dimensionKernel 2 (c * ρ * σ)) atTop (𝓝 0) := by
  let b : ℕ → ℝ := fun j => if j = 0 then a₀ else a₁
  have he (σ : ℝ) : dimensionJet 2 b σ = a₀ + a₁ * σ := by
    simp [dimensionJet, dimensionFactorCount, Finset.sum_range_succ, b]
  have hjet : (fun σ => D σ - dimensionJet 2 b σ) =o[𝓝[>] 0] (fun σ => σ ^ ((2 : ℝ) / 2)) := by
    simpa only [he, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using hj
  have hl := dimensionKernel_transverse_cancellation 2 (by norm_num) D hm C hbound b hjet c hc
  norm_num at hl ⊢
  exact hl

namespace TwoDShortRemainder.CubicBounds
variable {R : TwoDSpacetime → ℝ} {δ T : ℝ} (hB : CubicBounds R δ T)
include hB

/-- The actual compensated remainder density has zero physical signed response. -/
theorem normalized_density_limit (hR : Measurable R) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ 2 * ∫ σ : ℝ in Ioi 0,
      density R δ σ * dimensionKernel 2 (c * ρ * σ)) atTop (𝓝 0) := by
  obtain ⟨a₀, a₁, hj⟩ := hB.density_right_affine_jet hR
  exact twoD_affine_cancellation _ (measurable_density hR δ)
    (T * δ ^ 2 * (parameterMeasure δ).real univ) (fun _ hs => hB.density_bound hs.le) a₀ a₁ hj hc

end TwoDShortRemainder.CubicBounds
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem tendsto_longDensity {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => ρ ^ 2 * ∫ σ : ℝ in Ioi 0, twoDLongDensity h f δ σ *
      dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ)) atTop (𝓝 0) := by
  obtain ⟨a₀, a₁, hj⟩ := hf.longDensity_right_linear_jet hδ
  obtain ⟨C, _, hb⟩ := hf.bounded_longDensity hδ
  exact twoD_affine_cancellation _ (hf.measurable_longDensity δ) C
    (fun σ _ => by simpa only [Real.norm_eq_abs] using hb σ) a₀ a₁
    (by simpa using hj) (dimensionIntervalCoefficient_pos 2 (by norm_num))

/-- For EVERY fixed positive cutoff, the complete actual long action tends to
zero. Null partners and cutoff/closing contacts were retained in the jet. -/
theorem tendsto_longAction {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => twoDLongAction ρ δ h f) atTop (𝓝 0) := by
  have hl := (hf.tendsto_longDensity hδ).const_mul (-(dimensionPairCoefficient 2))
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards with ρ
  rw [hf.longAction_eq_density hδ ρ]
  have he : (∫ σ : ℝ, dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ) *
      twoDLongDensity h f δ σ) = ∫ σ : ℝ in Ioi 0, twoDLongDensity h f δ σ *
        dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ) := by
    rw [← integral_Ici_eq_integral_Ioi]
    have hz : ∀ σ, σ ∉ Ici (0 : ℝ) →
        dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ) * twoDLongDensity h f δ σ = 0 := by
      intro σ hσ
      simp [twoDLongDensity, longDensityENN_negative δ (lt_of_not_ge hσ)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    congr 1
    ext σ
    ring
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  rw [he]
  ring

end SmoothTwoD
end BoundaryDraft
