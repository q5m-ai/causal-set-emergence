import BoundaryDraft.TwoDCancellation
import BoundaryDraft.TwoDShortResponse

/-!
# Unconditional assembly of the actual whole-region 2D short action

A single positive geometric cutoff is produced. Every signed split is preceded
by absolute integrability, and the point term remains entirely in this short
piece. The exact model and remainder are linked to the original overlap density.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

namespace TwoDShortRemainder

theorem density_zero_of_cutoff (R : Space → ℝ) {δ σ : ℝ} (hδ : 0 < δ) (hσ : δ ^ 2 ≤ σ) :
    density R δ σ = 0 := by
  have hz (p : Parameter δ) : parameterFibre R δ p σ = 0 := by
    have hs : ¬ σ ≤ p.2.val ^ 2 := by
      have hh := (sq_lt_sq₀ p.2.property.1.le hδ.le).mpr p.2.property.2
      linarith
    simp only [parameterFibre, TruncatedAffineJet.truncate, if_neg hs]
  simp only [density, hz, integral_zero]

namespace CubicBounds
variable {R : Space → ℝ} {δ T : ℝ} (hB : CubicBounds R δ T)
include hB

theorem integrable_density_kernel (hR : Measurable R) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => density R δ σ * dimensionKernel 2 (c * ρ * σ)) (Ioi 0) := by
  simpa only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using
    integrableOn_dimensionKernel_density_mul_bounded 2 (by norm_num) (density R δ)
      (measurable_density hR δ) (T * δ ^ 2 * (parameterMeasure δ).real univ)
      (fun _ hs => hB.density_bound hs.le) c ρ hc hρ

end CubicBounds
end TwoDShortRemainder
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- All analytic data are produced from the geometric contract. The displayed
model contains the independently defined target and the actual volume. -/
theorem exists_shortDensity_model :
    ∃ δ : ℝ, 0 < δ ∧ ∃ (R : TwoDSpacetime → ℝ) (T a b c : ℝ),
      Measurable R ∧ TwoDShortRemainder.CubicBounds R δ T ∧
      ∀ σ : ℝ, 0 < σ → twoDShortOverlapDensity h f δ σ =
        TwoDShortResponse.modelDensity (δ ^ 2) a b (volume.real (twoDRegion h f))
          (twoDBoundaryIntegral h f) c σ + TwoDShortRemainder.density R δ σ := by
  obtain ⟨δ, hδ, R, T, hR, hB, he⟩ := hf.exists_absoluteOverlap_remainder
  let a := volume.real (twoDRegion h f) * Real.log δ - volume.real {x | 0 < h x} * δ / 2 +
    (twoDShortTimeCoefficient h + twoDShortSpaceCoefficient h f) * δ ^ 2 / 16
  let b := volume.real {x | 0 < h x} / (2 * δ) + twoDBoundaryIntegral h f * Real.log δ / 4
  let c := (twoDShortTimeCoefficient h + twoDShortSpaceCoefficient h f) / (16 * δ ^ 2)
  refine ⟨δ, hδ, R, T, a, b, c, hR, hB, ?_⟩
  intro σ hσ
  by_cases hs : σ ≤ δ ^ 2
  · rw [hf.shortDensity_eq_polynomial_add_remainder hδ hR hB he hσ hs,
      hf.shortPolynomialDensity_eq hδ hσ hs]
    simp only [TwoDShortResponse.modelDensity, if_pos (show 0 < σ ∧ σ ≤ δ ^ 2 from ⟨hσ, hs⟩),
      TwoDShortResponse.lowDensity]
    rfl
  · rw [twoDShortOverlapDensity, twoDShortOverlapDensityENN_zero_of_le h f δ (not_le.mp hs).le,
      TwoDShortRemainder.density_zero_of_cutoff R hδ (not_le.mp hs).le]
    simp only [TwoDShortResponse.modelDensity, if_neg (not_and.mpr (fun _ => hs)),
      ENNReal.toReal_zero, add_zero]

/-- Unconditional signed short limit for one PRODUCED positive cutoff. No
limit theorem is used to establish the roots, jets, coefficients or remainder. -/
theorem exists_shortAction_limit :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun ρ : ℝ => twoDShortAction ρ δ h f)
      atTop (𝓝 (twoDBoundaryIntegral h f)) := by
  obtain ⟨δ, hδ, R, T, a, b, c, hR, hB, he⟩ := hf.exists_shortDensity_model
  have hM := TwoDShortResponse.tendsto_modelAction (sq_pos_of_pos hδ) a b
    (volume.real (twoDRegion h f)) (twoDBoundaryIntegral h f) c
  have hRlim := (hB.normalized_density_limit hR
    (dimensionIntervalCoefficient_pos 2 (by norm_num))).const_mul (dimensionPairCoefficient 2)
  have ht := hM.sub hRlim
  simp only [mul_zero, sub_zero] at ht
  refine ⟨δ, hδ, ht.congr' ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hk := mul_pos (dimensionIntervalCoefficient_pos 2 (by norm_num)) hρ
  have hMi := TwoDShortResponse.integrable_modelDensity (sq_pos_of_pos hδ) a b
    (volume.real (twoDRegion h f)) (twoDBoundaryIntegral h f) c hk
  have hRi := hB.integrable_density_kernel hR (dimensionIntervalCoefficient_pos 2 (by norm_num)) hρ
  have hI : (∫ σ : ℝ in Ioi 0, dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ) *
      twoDShortOverlapDensity h f δ σ) =
      (∫ σ : ℝ in Ioi 0, TwoDShortResponse.modelDensity (δ ^ 2) a b (volume.real (twoDRegion h f))
        (twoDBoundaryIntegral h f) c σ * dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ)) +
      ∫ σ : ℝ in Ioi 0, TwoDShortRemainder.density R δ σ *
        dimensionKernel 2 (dimensionIntervalCoefficient 2 * ρ * σ) := by
    rw [← integral_add hMi hRi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro σ hσ
    dsimp only
    rw [he σ hσ]
    ring
  rw [hf.shortAction_eq_density ρ δ]
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  rw [hI]
  unfold TwoDShortResponse.modelAction
  ring

end SmoothTwoD
end BoundaryDraft
