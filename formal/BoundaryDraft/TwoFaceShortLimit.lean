import BoundaryDraft.TwoFaceAngularJet
import BoundaryDraft.ShortOverlapAsymptotics
import BoundaryDraft.TwoFaceShortReduction
import BoundaryDraft.ShortTaylorRemainder
import BoundaryDraft.ShortOverlapTaylor

/-!
# Short-limit assembly from the actual overlap remainder

This layer connects the geometric displacement jet derived from the original
admissibility class to the actual signed proper-time density. Every expansion
hypothesis in the intermediate helpers is discharged in the final existence
theorem. Fixed-cutoff independence then covers every positive fixed cutoff.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- The entire angular polynomial is retained until its full sphere average.
The sharp future-cone domain, including null displacements, is unchanged. -/
theorem angularExpansion_of_overlap_remainder
    {R : ShortNullRemainder.Space → ℝ} {δ : ℝ}
    (hjet : ∀ z ∈ Metric.ball (0 : ShortNullRemainder.Space) δ, ‖z.2‖ ≤ z.1 →
      translatedOverlap (twoFaceRegion h f) (Fin.cons z.1 z.2) -
        translatedOverlap (graphCapRegion h) (Fin.cons z.1 z.2) =
          twoFaceShortPolynomial h f z + R z) :
    ShortOverlapAsymptotics.AngularExpansion (twoFaceRegion h f) (graphCapRegion h)
      δ R (twoFaceShortCoefficient h f) := by
  intro σ hσ v hv hσv
  have hquot : 0 ≤ σ / v := div_nonneg hσ.le hv.1.le
  have hquotv : σ / v ≤ v := (div_le_iff₀ hv.1).mpr (by nlinarith only [hσv])
  have he (ω : OverlapSphere) :
      (translatedOverlap (twoFaceRegion h f) (properTimeDisplacement ω ![σ,v]) -
        translatedOverlap (graphCapRegion h) (properTimeDisplacement ω ![σ,v])) -
          R (ShortNullRemainder.point ω v σ) =
            twoFaceShortPolynomial h f ((v + σ / v) / 2, ((v - σ / v) / 2) • ω.val) := by
    have hp : ShortNullRemainder.point ω v σ ∈ Metric.ball (0 : ShortNullRemainder.Space) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (ShortNullRemainder.norm_point_le ω hv.1 ⟨hσ.le, hσv⟩).trans_lt hv.2
    have hc : ‖(ShortNullRemainder.point ω v σ).2‖ ≤ (ShortNullRemainder.point ω v σ).1 := by
      simp only [ShortNullRemainder.point, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ω.property, mul_one]
      rw [abs_of_nonneg (by linarith : 0 ≤ (v - σ / v) / 2)]
      linarith
    have hh := hjet _ hp hc
    change translatedOverlap (twoFaceRegion h f) (properTimeDisplacement ω ![σ,v]) -
      translatedOverlap (graphCapRegion h) (properTimeDisplacement ω ![σ,v]) =
        twoFaceShortPolynomial h f (ShortNullRemainder.point ω v σ) +
          R (ShortNullRemainder.point ω v σ) at hh
    rw [hh, add_sub_cancel_right]
    rfl
  rw [integral_congr_ae (Eventually.of_forall he)]
  exact hf.integral_overlapSphere_twoFaceShortPolynomial _ _

/-- A cubically controlled remainder for the actual overlap gives the
original short-action limit. The hypothesis is discharged by the local
geometric two-jet theorem, not added to `AdmissibleTwoFace`. -/
theorem short_limit_of_overlap_remainder
    {R : ShortNullRemainder.Space → ℝ} {δ T : ℝ} (hδ : 0 < δ)
    (hB : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    (hjet : ∀ z ∈ Metric.ball (0 : ShortNullRemainder.Space) δ, ‖z.2‖ ≤ z.1 →
      translatedOverlap (twoFaceRegion h f) (Fin.cons z.1 z.2) -
        translatedOverlap (graphCapRegion h) (Fin.cons z.1 z.2) =
          twoFaceShortPolynomial h f z + R z) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) := by
  have hl := ShortOverlapAsymptotics.bdg_action_limit hf.measurableSet_region hf.isBounded_region
    hf.toGraphCapData.measurableSet_cap hf.toGraphCapData.isBounded_cap hδ hB hR
      (hf.angularExpansion_of_overlap_remainder hjet)
  rw [hf.twoFaceShortCoefficient_identification] at hl
  simpa only [← add_sub_assoc, add_sub_cancel_left] using hf.short_limit_of_density_difference hδ hl

/-- The analytic assembly requires only an identified C³ overlap germ, not
any pre-assumed short-limit theorem or quantitative asymptotic rate. -/
theorem exists_short_limit_of_same_overlap_jet
    {F : ShortNullRemainder.Space → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hF : ContDiffAt ℝ 3 F 0)
    (h₀ : F 0 = twoFaceShortPolynomial h f 0)
    (h₁ : fderiv ℝ F 0 = fderiv ℝ (twoFaceShortPolynomial h f) 0)
    (h₂ : fderiv ℝ (fderiv ℝ F) 0 = fderiv ℝ (fderiv ℝ (twoFaceShortPolynomial h f)) 0)
    (hFeq : ∀ z ∈ Metric.ball (0 : ShortNullRemainder.Space) ε, ‖z.2‖ ≤ z.1 →
      F z = translatedOverlap (twoFaceRegion h f) (Fin.cons z.1 z.2) -
        translatedOverlap (graphCapRegion h) (Fin.cons z.1 z.2)) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) := by
  obtain ⟨R, d, T, hR, hd, hB, hEq⟩ := ShortNullRemainder.exists_remainder_of_same_jet hF
    ((hf.contDiff_twoFaceShortPolynomial.of_le le_top).contDiffAt) h₀ h₁ h₂
  refine ⟨min ε d, lt_min hε hd,
    hf.short_limit_of_overlap_remainder (lt_min hε hd) (hB.mono (min_le_right _ _)) hR ?_⟩
  intro z hz hc
  rw [← hFeq z (Metric.ball_subset_ball (min_le_left _ _) hz) hc]
  exact hEq z (Metric.ball_subset_ball (min_le_right _ _) hz)

/-- The short limit at one sufficiently small positive fixed cutoff, derived
from the actual overlap germ and its identified two-jet. No analytic premise
has been inserted into the original admissibility class. -/
theorem exists_shortContinuumMean_limit :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) := by
  obtain ⟨ε, hε, F, hF, hF₀, hP, hFeq⟩ := hf.exists_overlapDifference_taylorPolynomial
  obtain ⟨h₀, h₁, h₂⟩ := ShortNullRemainder.same_jet_of_taylor_form hF hF₀ hP
  exact hf.exists_short_limit_of_same_overlap_jet hε hF h₀ h₁ h₂ hFeq

/-- Every fixed positive cutoff has the same limit. This uses exact
recombination and the proved fixed-cutoff long cancellation, not a uniform
estimate or a density-dependent cutoff limit. -/
theorem shortContinuumMean_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f)) := by
  obtain ⟨ε, hε, hs⟩ := hf.exists_shortContinuumMean_limit
  simpa only [zero_add, sub_add_cancel] using (hf.tendsto_short_sub_short hδ hε).add hs

end AdmissibleTwoFace
end BoundaryDraft
