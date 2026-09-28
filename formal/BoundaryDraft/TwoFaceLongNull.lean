import BoundaryDraft.TwoFaceOverlap
import BoundaryDraft.NullTransverseCancellation

/-!
# Conditional assembly for the actual long-overlap contribution

This discharges the ancillary geometric inputs and the half-line endpoint
replacement. The right quadratic jet remains an EXPLICIT UNPROVED hypothesis;
this file does not resolve #61 or prove geometric long-null cancellation.
No condition is added to admissibility and no density representative is changed.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- The actual density vanishes on the negative half-line. Its point value at
zero need not be identified with any expansion coefficient. -/
theorem integral_longOverlapDensity_eq_Ioi (M : Set Spacetime) (δ : ℝ) (w : ℝ → ℝ) :
    (∫ σ : ℝ, w σ * longOverlapDensity M δ σ) =
      ∫ σ : ℝ in Ioi 0, w σ * longOverlapDensity M δ σ := by
  rw [← integral_Ici_eq_integral_Ioi]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro σ hσ
  have hneg : σ < 0 := lt_of_not_ge hσ
  simp [longOverlapDensity, longOverlapDensityENN_negative M δ hneg]

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- Absolute integrability of the original long-displacement overlap integrand,
with the complete signed kernel and its unchanged interval coefficient. -/
theorem integrableOn_longOverlap_bdg (δ ρ : ℝ) :
    IntegrableOn (fun z => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) (longFuture δ) := by
  apply (hf.integrableOn_overlap_weight _ (by
    unfold bdgKernel bdgPolynomial intervalSq spatialSeparationSq
    fun_prop)).mono_set
  exact fun _ hz => hz.1

/-- Exact positive-half-line version of the existing whole-line identity.
Atomlessness removes only the endpoint, not any surrounding near-null layer. -/
theorem integral_longOverlap_bdg_Ioi {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ in Ioi 0, longOverlapDensity (twoFaceRegion h f) δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) := by
  rw [hf.integral_longOverlap_bdg hδ ρ, integral_longOverlapDensity_eq_Ioi]
  congr 1
  funext σ
  exact mul_comm _ _

/-- Absolute integrability on the half-line is discharged from geometry, not
left to a future caller of the conditional cancellation theorem. -/
theorem integrableOn_longOverlapDensity_bdg (δ ρ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ *
      bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (Ioi 0) := by
  have hi := hf.integrable_longOverlapDensity_weight hδ
    (fun σ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) (by
      unfold bdgKernel bdgPolynomial
      fun_prop)
  simpa only [mul_comm] using hi.integrableOn (s := Ioi 0)

/-- CONDITIONAL geometric assembly: the actual averaged density's right jet is
the one remaining input. In particular this is not a proof of that input. -/
theorem tendsto_longOverlap_of_quadratic_jet {δ : ℝ} (hδ : 0 < δ)
    (hjet : ∃ b₀ b₁ b₂ : ℝ,
      (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
        (b₀ + b₁ * σ + b₂ * σ ^ 2)) =o[𝓝[>] (0 : ℝ)] (fun σ => σ ^ 2)) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  obtain ⟨b₀, b₁, b₂, hj⟩ := hjet
  obtain ⟨C, _, hC⟩ := hf.bounded_longOverlapDensity hδ
  have he := bdgKernel_transverse_cancellation
    (longOverlapDensity (twoFaceRegion h f) δ) (hf.measurable_longOverlapDensity δ)
    C (fun σ _ => by simpa only [Real.norm_eq_abs] using hC σ)
    b₀ b₁ b₂ hj (Real.pi / 24) (by positivity)
  simpa only [← hf.integral_longOverlap_bdg_Ioi hδ] using he

/-- The signed contribution in the original action has BOTH density factors.
The point term and the short-displacement pair term are not included here. -/
theorem tendsto_normalized_longOverlap_of_quadratic_jet {δ : ℝ} (hδ : 0 < δ)
    (hjet : ∃ b₀ b₁ b₂ : ℝ,
      (fun σ => longOverlapDensity (twoFaceRegion h f) δ σ -
        (b₀ + b₁ * σ + b₂ * σ ^ 2)) =o[𝓝[>] (0 : ℝ)] (fun σ => σ ^ 2)) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
        translatedOverlap (twoFaceRegion h f) z) atTop (𝓝 0) := by
  have he := (hf.tendsto_longOverlap_of_quadratic_jet hδ hjet).const_mul
    (-(4 / Real.sqrt 6))
  simp only [mul_zero] at he
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hp : ρ ^ (3 / 2 : ℝ) = Real.sqrt ρ * ρ := by
    calc
      _ = ρ ^ ((1 / 2 : ℝ) + 1) := by congr 1; norm_num
      _ = ρ ^ (1 / 2 : ℝ) * ρ ^ (1 : ℝ) := Real.rpow_add hρ _ _
      _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
  rw [hp]
  ring

end AdmissibleTwoFace
end BoundaryDraft
