import BoundaryDraft.TwoFaceAssembly
import BoundaryDraft.ShortOverlapDensity

/-!
# Reduction to the curved-minus-planar short density

The planar comparison has exactly the same spacetime volume. These identities
retain the original sharp cutoff and the entire signed BDG kernel. The limit
of the difference density is still an analytic obligation, not a hypothesis in
`AdmissibleTwoFace`.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The vertex overlap is the actual spacetime volume. -/
theorem translatedOverlap_at_zero {M : Set Spacetime} (hm : MeasurableSet M) :
    translatedOverlap M 0 = volume.real M := by
  rw [translatedOverlap]
  calc
    _ = ∫ _x in M, (1 : ℝ) := setIntegral_congr_fun hm (fun x hx => by simp [hx])
    _ = volume.real M := by simp

theorem integral_shortOverlapDensity_eq_Ioi (M : Set Spacetime) (δ : ℝ) (w : ℝ → ℝ) :
    (∫ σ : ℝ, w σ * shortOverlapDensity M δ σ) =
      ∫ σ : ℝ in Ioi 0, w σ * shortOverlapDensity M δ σ := by
  rw [← integral_Ici_eq_integral_Ioi]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro σ hσ
  have hneg : σ < 0 := lt_of_not_ge hσ
  simp [shortOverlapDensity, shortOverlapDensityENN_negative M δ hneg]

namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- Vertical translation of each fibre preserves the region volume. -/
theorem volume_region_eq_planar : volume.real (twoFaceRegion h f) = volume.real (graphCapRegion h) := by
  have hz : Fin.cons (0 : ℝ) (0 : Spatial) = (0 : Spacetime) := by ext i; fin_cases i <;> rfl
  have hm : Fin.cons (0 : ℝ) (0 : Spatial) ∈ causalFuture 0 := by
    rw [hz]
    exact causalFuture_refl _
  have he := hf.translatedOverlap_causal hm
  have hp := hf.toGraphCapData.translatedOverlap_causal hm
  rw [hz, translatedOverlap_at_zero hf.measurableSet_region] at he
  rw [hz, translatedOverlap_at_zero hf.toGraphCapData.measurableSet_cap] at hp
  rw [he, hp]
  congr 1
  ext x
  simp

/-- The point terms cancel exactly, before any asymptotic manipulation. -/
theorem shortContinuumMean_sub_planar (ρ δ : ℝ) :
    shortContinuumMean ρ δ (twoFaceRegion h f) - shortContinuumMean ρ δ (graphCapRegion h) =
      -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
        (shortOverlapDensity (twoFaceRegion h f) δ σ - shortOverlapDensity (graphCapRegion h) δ σ) *
          bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) := by
  let w := fun σ : ℝ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)
  have hw : Continuous w := by unfold w bdgKernel bdgPolynomial; fun_prop
  have hi := (integrable_shortOverlapDensity_weight hf.measurableSet_region hf.isBounded_region δ w hw).restrict (s := Ioi 0)
  have hip := (integrable_shortOverlapDensity_weight hf.toGraphCapData.measurableSet_cap
    hf.toGraphCapData.isBounded_cap δ w hw).restrict (s := Ioi 0)
  rw [hf.shortContinuumMean_eq_density,
    BoundaryDraft.shortContinuumMean_eq_density hf.toGraphCapData.measurableSet_cap
      hf.toGraphCapData.isBounded_cap, hf.volume_region_eq_planar,
    integral_shortOverlapDensity_eq_Ioi, integral_shortOverlapDensity_eq_Ioi]
  have he : (∫ σ : ℝ in Ioi 0,
      (shortOverlapDensity (twoFaceRegion h f) δ σ - shortOverlapDensity (graphCapRegion h) δ σ) * w σ) =
      (∫ σ : ℝ in Ioi 0, w σ * shortOverlapDensity (twoFaceRegion h f) δ σ) -
        ∫ σ : ℝ in Ioi 0, w σ * shortOverlapDensity (graphCapRegion h) δ σ := by
    simp_rw [mul_comm _ (w _), mul_sub]
    exact integral_sub hi hip
  rw [he]
  ring

/-- A proved density difference limit combines with the existing planar limit.
This assembly lemma does not supply the missing geometric asymptotic theorem. -/
theorem short_limit_of_density_difference {δ L : ℝ} (hδ : 0 < δ)
    (hlim : Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ σ : ℝ in Ioi 0,
        (shortOverlapDensity (twoFaceRegion h f) δ σ - shortOverlapDensity (graphCapRegion h) δ σ) *
          bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) atTop (𝓝 L)) :
    Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
      (𝓝 (graphBoundaryIntegral h + L)) := by
  have ht := (hf.toAdmissibleGraphCap.shortContinuumMean_limit hδ).add hlim
  apply ht.congr'
  filter_upwards with ρ
  rw [← hf.shortContinuumMean_sub_planar ρ δ]
  ring

end AdmissibleTwoFace
end BoundaryDraft
