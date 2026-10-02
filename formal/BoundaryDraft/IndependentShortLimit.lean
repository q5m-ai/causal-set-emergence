import BoundaryDraft.IndependentShortAngular

/-!
# Actual class-E fixed-cutoff short limit

Signed Fubini and the four radial basis terms connect the geometric producer
to the checked absolute analytic backend. Every sufficiently small FIXED
positive cutoff works. No long-density theorem, full-action limit or Poisson
limit is asserted here.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft
namespace AbsoluteShortModel

private theorem integral_cutoff_fibre {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) (Q : ℝ → ℝ) :
    (∫ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then Q v else 0) =
      ∫ v in (Real.sqrt σ)..δ, Q v := by
  have hset : Ico (Real.sqrt σ) δ ⊆ Ioo 0 δ :=
    fun v hv => ⟨(Real.sqrt_pos.mpr hσ).trans_le hv.1, hv.2⟩
  calc
    _ = ∫ v in Ioo (0 : ℝ) δ, (Ico (Real.sqrt σ) δ).indicator Q v := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro v hv
      dsimp only
      by_cases h : σ ≤ v ^ 2
      · rw [if_pos h, indicator_of_mem (show v ∈ Ico (Real.sqrt σ) δ from
          ⟨Real.sqrt_le_iff.mpr ⟨hv.1.le, h⟩, hv.2⟩)]
      · rw [if_neg h, indicator_of_not_mem (show v ∉ Ico (Real.sqrt σ) δ from
          fun hh => h (Real.sqrt_le_iff.mp hh.1).2)]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.mpr hset,
        intervalIntegral.integral_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hs⟩),
        integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

/-- All four actual radial basis responses, including the empty-support case.
The moving lower endpoint is kept by interval integration, not dropped. -/
theorem density_eq_integral_fibre {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (V ℓ α β : ℝ) :
    density δ V ℓ α β σ = ∫ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then
      ShortNullRemainder.jacobian v σ * (4 * Real.pi * V + ℓ * ((v + σ / v) / 2) +
        α * ((v + σ / v) / 2) ^ 2 + β * ((v - σ / v) / 2) ^ 2) else 0 := by
  by_cases hs : σ ≤ δ ^ 2
  · rw [integral_cutoff_fibre hδ hσ hs]
    let J : ℝ → ℝ := fun v => ShortNullRemainder.jacobian v σ
    let t : ℝ → ℝ := fun v => (v + σ / v) / 2
    let r : ℝ → ℝ := fun v => (v - σ / v) / 2
    have hv (v : ℝ) (hv : v ∈ uIcc (Real.sqrt σ) δ) : v ≠ 0 := by
      rw [uIcc_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hs⟩)] at hv
      exact ((Real.sqrt_pos.mpr hσ).trans_le hv.1).ne'
    have hd : ContinuousOn (fun v : ℝ => σ / v) (uIcc (Real.sqrt σ) δ) :=
      continuousOn_const.div continuousOn_id hv
    have ht : ContinuousOn t (uIcc (Real.sqrt σ) δ) := (continuousOn_id.add hd).div_const 2
    have hr : ContinuousOn r (uIcc (Real.sqrt σ) δ) := (continuousOn_id.sub hd).div_const 2
    have hJ : ContinuousOn J (uIcc (Real.sqrt σ) δ) :=
      ((continuousOn_id.sub hd).pow 2).div (continuousOn_const.mul continuousOn_id)
        (fun v hh => mul_ne_zero (by norm_num) (hv v hh))
    have h₀ := (hJ.intervalIntegrable (μ := volume)).const_mul (4 * Real.pi * V)
    have h₁ := ((hJ.mul ht).intervalIntegrable (μ := volume)).const_mul ℓ
    have h₂ := ((hJ.mul (ht.pow 2)).intervalIntegrable (μ := volume)).const_mul α
    have h₃ := ((hJ.mul (hr.pow 2)).intervalIntegrable (μ := volume)).const_mul β
    have he (v : ℝ) : ShortNullRemainder.jacobian v σ *
        (4 * Real.pi * V + ℓ * ((v + σ / v) / 2) + α * ((v + σ / v) / 2) ^ 2 +
          β * ((v - σ / v) / 2) ^ 2) =
        ((4 * Real.pi * V) * J v + ℓ * (J v * t v)) +
          α * (J v * t v ^ 2) + β * (J v * r v ^ 2) := by dsimp [J, t, r]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
      intervalIntegral.integral_add (h₀.add h₁) h₂, intervalIntegral.integral_add h₀ h₁]
    simp only [intervalIntegral.integral_const_mul]
    rw [density, shortRadialConstant_eq_integral hδ hσ hs, shortRadialTime_eq_integral hδ hσ hs,
      shortRadialTimeSquare_eq_integral hδ hσ hs, shortRadialQuadratic_eq_integral hδ hσ hs]
    rfl
  · have hz : density δ V ℓ α β σ = 0 := by
      simp [density, shortRadialConstant, shortRadialTime, shortRadialTimeSquare, shortRadialQuadratic, hs]
    rw [hz]
    symm
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    have hvs : ¬σ ≤ v ^ 2 := by
      intro h
      exact hs (h.trans (sq_le_sq₀ hv.1.le hδ.le |>.mpr hv.2.le))
    simp only [if_neg hvs]

/-- Pointwise decomposition of the EXISTING nonnegative short overlap density.
Both product integrands are absolutely integrable before signed subtraction
and exchange of the angular and long-coordinate integrals. -/
theorem actual_density_decomposition {M : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    {R : Displacement → ℝ} {δ T V ℓ α β : ℝ} (hδ : 0 < δ)
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    (ha : AngularExpansion M δ R V ℓ α β) {σ : ℝ} (hσ : 0 < σ) :
    shortOverlapDensity M δ σ = density δ V ℓ α β σ + ShortNullRemainder.density R δ σ := by
  let μ := overlapSphereMeasure.prod (volume.restrict (Ioo (0 : ℝ) δ))
  let F : OverlapSphere × ℝ → ℝ := fun p =>
    shortOverlapFibre M σ p.1 p.2 - ShortOverlapAsymptotics.remainderFibre R σ p.1 p.2
  have hiM := integrable_shortOverlapFibre hm hb δ hσ.le
  have hiR := ShortOverlapAsymptotics.integrable_remainderFibre h hR hσ.le
  have hiF : Integrable F μ := hiM.sub hiR
  have hdM : shortOverlapDensity M δ σ = ∫ p, shortOverlapFibre M σ p.1 p.2 ∂μ :=
    (shortOverlapDensity_eq_average hm hb δ hσ.le).trans (integral_prod _ hiM).symm
  have hdR : ShortNullRemainder.density R δ σ =
      ∫ p, ShortOverlapAsymptotics.remainderFibre R σ p.1 p.2 ∂μ :=
    (h.density_eq_iterated hR hσ.le).trans (integral_prod _ hiR).symm
  have he : shortOverlapDensity M δ σ - ShortNullRemainder.density R δ σ = density δ V ℓ α β σ := by
    calc
      _ = ∫ p, F p ∂μ := by rw [hdM, hdR, ← integral_sub hiM hiR]
      _ = ∫ v in Ioo (0 : ℝ) δ, ∫ ω, F (ω, v) ∂overlapSphereMeasure := integral_prod_symm _ hiF
      _ = density δ V ℓ α β σ := by
        rw [density_eq_integral_fibre hδ hσ]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro v hv
        by_cases hs : σ ≤ v ^ 2
        · have hp (ω : OverlapSphere) : F (ω, v) = ShortNullRemainder.jacobian v σ *
              (translatedOverlap M (properTimeDisplacement ω ![σ,v]) - R (ShortNullRemainder.point ω v σ)) := by
            dsimp only [F, shortOverlapFibre, ShortOverlapAsymptotics.remainderFibre]
            rw [if_pos hs, if_pos hs]
            dsimp only [ShortNullRemainder.jacobian]
            ring
          simp_rw [hp]
          rw [integral_const_mul, ha σ hσ v hv hs, if_pos hs]
        · have hp (ω : OverlapSphere) : F (ω, v) = 0 := by
            simp [F, shortOverlapFibre, ShortOverlapAsymptotics.remainderFibre, hs]
          simp only [hp, integral_zero, if_neg hs]
  linarith

end AbsoluteShortModel

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- The exact density decomposition and primitive bounds are both produced
from class E. One measurable remainder works at every smaller positive cutoff. -/
theorem exists_shortOverlapDensity_decomposition :
    ∃ (R : Displacement → ℝ) (δ₀ T : ℝ), Measurable R ∧ 0 < δ₀ ∧
      ShortNullRemainder.CubicBounds R δ₀ T ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ σ : ℝ, 0 < σ →
        shortOverlapDensity (twoFaceRegion h f) δ σ =
          AbsoluteShortModel.density δ (volume.real (twoFaceRegion h f))
            (-4 * Real.pi * volume.real {x : JointSpace | 0 < h x})
            (2 * Real.pi * graphBoundaryIntegral h) (twoFaceShortCoefficient h f) σ +
              ShortNullRemainder.density R δ σ := by
  obtain ⟨R, δ₀, T, hR, hδ₀, hB, ha⟩ := hf.exists_absoluteAngularExpansion
  refine ⟨R, δ₀, T, hR, hδ₀, hB, ?_⟩
  intro δ hδ hδle σ hσ
  exact AbsoluteShortModel.actual_density_decomposition hf.measurableSet_region hf.isBounded_region
    hδ (hB.mono hδle) hR
    (fun σ hσ v hv hs => ha σ hσ v ⟨hv.1, hv.2.trans_le hδle⟩ hs) hσ

/-- The actual class-E short observable tends to the UNCHANGED independent
intrinsic joint target at every sufficiently small fixed positive cutoff.
Neither a same-height cap nor a long-density result is needed. -/
theorem exists_shortContinuumMean_limit :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun ρ => shortContinuumMean ρ δ (twoFaceRegion h f)) atTop
        (𝓝 (twoFaceBoundaryIntegral h f)) := by
  obtain ⟨R, δ₀, T, hR, hδ₀, hB, hdecomp⟩ := hf.exists_shortOverlapDensity_decomposition
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle
  have hb := hB.mono hδle
  have hl := AbsoluteShortModel.action_limit_of_remainder hδ hR hb
    (shortOverlapDensity (twoFaceRegion h f) δ) (volume.real (twoFaceRegion h f))
    (-4 * Real.pi * volume.real {x : JointSpace | 0 < h x})
    (2 * Real.pi * graphBoundaryIntegral h) (twoFaceShortCoefficient h f)
    (hdecomp δ hδ hδle)
  rw [hf.absoluteShortCoefficient_identification] at hl
  apply hl.congr'
  filter_upwards with ρ
  rw [shortContinuumMean_eq_density hf.measurableSet_region hf.isBounded_region,
    integral_shortOverlapDensity_eq_Ioi]
  congr 3
  apply setIntegral_congr_fun measurableSet_Ioi
  intro σ _
  ring

end AdmissibleIndependentTwoFace
end BoundaryDraft
