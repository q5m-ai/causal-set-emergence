import BoundaryDraft.TwoFaceLongDisintegration
import BoundaryDraft

/-! Pointwise exact finite-density regressions; no quadratic jet is assumed. -/

open BoundaryDraft MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace TwoFaceLongDisintegrationRegression

example : overlapSphereMeasure.real univ = 4 * Real.pi := overlapSphere_mass

example : max (1 / 4 : ℝ) (Real.sqrt 0) = 1 / 4 :=
  max_cutoff_sqrt_eq (by norm_num) (by norm_num) (by norm_num)

example : max (1 / 4 : ℝ) (Real.sqrt (1 / 32)) = 1 / 4 :=
  max_cutoff_sqrt_eq (by norm_num) (by norm_num) (by norm_num)

private def cap : Spatial → ℝ := ellipsoidProfile (1 / 4) ![1, 2, 3]

private theorem admissible_cap : AdmissibleGraphCap cap := by
  exact ellipsoid_admissible _ _ (by norm_num)
    (fun i => by fin_cases i <;> norm_num)

-- Endpoint and positive parameter, strictly inside the same right neighborhood.
example (ω : OverlapSphere) :
    ENNReal.ofReal (∫ x : Spatial, max 0 (twoFaceRayGap cap (fun _ => 0) x ω 0 1)) =
      ∫⁻ x : Spatial, ENNReal.ofReal (max 0 (twoFaceRayGap cap (fun _ => 0) x ω 0 1)) := by
  exact admissible_cap.twoFace_planar.ofReal_integral_gap_eq_lintegral
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) (by norm_num) (by norm_num) ω

example (ω : OverlapSphere) :
    (∫⁻ x : Spatial, ENNReal.ofReal
      (max 0 (twoFaceRayGap cap (fun _ => 0) x ω (1 / 32) 1))) < ⊤ := by
  exact admissible_cap.twoFace_planar.lintegral_gap_lt_top
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) (by norm_num) (by norm_num) ω

example : longOverlapDensity (twoFaceRegion cap (fun _ => 0)) (1 / 4) (1 / 32) =
    ∫ ω, (∫ x : Spatial, ∫ v in Ici (1 / 4 : ℝ),
      ((v - (1 / 32 : ℝ) / v)^2 / (8*v)) *
        max 0 (twoFaceRayGap cap (fun _ => 0) x ω (1 / 32) v))
        ∂overlapSphereMeasure := by
  exact admissible_cap.twoFace_planar.longOverlapDensity_eq_gap_fibres
    (by norm_num) (by norm_num) (by norm_num)

-- A truly curved future face, retaining the existing nonaffinity witness.
theorem curved_fibre : ∃ c : ℝ, 0 < c ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 ∧
    longOverlapDensity (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4))
      (twoFaceSine c)) (1 / 4) 0 =
      ∫ ω, (∫ x : Spatial, ∫ v in Ici (1 / 4 : ℝ),
        ((v - (0 : ℝ) / v)^2 / (8*v)) * max 0
          (twoFaceRayGap (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c)
            x ω 0 v)) ∂overlapSphereMeasure := by
  obtain ⟨c, hc, hf, _, hcurve⟩ := twoFace_curved_nonvacuity
  exact ⟨c, hc, hcurve, hf.longOverlapDensity_eq_gap_fibres
    (by norm_num) (by norm_num) (by norm_num)⟩

-- Upper clearance is a premise, not inferred from a mere finite cutoff.
-- This checks agreement with the untruncated real fibre at a nonzero σ.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    (hclear : ∀ (ω : OverlapSphere) (x : Spatial) (v : ℝ), 10 < v →
      twoFaceRayGap h f x ω (1 / 32) v ≤ 0) :
    (∫ ω, (∫ x : Spatial, ∫ v in Ici (1 / 4 : ℝ),
      ((v - (1 / 32 : ℝ) / v)^2 / (8*v)) *
        max 0 (twoFaceRayGap h f x ω (1 / 32) v)) ∂overlapSphereMeasure) =
    ∫ ω, (∫ x : Spatial, ∫ v in Icc (1 / 4 : ℝ) 10,
      ((v - (1 / 32 : ℝ) / v)^2 / (8*v)) *
        max 0 (twoFaceRayGap h f x ω (1 / 32) v)) ∂overlapSphereMeasure := by
  calc
    _ = longOverlapDensity (twoFaceRegion h f) (1 / 4) (1 / 32) :=
      (hf.longOverlapDensity_eq_gap_fibres (by norm_num) (by norm_num) (by norm_num)).symm
    _ = _ := hf.longOverlapDensity_eq_gap_fibres_Icc (by norm_num) (by norm_num)
      (by norm_num) hclear

-- Zero-volume and empty sets have the unchanged zero density at every parameter.
example (δ σ : ℝ) : longOverlapDensity (∅ : Set Spacetime) δ σ = 0 := by
  exact longOverlapDensity_zero_of_volume_zero (by simp) δ σ

example {M : Set Spacetime} (hM : volume M = 0) (δ σ : ℝ) :
    longOverlapDensity M δ σ = 0 :=
  longOverlapDensity_zero_of_volume_zero hM δ σ

end TwoFaceLongDisintegrationRegression
