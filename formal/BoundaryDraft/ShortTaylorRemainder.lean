import BoundaryDraft.CubicRemainderBounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# From an identified local two-jet to a measurable cubic remainder

This helper keeps geometric jet identification separate from the analytic
cancellation machinery. Equality of the actual first two derivatives is an
explicit intermediate obligation, not a new geometric admissibility field.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ShortNullRemainder

/-- Equal local C³ two-jets yield one measurable, cubically controlled
remainder on one fixed positive ball. -/
theorem exists_remainder_of_same_jet {F P : Space → ℝ}
    (hF : ContDiffAt ℝ 3 F 0) (hP : ContDiffAt ℝ 3 P 0)
    (h₀ : F 0 = P 0) (h₁ : fderiv ℝ F 0 = fderiv ℝ P 0)
    (h₂ : fderiv ℝ (fderiv ℝ F) 0 = fderiv ℝ (fderiv ℝ P) 0) :
    ∃ (R : Space → ℝ) (δ T : ℝ), Measurable R ∧ 0 < δ ∧ CubicBounds R δ T ∧
      ∀ z ∈ Metric.ball 0 δ, F z = P z + R z := by
  have hdF := hF.differentiableAt (by norm_num)
  have hdP := hP.differentiableAt (by norm_num)
  have hD₀ : (fun z => F z - P z) 0 = 0 := sub_eq_zero.mpr h₀
  have hD₁ : fderiv ℝ (fun z => F z - P z) 0 = 0 := by
    rw [fderiv_sub hdF hdP, h₁, sub_self]
  have he : fderiv ℝ (fun z => F z - P z) =ᶠ[𝓝 (0 : Space)]
      (fun z => fderiv ℝ F z - fderiv ℝ P z) := by
    filter_upwards [hF.eventually (by norm_num), hP.eventually (by norm_num)] with z hzF hzP
    exact fderiv_sub (hzF.differentiableAt (by norm_num)) (hzP.differentiableAt (by norm_num))
  have hD₂ : fderiv ℝ (fderiv ℝ (fun z => F z - P z)) 0 = 0 := by
    rw [he.fderiv_eq, fderiv_sub
      ((hF.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
      ((hP.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)), h₂, sub_self]
  obtain ⟨R, δ, T, hR, hδ, hB, hEq⟩ := exists_measurable_cubicRemainder (hF.sub hP) hD₀ hD₁ hD₂
  refine ⟨R, δ, T, hR, hδ, hB, ?_⟩
  intro z hz
  have hval := hEq hz
  change R z = F z - P z at hval
  linarith

private theorem hasFDerivAt_half_quadratic
    (B : Space →L[ℝ] Space →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (z : Space) :
    HasFDerivAt (fun x => (1 / 2 : ℝ) * B x x) (B z) z := by
  have hd := ((B.hasFDerivAt).clm_apply (hasFDerivAt_id z)).const_mul (1 / 2 : ℝ)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, id_eq, smul_eq_mul]
  rw [hB v z]
  ring

/-- The polynomial displayed by the geometric computation has exactly the
same first two derivatives. Symmetry is proved by Schwarz's theorem from
C³ regularity, not postulated for the geometric Hessian. -/
theorem same_jet_of_taylor_form {F P : Space → ℝ}
    (hF : ContDiffAt ℝ 3 F 0) (h₀ : F 0 = 0)
    (hP : ∀ z, P z = fderiv ℝ F 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ F) 0 z z) :
    F 0 = P 0 ∧ fderiv ℝ F 0 = fderiv ℝ P 0 ∧
      fderiv ℝ (fderiv ℝ F) 0 = fderiv ℝ (fderiv ℝ P) 0 := by
  let L := fderiv ℝ F 0
  let B := fderiv ℝ (fderiv ℝ F) 0
  have hsym : ∀ v w, B v w = B w v :=
    (hF.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).isSymmSndFDerivAt (by simp [minSmoothness])
  have he : P = fun z => L z + (1 / 2 : ℝ) * B z z := funext hP
  have hd (z : Space) : HasFDerivAt P (L + B z) z := by
    rw [he]
    exact L.hasFDerivAt.add (hasFDerivAt_half_quadratic B hsym z)
  have hD : fderiv ℝ P = fun z => L + B z := funext fun z => (hd z).fderiv
  refine ⟨?_, ?_, ?_⟩
  · simp [he, h₀]
  · rw [hD]
    simp [L]
  · rw [hD]
    have hh := ((hasFDerivAt_const L (0 : Space)).add B.hasFDerivAt).fderiv
    simpa only [zero_add] using hh.symm

end ShortNullRemainder
end BoundaryDraft
