import BoundaryDraft.ShortRadialQuadratic

/-!
# The indicator-fibre integral for the radial quadratic density

The proper-time cutoff restricts the positive long coordinate to the interval
from `sqrt σ` to the fixed cutoff. The fibre is absolutely integrable, and its
integral agrees with the existing closed radial density. No asymptotic or
geometric localization claim is added.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section
namespace BoundaryDraft

private theorem radial_fibre_eq_indicator (δ σ v : ℝ) (hv : v ∈ Ioo 0 δ) :
    (if σ ≤ v ^ 2 then
      ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2 else 0) =
      (Ico (Real.sqrt σ) δ).indicator
        (fun u => ((u - σ / u) ^ 2 / (8 * u)) * ((u - σ / u) / 2) ^ 2) v := by
  by_cases hs : σ ≤ v ^ 2
  · have hr : v ∈ Ico (Real.sqrt σ) δ :=
      ⟨Real.sqrt_le_iff.mpr ⟨hv.1.le, hs⟩, hv.2⟩
    simp only [if_pos hs, Set.indicator_of_mem hr]
  · have hr : v ∉ Ico (Real.sqrt σ) δ := by
      intro h
      exact hs (Real.sqrt_le_iff.mp h.1).2
    simp only [if_neg hs, Set.indicator_of_not_mem hr]

/-- Absolute integrability of the actual cutoff fibre. Positivity of proper time
keeps its support away from the apparent singularity at zero; `δ` may be arbitrary. -/
theorem integrableOn_shortRadialQuadratic_fibre (δ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => if σ ≤ v ^ 2 then
      ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2 else 0) (Ioo 0 δ) := by
  have hv (v : ℝ) (h : v ∈ Icc (Real.sqrt σ) δ) : v ≠ 0 :=
    ((Real.sqrt_pos.mpr hσ).trans_le h.1).ne'
  have hc : ContinuousOn (fun v : ℝ => v - σ / v) (Icc (Real.sqrt σ) δ) :=
    continuousOn_id.sub (continuousOn_const.div continuousOn_id hv)
  have hf : ContinuousOn
      (fun v : ℝ => ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2)
      (Icc (Real.sqrt σ) δ) :=
    ((hc.pow 2).div (continuousOn_const.mul continuousOn_id)
      (fun v h => mul_ne_zero (by norm_num) (hv v h))).mul ((hc.div_const 2).pow 2)
  have hi := ((hf.integrableOn_Icc (μ := volume)).mono_set
    Ico_subset_Icc_self).integrable_indicator measurableSet_Ico
  exact hi.integrableOn.congr_fun
    (fun v hv => (radial_fibre_eq_indicator δ σ v hv).symm) measurableSet_Ioo

/-- The actual indicator-fibre identity, including the empty-support regime.
The open/closed endpoint changes are Lebesgue-null. -/
theorem shortRadialQuadratic_eq_integral_fibre {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) :
    shortRadialQuadratic δ σ = ∫ v : ℝ in Ioo 0 δ, if σ ≤ v ^ 2 then
      ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2 else 0 := by
  have hset : Ico (Real.sqrt σ) δ ⊆ Ioo 0 δ := by
    intro v hv
    exact ⟨(Real.sqrt_pos.mpr hσ).trans_le hv.1, hv.2⟩
  have hi : (∫ v : ℝ in Ioo 0 δ, if σ ≤ v ^ 2 then
        ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2 else 0) =
      ∫ v : ℝ in Ico (Real.sqrt σ) δ,
        ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2 := by
    calc
      _ = ∫ v : ℝ in Ioo 0 δ, (Ico (Real.sqrt σ) δ).indicator
          (fun u => ((u - σ / u) ^ 2 / (8 * u)) * ((u - σ / u) / 2) ^ 2) v :=
        setIntegral_congr_fun measurableSet_Ioo (fun v hv => radial_fibre_eq_indicator δ σ v hv)
      _ = _ := by rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.mpr hset]
  rw [hi]
  by_cases hs : σ ≤ δ ^ 2
  · rw [shortRadialQuadratic_eq_integral hδ hσ hs,
      intervalIntegral.integral_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hs⟩),
      integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  · have hr : δ ≤ Real.sqrt σ := by
      by_contra! h
      exact hs (Real.sqrt_le_iff.mp h.le).2
    simp [shortRadialQuadratic, hs, Ico_eq_empty_of_le hr]

end BoundaryDraft
