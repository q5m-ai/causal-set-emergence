import BoundaryDraft.TwoDCubicBounds
import BoundaryDraft.TwoDShortCoordinates
import BoundaryDraft.TruncatedLinearJet

/-!
# Nearly-null transport of the actual 2D cubic remainder

The constant-in-proper-time Jacobian is `1/(2*v)`. Value, first derivative and
second derivative bounds become `T*v²`, `T`, `T/v²`. The inverse-square bound
is NOT integrated by itself: the closing-fibre cutoff compensates it.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDShortRemainder

def point (ω : TwoDDirection) (v σ : ℝ) : Space :=
  ((v + σ / v) / 2, ((v - σ / v) / 2) • ω.val)

theorem point_eq_properTimeDisplacement (ω : TwoDDirection) (v σ : ℝ) :
    point ω v σ = twoDProperTimeDisplacement ω ![σ,v] := rfl

def direction (ω : TwoDDirection) (v : ℝ) : Space :=
  (1 / (2 * v), (-(1 / (2 * v))) • ω.val)

def fibre (R : Space → ℝ) (ω : TwoDDirection) (v σ : ℝ) : ℝ :=
  twoDNullJacobian σ v * R (point ω v σ)

def first (R : Space → ℝ) (ω : TwoDDirection) (v σ : ℝ) : ℝ :=
  (1 / (2 * v)) * fderiv ℝ R (point ω v σ) (direction ω v)

def second (R : Space → ℝ) (ω : TwoDDirection) (v σ : ℝ) : ℝ :=
  (1 / (2 * v)) * fderiv ℝ (fderiv ℝ R) (point ω v σ) (direction ω v) (direction ω v)

theorem hasDerivAt_point (ω : TwoDDirection) (v σ : ℝ) :
    HasDerivAt (point ω v) (direction ω v) σ := by
  have ht := ((hasDerivAt_const σ v).add ((hasDerivAt_id σ).div_const v)).div_const 2
  have hr := (((hasDerivAt_const σ v).sub ((hasDerivAt_id σ).div_const v)).div_const 2).smul_const ω.val
  convert ht.prodMk hr using 1
  apply Prod.ext
  · dsimp only [direction]; ring
  · change (-(1 / (2 * v))) • ω.val = ((0 - 1 / v) / 2) • ω.val
    congr 1
    ring

theorem norm_direction (ω : TwoDDirection) {v : ℝ} (hv : 0 < v) :
    ‖direction ω v‖ = 1 / (2 * v) := by
  simp only [direction, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_neg,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, max_self]
  exact abs_of_pos (by positivity)

theorem norm_point_le (ω : TwoDDirection) {v σ : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖point ω v σ‖ ≤ v := by
  have hquot : 0 ≤ σ / v := div_nonneg hσ.1 hv.le
  have hquotv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith only [hσ.2])
  simp only [point, Prod.norm_def, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, max_le_iff]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem point_causal (ω : TwoDDirection) {v σ : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖(point ω v σ).2‖ ≤ (point ω v σ).1 := by
  have hquot : 0 ≤ σ / v := div_nonneg hσ.1 hv.le
  have hquotv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith only [hσ.2])
  simp only [point, norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp ω.property, mul_one]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem hasDerivAt_fibre {R : Space → ℝ} (ω : TwoDDirection) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ)) :
    HasDerivAt (fibre R ω v) (first R ω v σ) σ :=
  (hR.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_point ω v σ)).const_mul _

theorem hasDerivAt_first {R : Space → ℝ} (ω : TwoDDirection) (v σ : ℝ)
    (hR : DifferentiableAt ℝ (fderiv ℝ R) (point ω v σ)) :
    HasDerivAt (first R ω v) (second R ω v σ) σ := by
  have hd := (hR.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_point ω v σ)).clm_apply
    (hasDerivAt_const σ (direction ω v))
  simpa only [map_zero, add_zero] using hd.const_mul (1 / (2 * v))

namespace CubicBounds
variable {R : Space → ℝ} {δ T : ℝ} (h : CubicBounds R δ T)
include h

omit h in
theorem point_mem (ω : TwoDDirection) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) : point ω v σ ∈ Metric.ball (0 : Space) δ := by
  simpa only [Metric.mem_ball, dist_zero_right] using (norm_point_le ω hv.1 hσ).trans_lt hv.2

theorem point_bounds (ω : TwoDDirection) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖R (point ω v σ)‖ ≤ T * v ^ 3 ∧
    ‖fderiv ℝ R (point ω v σ)‖ ≤ T * v ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ ≤ T * v := by
  have hp := point_mem ω hv hσ
  have hn := norm_point_le ω hv.1 hσ
  have hT := h.nonneg
  refine ⟨(h.value _ hp).trans ?_, (h.first _ hp).trans ?_, (h.second _ hp).trans ?_⟩ <;> gcongr

theorem fibre_deriv (ω : TwoDDirection) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) : HasDerivAt (fibre R ω v) (TwoDShortRemainder.first R ω v σ) σ :=
  hasDerivAt_fibre ω v σ ((h.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
    (point_mem ω hv hσ))).differentiableAt (by norm_num))

theorem first_deriv (ω : TwoDDirection) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) : HasDerivAt (TwoDShortRemainder.first R ω v) (TwoDShortRemainder.second R ω v σ) σ := by
  have hs := h.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds (point_mem ω hv hσ))
  exact hasDerivAt_first ω v σ ((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem bounds (ω : TwoDDirection) {v σ : ℝ} (hv : v ∈ Ioo 0 δ) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    |fibre R ω v σ| ≤ T * v ^ 2 ∧ |TwoDShortRemainder.first R ω v σ| ≤ T ∧
      |TwoDShortRemainder.second R ω v σ| ≤ T / v ^ 2 := by
  obtain ⟨h₀, h₁, h₂⟩ := h.point_bounds ω hv hσ
  have hj : 0 ≤ 1 / (2 * v) := one_div_nonneg.mpr (mul_nonneg (by norm_num) hv.1.le)
  have hA : ‖fderiv ℝ R (point ω v σ) (direction ω v)‖ ≤ T * v ^ 2 * (1 / (2 * v)) := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    rw [norm_direction ω hv.1]
    exact mul_le_mul_of_nonneg_right h₁ hj
  have hAA : ‖fderiv ℝ (fderiv ℝ R) (point ω v σ) (direction ω v) (direction ω v)‖ ≤
      T * v * (1 / (2 * v)) * (1 / (2 * v)) := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)).trans
    rw [norm_direction ω hv.1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ hj) hj
  have he₀ : (1 / (2 * v)) * (T * v ^ 3) = T * v ^ 2 / 2 := by field_simp [hv.1.ne']; ring
  have he₁ : (1 / (2 * v)) * (T * v ^ 2 * (1 / (2 * v))) = T / 4 := by field_simp [hv.1.ne']; ring
  have he₂ : (1 / (2 * v)) * (T * v * (1 / (2 * v)) * (1 / (2 * v))) = (T / v ^ 2) / 8 := by
    field_simp [hv.1.ne']; ring
  simp only [fibre, TwoDShortRemainder.first, TwoDShortRemainder.second, twoDNullJacobian, abs_mul, abs_of_nonneg hj]
  refine ⟨?_, ?_, ?_⟩
  · apply (mul_le_mul_of_nonneg_left h₀ hj).trans
    rw [he₀]
    linarith [mul_nonneg h.nonneg (sq_nonneg v)]
  · apply (mul_le_mul_of_nonneg_left hA hj).trans
    rw [he₁]
    linarith [h.nonneg]
  · apply (mul_le_mul_of_nonneg_left hAA hj).trans
    rw [he₂]
    linarith [div_nonneg h.nonneg (sq_nonneg v)]

end CubicBounds
end TwoDShortRemainder
end BoundaryDraft
