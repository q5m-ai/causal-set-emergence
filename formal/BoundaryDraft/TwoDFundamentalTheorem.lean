import BoundaryDraft.TwoDComponents
import BoundaryDraft.TwoDEndpointCoefficient
import BoundaryDraft.TwoDMovingEndpoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Oriented FTC on every positive interval, retaining the complete frontier -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The actual one-dimensional future Hessian, in the unit real coordinate. -/
def twoDFutureHessian (f : TwoDSpace → ℝ) (x : TwoDSpace) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (twoDLine.symm 1) (twoDLine.symm 1)

namespace TwoDIntervalFamily
variable {h : TwoDSpace → ℝ} (A : TwoDIntervalFamily h)

theorem left_mem_joint (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
    twoDLine.symm p.1 ∈ dimensionTwoSpatialJoint h := by
  obtain ⟨x, hx, he⟩ := (A.ends p hp).1
  simpa only [← he, twoDLine.symm_apply_apply] using hx

theorem right_mem_joint (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
    twoDLine.symm p.2 ∈ dimensionTwoSpatialJoint h := by
  obtain ⟨x, hx, he⟩ := (A.ends p hp).2
  simpa only [← he, twoDLine.symm_apply_apply] using hx

theorem positive_on_interval (p : ℝ × ℝ) (hp : p ∈ A.intervals) {s : ℝ} (hs : s ∈ Ioo p.1 p.2) :
    0 < h (twoDLine.symm s) := by
  apply (mem_twoDPositiveLine h s).mp
  rw [A.positive]
  exact mem_iUnion₂.mpr ⟨p, hp, hs⟩

theorem interval_mem_closedPositive (p : ℝ × ℝ) (hp : p ∈ A.intervals)
    {s : ℝ} (hs : s ∈ Icc p.1 p.2) : twoDLine.symm s ∈ twoDClosedPositive h := by
  by_cases ha : s = p.1
  · rw [ha]; exact (A.left_mem_joint p hp).1
  by_cases hb : s = p.2
  · rw [hb]; exact (A.right_mem_joint p hp).1
  exact subset_closure (A.positive_on_interval p hp
    ⟨lt_of_le_of_ne hs.1 (Ne.symm ha), lt_of_le_of_ne hs.2 hb⟩)

end TwoDIntervalFamily
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem interval_left_gradient_pos (A : TwoDIntervalFamily h) (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
    0 < twoDGradient h (twoDLine.symm p.1) 0 := by
  have hx := A.left_mem_joint p hp
  have hzero : h (twoDLine.symm p.1) = 0 := hx.2
  have hd := twoD_real_hasDerivAt ((hf.height_smoothAt _ hx.1).differentiableAt (by simp))
  have hn : 0 ≤ twoDGradient h (twoDLine.symm p.1) 0 := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (sub_pos.mpr (A.ordered p hp)))] with s hs hs'
    have hs0 : 0 < s := hs
    have hv := A.positive_on_interval p hp (show p.1 + s ∈ Ioo p.1 p.2 from ⟨by linarith, by linarith⟩)
    simp only [hzero, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hs0.le) hv.le
  have hne : twoDGradient h (twoDLine.symm p.1) 0 ≠ 0 := by
    have hg := hf.endpoint_gradient_pos _ hx
    rw [twoD_norm_eq] at hg
    exact abs_pos.mp hg
  exact lt_of_le_of_ne hn (Ne.symm hne)

theorem interval_right_gradient_neg (A : TwoDIntervalFamily h) (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
    twoDGradient h (twoDLine.symm p.2) 0 < 0 := by
  have hx := A.right_mem_joint p hp
  have hzero : h (twoDLine.symm p.2) = 0 := hx.2
  have hd := twoD_real_hasDerivAt ((hf.height_smoothAt _ hx.1).differentiableAt (by simp))
  have hn : twoDGradient h (twoDLine.symm p.2) 0 ≤ 0 := by
    apply le_of_tendsto hd.tendsto_slope_zero_left
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds (sub_neg.mpr (A.ordered p hp)))] with s hs hs'
    have hs0 : s < 0 := hs
    have hv := A.positive_on_interval p hp (show p.2 + s ∈ Ioo p.1 p.2 from ⟨by linarith, by linarith⟩)
    simp only [hzero, sub_zero, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hs0.le) hv.le
  have hne : twoDGradient h (twoDLine.symm p.2) 0 ≠ 0 := by
    have hg := hf.endpoint_gradient_pos _ hx
    rw [twoD_norm_eq] at hg
    exact abs_pos.mp hg
  exact lt_of_le_of_ne hn hne

theorem futureSlope_hasDerivAt {s : ℝ} (hs : twoDLine.symm s ∈ twoDClosedPositive h) :
    HasDerivAt (fun t => twoDGradient f (twoDLine.symm t) 0)
      (twoDFutureHessian f (twoDLine.symm s)) s := by
  have hD := (((hf.future_smoothAt _ hs).fderiv_right (m := 2)
    (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)).hasFDerivAt
  have he : HasDerivAt (fun t : ℝ => twoDLine.symm t) (twoDLine.symm 1) s :=
    twoDLine.symm.toContinuousLinearEquiv.hasFDerivAt.hasDerivAt
  simpa only [twoDFutureHessian, Function.comp_apply, twoD_differential_eq_inner, twoD_inner_eq,
    twoDLine_symm_apply, mul_one, map_zero, add_zero] using
    (hD.comp_hasDerivAt s he).clm_apply (hasDerivAt_const s (twoDLine.symm 1))

theorem continuousAt_futureHessian {x : TwoDSpace} (hx : x ∈ twoDClosedPositive h) :
    ContinuousAt (twoDFutureHessian f) x := by
  have he : Continuous (fun L : TwoDSpace →L[ℝ] TwoDSpace →L[ℝ] ℝ =>
      L (twoDLine.symm 1) (twoDLine.symm 1)) :=
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const
  exact he.continuousAt.comp (((hf.future_smoothAt x hx).fderiv_right (m := 2)
    (WithTop.coe_le_coe.mpr le_top)).fderiv_right (m := 1) (by norm_num)).continuousAt

/-- Ordinary FTC on each complete component, with no critical-point exclusion. -/
theorem integral_futureHessian_interval (A : TwoDIntervalFamily h) (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
    (∫ s in p.1..p.2, twoDFutureHessian f (twoDLine.symm s)) =
      twoDGradient f (twoDLine.symm p.2) 0 - twoDGradient f (twoDLine.symm p.1) 0 := by
  have hreg {s : ℝ} (hs : s ∈ uIcc p.1 p.2) : twoDLine.symm s ∈ twoDClosedPositive h := by
    rw [uIcc_of_le (A.ordered p hp).le] at hs
    exact A.interval_mem_closedPositive p hp hs
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hf.futureSlope_hasDerivAt (hreg hs))
  exact ContinuousOn.intervalIntegrable (fun s hs =>
    ((hf.continuousAt_futureHessian (hreg hs)).comp
      twoDLine.symm.continuous.continuousAt).continuousWithinAt)

end SmoothTwoD
end BoundaryDraft
