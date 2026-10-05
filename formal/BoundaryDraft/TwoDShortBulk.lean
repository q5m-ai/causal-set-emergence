import BoundaryDraft.TwoDMovingEndpoint

/-! # Actual fixed-domain 2D bulk and absolute collar decomposition

The full point volume, time-linear term and future Hessian are retained.
These fixed-domain derivatives include every positive-height critical point.
The global moving-endpoint collar assembly is a separate producer.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

@[simp] theorem twoDShortGap_zero (f : TwoDSpace → ℝ) (x : TwoDSpace) :
    twoDShortGap f 0 x = 0 := by simp [twoDShortGap]

/-- The correction is supported in the original positive source region,
not in an extension containing unrelated exterior zeros. -/
def twoDShortCollarCorrection (h f : TwoDSpace → ℝ) (z : TwoDSpacetime) : ℝ :=
  ∫ x in {x | 0 < h x}, max 0 (twoDShortGap f z x - h x)

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem future_contDiffAt_three (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    ContDiffAt ℝ 3 f x := (hf.future_smoothAt x hx).of_le (WithTop.coe_le_coe.mpr le_top)

/-- A global bound for the actual short gap, including noncausal parameters. -/
theorem abs_shortGap_le (z : TwoDSpacetime) (x : TwoDSpace) :
    |twoDShortGap f z x| ≤ 2 * ‖z‖ := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  have hb := C.future_increment x z.2
  have ht : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hη : η ≤ 1 := by linarith [C.budget, C.height_nonneg]
  have hb' : |f (x + z.2) - f x| ≤ ‖z‖ :=
    hb.trans ((mul_le_of_le_one_left (norm_nonneg _) hη).trans (norm_snd_le z))
  calc
    |twoDShortGap f z x| = |z.1 - (f (x + z.2) - f x)| := by congr 1; unfold twoDShortGap; ring
    _ ≤ |z.1| + |f (x + z.2) - f x| := abs_sub _ _
    _ ≤ 2 * ‖z‖ := by linarith

theorem shortGap_nonneg (z : TwoDSpacetime) (hz : ‖z.2‖ ≤ z.1) (x : TwoDSpace) :
    0 ≤ twoDShortGap f z x := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  exact (mul_nonneg (by linarith [C.budget, C.height_nonneg])
    ((norm_nonneg _).trans hz)).trans (C.shortGap_bounds z hz x).1

theorem shortCollar_integrand_eq_zero (z : TwoDSpacetime) (x : TwoDSpace)
    (hx : 2 * ‖z‖ ≤ h x) : max 0 (twoDShortGap f z x - h x) = 0 := by
  apply max_eq_left
  have hb := (le_abs_self (twoDShortGap f z x)).trans (hf.abs_shortGap_le z x)
  linarith

end SmoothTwoD
/-- The fixed-domain future-face increment. No collar charts are used here. -/
def twoDShortBulk (h f : TwoDSpace → ℝ) (z : TwoDSpacetime) : ℝ :=
  ∫ x in {x | 0 < h x}, f (x + z.2) - f x

private theorem twoD_hasFDerivAt_bulkSlice {g : TwoDSpace → ℝ} {x : TwoDSpace}
    (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (fun z : TwoDSpacetime => g (x + z.2) - g x)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.snd ℝ ℝ TwoDSpace)) 0 := by
  have ht : HasFDerivAt (fun z : TwoDSpacetime => x + z.2)
      (ContinuousLinearMap.snd ℝ ℝ TwoDSpace) 0 := by
    simpa only [zero_add] using (hasFDerivAt_const x (0 : TwoDSpacetime)).add
      (hasFDerivAt_snd (p := (0 : TwoDSpacetime)) (𝕜 := ℝ))
  have hg' : HasFDerivAt g (fderiv ℝ g x) (x + (0 : TwoDSpacetime).2) := by
    simpa using hg.hasFDerivAt
  exact (hg'.comp (f := fun z : TwoDSpacetime => x + z.2) 0 ht).sub_const (g x)

private theorem twoD_fderiv_fderiv_bulkSlice {g : TwoDSpace → ℝ} {x : TwoDSpace}
    (hg : ContDiffAt ℝ 3 g x) (v w : TwoDSpacetime) :
    fderiv ℝ (fderiv ℝ (fun z : TwoDSpacetime => g (x + z.2) - g x)) 0 v w =
      fderiv ℝ (fderiv ℝ g) x v.2 w.2 := by
  let S : TwoDSpacetime →L[ℝ] TwoDSpace := ContinuousLinearMap.snd ℝ ℝ TwoDSpace
  let T : TwoDSpacetime → TwoDSpace := fun z => x + z.2
  have hT (z : TwoDSpacetime) : HasFDerivAt T S z := by
    simpa only [zero_add] using (hasFDerivAt_const x z).add
      (hasFDerivAt_snd (p := z) (𝕜 := ℝ))
  have he : fderiv ℝ (fun z : TwoDSpacetime => g (x + z.2) - g x) =ᶠ[𝓝 0]
      (fun z => (fderiv ℝ g (T z)).comp S) := by
    have hh : ∀ᶠ z in 𝓝 (0 : TwoDSpacetime), ContDiffAt ℝ 3 g (T z) := by
      have ht : Tendsto T (𝓝 (0 : TwoDSpacetime)) (𝓝 x) := by
        simpa [T] using (hT 0).continuousAt.tendsto
      exact ht.eventually (hg.eventually (by simp))
    filter_upwards [hh] with z hz
    exact (((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z (hT z)).sub_const (g x)).fderiv
  have hD : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) (T 0) := by
    simpa [T] using ((hg.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hH := (hD.comp 0 (hT 0)).clm_comp (hasFDerivAt_const S (0 : TwoDSpacetime))
  have hHeq := hH.fderiv
  dsimp only [Function.comp_apply] at hHeq
  rw [he.fderiv_eq, hHeq]
  simp [ContinuousLinearMap.comp_apply, S]

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- Joint smoothness and compact parameter differentiation keep every point
of the fixed interior, including positive-height critical points. -/
theorem contDiffAt_shortBulk : ContDiffAt ℝ 3 (twoDShortBulk h f) 0 := by
  let μ : Measure TwoDSpace := volume.restrict {x | 0 < h x}
  have hs := hf.isCompact_closedPositive
  have he : (fun z : TwoDSpacetime => ∫ x in twoDClosedPositive h,
      f (x + z.2) - f x ∂μ) = twoDShortBulk h f := by
    funext z
    have hm : μ.restrict (twoDClosedPositive h) = μ := by
      dsimp [μ]
      rw [Measure.restrict_restrict hs.measurableSet,
        inter_eq_right.mpr (show {x | 0 < h x} ⊆ twoDClosedPositive h from subset_closure)]
    change ∫ x, (f (x + z.2) - f x) ∂μ.restrict (twoDClosedPositive h) = _
    rw [hm]
    rfl
  rw [← he]
  apply MovingCollar.contDiffAt_integral_compact 3 hs
    (F := fun p : TwoDSpacetime × TwoDSpace => f (p.2 + p.1.2) - f p.2)
  intro x hx
  have hfx := hf.future_contDiffAt_three x hx
  have hfb : ContDiffAt ℝ 3 f (x + (0 : TwoDSpacetime).2) := by simpa using hfx
  exact (hfb.comp (0, x) (contDiffAt_snd.add contDiffAt_fst.snd)).sub
    (hfx.comp (0, x) contDiffAt_snd)

/-- Fixed-domain two-jet with the actual future Hessian. -/
theorem shortBulk_twoJet : ContDiffAt ℝ 3 (twoDShortBulk h f) 0 ∧
    twoDShortBulk h f 0 = 0 ∧
    (∀ v : TwoDSpacetime, fderiv ℝ (twoDShortBulk h f) 0 v =
      ∫ x in {x | 0 < h x}, fderiv ℝ f x v.2) ∧
    ∀ v w : TwoDSpacetime, fderiv ℝ (fderiv ℝ (twoDShortBulk h f)) 0 v w =
      ∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x v.2 w.2 := by
  let μ : Measure TwoDSpace := volume.restrict {x | 0 < h x}
  let F : TwoDSpacetime × TwoDSpace → ℝ := fun p => f (p.2 + p.1.2) - f p.2
  have hm : μ.restrict (twoDClosedPositive h) = μ := by
    dsimp only [μ]
    rw [Measure.restrict_restrict hf.isCompact_closedPositive.measurableSet,
      inter_eq_right.mpr (show {x | 0 < h x} ⊆ twoDClosedPositive h from subset_closure)]
  have hF (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) : ContDiffAt ℝ 2 F (0, x) := by
    have hfx := hf.future_contDiffAt_three x hx
    have hfb : ContDiffAt ℝ 3 f (x + (0 : TwoDSpacetime).2) := by simpa using hfx
    exact ((hfb.comp (0, x) (contDiffAt_snd.add contDiffAt_fst.snd)).sub
      (hfx.comp (0, x) contDiffAt_snd)).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hj := MovingCollar.integral_twoJet (μ := μ) (F := F) (x₀ := (0 : TwoDSpacetime))
    hf.isCompact_closedPositive hF
  simp only [IntegrableOn, hm] at hj
  refine ⟨hf.contDiffAt_shortBulk, by simp [twoDShortBulk], ?_, ?_⟩
  · intro v
    have he := hj.2.2.1.fderiv
    change fderiv ℝ (twoDShortBulk h f) 0 = ∫ x, fderiv ℝ (fun z => F (z, x)) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.1]
    apply setIntegral_congr_fun hf.isOpen_positive.measurableSet
    intro x hx
    have hd := twoD_hasFDerivAt_bulkSlice
      ((hf.future_contDiffAt_three x (subset_closure hx)).differentiableAt (by norm_num))
    exact congrArg (fun L : TwoDSpacetime →L[ℝ] ℝ => L v) hd.fderiv
  · intro v w
    have he := hj.2.2.2
    change fderiv ℝ (fderiv ℝ (twoDShortBulk h f)) 0 =
      ∫ x, fderiv ℝ (fderiv ℝ (fun z => F (z, x))) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.2.1,
      ContinuousLinearMap.integral_apply (hj.2.1.apply_continuousLinearMap v)]
    apply setIntegral_congr_fun hf.isOpen_positive.measurableSet
    intro x hx
    exact twoD_fderiv_fderiv_bulkSlice (hf.future_contDiffAt_three x (subset_closure hx)) v w

/-- Exact absolute identity before taking derivatives. No planar comparison
cancels the point volume or the moving time slice. -/
theorem overlap_eq_absolute_bulk (z : TwoDSpacetime) (hc : ‖z.2‖ ≤ z.1) :
    twoDDisplacementOverlap h f z =
      volume.real (twoDRegion h f) - z.1 * volume.real {x | 0 < h x} +
        twoDShortBulk h f z + twoDShortCollarCorrection h f z := by
  have hi : IntegrableOn (fun _ : TwoDSpace => z.1) {x | 0 < h x} :=
    (continuous_const.continuousOn.integrableOn_compact
      hf.isCompact_closedPositive).mono_set subset_closure
  have hq : IntegrableOn (twoDShortGap f z) {x | 0 < h x} := by
    simpa only [one_mul] using hf.integrableOn_weighted_shortGap (fun _ => 1) continuousOn_const z
  have he : twoDShortBulk h f z = z.1 * volume.real {x | 0 < h x} -
      ∫ x in {x | 0 < h x}, twoDShortGap f z x := by
    calc
      _ = ∫ x in {x | 0 < h x}, z.1 - twoDShortGap f z x := by
        apply integral_congr_ae
        filter_upwards with x
        unfold twoDShortGap
        ring
      _ = _ := by rw [integral_sub hi hq]; simp [mul_comm]
  have ha := hf.weightedOverlap_eq_bulk_add_correction (fun _ => 1) continuousOn_const z hc
  simp only [one_mul] at ha
  change twoDDisplacementOverlap h f z = _ at ha
  rw [← hf.volume_region] at ha
  rw [ha, he]
  dsimp only [twoDShortCollarCorrection, Measure.real]
  ring


end SmoothTwoD
end BoundaryDraft
