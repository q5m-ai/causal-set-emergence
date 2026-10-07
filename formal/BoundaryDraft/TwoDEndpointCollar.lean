import BoundaryDraft.TwoDShortBulk
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Physical endpoint collars for the actual whole-region correction -/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

private theorem positive_inward_interval {H : ℝ → ℝ} {d : ℝ}
    (hH : ContDiffAt ℝ 3 H 0) (hD : HasDerivAt H d 0) (h0 : H 0 = 0) (hd : 0 < d) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ Icc (-B) B,
      ContDiffAt ℝ 3 H s ∧ (0 < H s ↔ 0 < s) ∧ (0 ≤ H s ↔ 0 ≤ s) := by
  have hderiv : ContinuousAt (deriv H) 0 :=
    ((hH.fderiv_right (m := 0) (by decide)).clm_apply contDiffAt_const).continuousAt
  have hp : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 3 H s ∧ 0 < deriv H s :=
    (hH.eventually (by simp)).and
      (hderiv.eventually (lt_mem_nhds (by simpa only [hD.deriv] using hd)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hp
  let B := r / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hs (s : ℝ) (hs : s ∈ Icc (-B) B) : ContDiffAt ℝ 3 H s ∧ 0 < deriv H s := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> dsimp [B] at hs ⊢ <;> linarith [hs.1, hs.2]
  have hm : StrictMonoOn H (Icc (-B) B) := strictMonoOn_of_deriv_pos (convex_Icc (-B) B)
    (fun s hs' => (hs s hs').1.continuousAt.continuousWithinAt)
    (fun s hs' => (hs s (interior_subset hs')).2)
  have hz : (0 : ℝ) ∈ Icc (-B) B := ⟨by linarith, hB.le⟩
  refine ⟨B, hB, fun s hs' => ⟨(hs s hs').1, ?_, ?_⟩⟩
  · simpa only [h0] using hm.lt_iff_lt hz hs'
  · simpa only [h0] using hm.le_iff_le hz hs'

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- The raw height changes sign across the actual regular endpoint in the
physical inward coordinate; no interior gradient lower bound is assumed. -/
theorem exists_inward_interval (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h) :
    ∃ B : ℝ, 0 < B ∧ ∀ s ∈ Icc (-B) B,
      ContDiffAt ℝ 3 (fun t => h (twoDEndpointPoint h x t)) s ∧
      (0 < h (twoDEndpointPoint h x s) ↔ 0 < s) ∧
      (0 ≤ h (twoDEndpointPoint h x s) ↔ 0 ≤ s) := by
  have hpoint : ContDiff ℝ 3 (twoDEndpointPoint h x) := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hh : ContDiffAt ℝ 3 h (twoDEndpointPoint h x 0) := by
    simpa [twoDEndpointPoint] using
      (hf.height_smoothAt x hx.1).of_le (m := 3) (WithTop.coe_le_coe.mpr le_top)
  have he : HasDerivAt (twoDEndpointPoint h x) (twoDInward h x) 0 := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const (twoDInward h x))
  have hd : HasDerivAt (fun s => h (twoDEndpointPoint h x s)) ‖twoDGradient h x‖ 0 := by
    simpa only [twoDEndpointPoint, zero_smul, add_zero, hf.height_inward x hx] using
      (hh.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 he
  exact positive_inward_interval (hh.comp 0 hpoint.contDiffAt) hd
    (by simpa [twoDEndpointPoint] using hx.2) (hf.endpoint_gradient_pos x hx)

theorem endpointGap_root_iff (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h)
    (z : TwoDSpacetime) (s : ℝ) :
    s = twoDEndpointGap h f x (z, s) ↔
      h (twoDEndpointPoint h x s) = twoDShortGap f z (twoDEndpointPoint h x s) := by
  unfold twoDEndpointGap
  constructor
  · intro he
    have hd : (twoDShortGap f z (twoDEndpointPoint h x s) - h (twoDEndpointPoint h x s)) /
        ‖twoDGradient h x‖ = 0 := by linarith
    exact (sub_eq_zero.mp ((div_eq_zero_iff.mp hd).resolve_right
      (hf.endpoint_gradient_pos x hx).ne')).symm
  · intro he
    simp [he]

/-- Every root produced above has an arbitrarily small PHYSICAL collar on
which its oriented integral is the actual positive-part correction. -/
theorem exists_endpointCollar (x : TwoDSpace) (hx : x ∈ dimensionTwoSpatialJoint h)
    (R : ℝ) (hR : 0 < R) (η : TwoDSpacetime → ℝ) (hη₀ : η 0 = 0)
    (hη : ContinuousAt η 0)
    (hroot : ∀ᶠ z in 𝓝 0, η z = twoDEndpointGap h f x (z, η z))
    (hunique : ∀ᶠ p in 𝓝 ((0 : TwoDSpacetime), (0 : ℝ)),
      p.2 = twoDEndpointGap h f x p → p.2 = η p.1) :
    ∃ B δ : ℝ, 0 < B ∧ B < R ∧ 0 < δ ∧
      (∀ s ∈ Icc (-B) B, 0 < h (twoDEndpointPoint h x s) ↔ 0 < s) ∧
      ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
        (∫ s in (0 : ℝ)..B,
          max 0 (twoDShortGap f z (twoDEndpointPoint h x s) - h (twoDEndpointPoint h x s))) =
            twoDEndpointCorrection h f x η z := by
  obtain ⟨b, hb, hsign⟩ := hf.exists_inward_interval x hx
  have hnear := ((hf.contDiffAt_endpointGap x hx).eventually (by simp)).and hunique
  obtain ⟨r, hr, hq⟩ := Metric.mem_nhds_iff.mp hnear
  let B := min b (min R r) / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hBb : B < b := by dsimp [B]; linarith [min_le_left b (min R r)]
  have hBR : B < R := by dsimp [B]; linarith [(min_le_right b (min R r)).trans (min_le_left R r)]
  have hBr : B < r := by dsimp [B]; linarith [(min_le_right b (min R r)).trans (min_le_right R r)]
  have hsgn (s : ℝ) (hs : s ∈ Icc (-B) B) := hsign s
    (show s ∈ Icc (-b) b from ⟨by linarith [hs.1], hs.2.trans hBb.le⟩)
  have hHB : 0 < h (twoDEndpointPoint h x B) := (hsgn B ⟨by linarith, le_rfl⟩).2.1.mpr hB
  have hqs (z : TwoDSpacetime) (hz : ‖z‖ < r) (s : ℝ) (hs : s ∈ Icc (-B) B) :
      ContDiffAt ℝ 3 (twoDEndpointGap h f x) (z, s) ∧
        (s = twoDEndpointGap h f x (z, s) → s = η z) := by
    apply hq
    change dist (z, s) (0 : TwoDSpacetime × ℝ) < r
    rw [dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
    exact ⟨hz, (abs_le.mpr hs).trans_lt hBr⟩
  have hηsmall : ∀ᶠ z in 𝓝 (0 : TwoDSpacetime), |η z| < B := by
    have ht := hη.eventually (Metric.ball_mem_nhds (η 0) hB)
    simpa only [hη₀, Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  have hzr : ∀ᶠ z in 𝓝 (0 : TwoDSpacetime), ‖z‖ < r := by
    filter_upwards [Metric.ball_mem_nhds (0 : TwoDSpacetime) hr] with z hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzm : ∀ᶠ z in 𝓝 (0 : TwoDSpacetime), ‖z‖ < h (twoDEndpointPoint h x B) / 4 := by
    filter_upwards [Metric.ball_mem_nhds (0 : TwoDSpacetime)
      (div_pos hHB (by norm_num : (0 : ℝ) < 4))] with z hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhds_iff.mp (hroot.and (hηsmall.and (hzr.and hzm)))
  refine ⟨B, δ, hB, hBR, hδ, fun s hs => (hsgn s hs).2.1, ?_⟩
  intro z hz hc
  obtain ⟨hrz, hηz, hzr, hzm⟩ := hδprop hz
  have hηB : η z ∈ Icc (-B) B := abs_le.mp hηz.le
  have hroot' := (hf.endpointGap_root_iff x hx z (η z)).mp hrz
  have hηpos : 0 ≤ η z := (hsgn (η z) hηB).2.2.mp (by
    rw [hroot']
    exact hf.shortGap_nonneg z hc _)
  have hC : ContinuousOn (fun s => twoDEndpointGap h f x (z, s)) (Icc 0 B) :=
    fun s hs => ((hqs z hzr s ⟨by linarith [hs.1], hs.2⟩).1.continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hd : 0 < ‖twoDGradient h x‖ := hf.endpoint_gradient_pos x hx
  have hx0 : h x = 0 := hx.2
  have hq0 : 0 ≤ twoDEndpointGap h f x (z, 0) := by
    simpa [twoDEndpointGap, twoDEndpointPoint, hx0] using
      div_nonneg (hf.shortGap_nonneg z hc x) hd.le
  have hqB : twoDEndpointGap h f x (z, B) < B := by
    have ht := (le_abs_self (twoDShortGap f z (twoDEndpointPoint h x B))).trans (hf.abs_shortGap_le z _)
    have hn : twoDShortGap f z (twoDEndpointPoint h x B) - h (twoDEndpointPoint h x B) < 0 := by linarith
    have ht := div_neg_of_neg_of_pos hn hd
    dsimp only [twoDEndpointGap]
    linarith
  have he (s : ℝ) : ‖twoDGradient h x‖ * max 0 (twoDEndpointGap h f x (z, s) - s) =
      max 0 (twoDShortGap f z (twoDEndpointPoint h x s) - h (twoDEndpointPoint h x s)) := by
    have hg : twoDEndpointGap h f x (z, s) - s =
        (twoDShortGap f z (twoDEndpointPoint h x s) - h (twoDEndpointPoint h x s)) /
          ‖twoDGradient h x‖ := by unfold twoDEndpointGap; ring
    rw [hg]
    by_cases ha : 0 ≤ twoDShortGap f z (twoDEndpointPoint h x s) - h (twoDEndpointPoint h x s)
    · rw [max_eq_right ha, max_eq_right (div_nonneg ha hd.le)]
      field_simp
    · rw [max_eq_left (le_of_not_ge ha), max_eq_left (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hd.le), mul_zero]
  have hint := MovingCollar.integral_positivePart_eq_root (W := fun _ => ‖twoDGradient h x‖)
    ⟨hηpos, hηB.2⟩ hC continuousOn_const hq0 hqB hrz
    (fun s hs => (hqs z hzr s ⟨by linarith [hs.1], hs.2⟩).2)
  simp_rw [he] at hint
  exact hint

end SmoothTwoD
end BoundaryDraft
