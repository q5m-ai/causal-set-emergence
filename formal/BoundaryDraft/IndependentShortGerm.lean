import BoundaryDraft.IndependentFace
import BoundaryDraft.TwoFaceShortOverlapJet
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Raw germs in the independent-envelope short overlap

The envelopes need not be differentiable across the joint. Before taking any
raw-germ displacement derivatives, this file proves equality of their positive
parts on one fixed small future-cone neighborhood. All margins are derived
from class E; the same-height planar cap is never used.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A derived neighborhood of the compact spatial region on which both RAW
face germs are smooth with a common strict differential bound. This is not an
admissibility field and imposes no condition at positive-height critical points. -/
structure RawFaceNeighborhood (h f : Spatial → ℝ) (ε κ : ℝ) : Prop where
  radius_pos : 0 < ε
  slope_nonneg : 0 ≤ κ
  slope_lt_one : κ < 1
  smooth_future : ∀ x ∈ Metric.cthickening ε (graphClosedPositive h),
    ContDiffAt ℝ 3 (fun y : JointSpace => f y) x
  smooth_past : ∀ x ∈ Metric.cthickening ε (graphClosedPositive h),
    ContDiffAt ℝ 3 (fun y : JointSpace => f y - h y) x
  bound_future : ∀ x ∈ Metric.cthickening ε (graphClosedPositive h),
    ‖fderiv ℝ (fun y : JointSpace => f y) x‖ ≤ κ
  bound_past : ∀ x ∈ Metric.cthickening ε (graphClosedPositive h),
    ‖fderiv ℝ (fun y : JointSpace => f y - h y) x‖ ≤ κ

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- Compactness and continuity of the raw differentials enlarge the independent
strict bounds to a common neighborhood, without differentiating an envelope. -/
theorem exists_rawFaceNeighborhood : ∃ ε κ : ℝ, RawFaceNeighborhood h f ε κ := by
  obtain ⟨k, hk, hk1, hb⟩ := hf.exists_face_slope_bound
  let κ := (k + 1) / 2
  have hkκ : k < κ := by dsimp [κ]; linarith
  have hκ : 0 ≤ κ := by dsimp [κ]; linarith
  have hκ1 : κ < 1 := by dsimp [κ]; linarith
  let U := {x : JointSpace | ContDiffAt ℝ 3 (fun y : JointSpace => f y) x ∧
    ContDiffAt ℝ 3 (fun y : JointSpace => f y - h y) x ∧
    ‖fderiv ℝ (fun y : JointSpace => f y) x‖ < κ ∧
    ‖fderiv ℝ (fun y : JointSpace => f y - h y) x‖ < κ}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun x hx => by
    have hF := hx.1
    have hP := hx.2.1
    have hDF := (hF.fderiv_right (m := 0) (by norm_num)).continuousAt.norm
    have hDP := (hP.fderiv_right (m := 0) (by norm_num)).continuousAt.norm
    exact (hF.eventually (by simp)).and ((hP.eventually (by simp)).and
      ((hDF.eventually (gt_mem_nhds hx.2.2.1)).and (hDP.eventually (gt_mem_nhds hx.2.2.2))))
  have hKU : graphClosedPositive h ⊆ U := by
    intro x hx
    refine ⟨hf.smooth_future x hx, (hf.smooth_future x hx).sub (hf.smooth_near x hx), ?_, ?_⟩
    · exact (show ‖fderiv ℝ (fun y : JointSpace => f y) x‖ ≤ k by
        simpa only [← graphSlope_eq_norm_fderiv, graphSlope] using (hb x hx).1).trans_lt hkκ
    · exact (show ‖fderiv ℝ (fun y : JointSpace => f y - h y) x‖ ≤ k by
        simpa only [← graphSlope_eq_norm_fderiv, graphSlope] using (hb x hx).2).trans_lt hkκ
  obtain ⟨ε, hε, he⟩ := hf.toRegularHeight.isCompact_closedPositive.exists_cthickening_subset_open hU hKU
  exact ⟨ε, κ, hε, hκ, hκ1, fun x hx => (he hx).1,
    fun x hx => (he hx).2.1, fun x hx => (he hx).2.2.1.le, fun x hx => (he hx).2.2.2.le⟩

end AdmissibleIndependentTwoFace

namespace RawFaceNeighborhood
variable {h f : Spatial → ℝ} {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
include N

omit N in
/-- Every short segment from the closed positive region stays in the raw
smoothness neighborhood. No convexity of the spatial region is required. -/
theorem add_mem {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {b : JointSpace} (hb : ‖b‖ ≤ ε) : x + b ∈ Metric.cthickening ε (graphClosedPositive h) := by
  apply Metric.mem_cthickening_of_dist_le (x + b) x ε _ hx
  simpa only [dist_eq_norm, add_sub_cancel_left] using hb

private theorem difference_bound {g : JointSpace → ℝ}
    (hs : ∀ x ∈ Metric.cthickening ε (graphClosedPositive h), ContDiffAt ℝ 3 g x)
    (hd : ∀ x ∈ Metric.cthickening ε (graphClosedPositive h), ‖fderiv ℝ g x‖ ≤ κ)
    {x : JointSpace} (hx : x ∈ graphClosedPositive h) {b : JointSpace} (hb : ‖b‖ ≤ ε) :
    |g (x + b) - g x| ≤ κ * ‖b‖ := by
  have hsub : Metric.closedBall x ε ⊆ Metric.cthickening ε (graphClosedPositive h) :=
    fun y hy => Metric.mem_cthickening_of_dist_le y x ε _ hx hy
  have he := (convex_closedBall x ε).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => (hs y (hsub hy)).differentiableAt (by norm_num))
    (fun y hy => hd y (hsub hy)) (Metric.mem_closedBall_self N.radius_pos.le)
    (show x + b ∈ Metric.closedBall x ε by simpa [dist_eq_norm] using hb)
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using he

theorem future_difference {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {b : JointSpace} (hb : ‖b‖ ≤ ε) : |f (x + b) - f x| ≤ κ * ‖b‖ :=
  N.difference_bound N.smooth_future N.bound_future hx hb

theorem past_difference {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {b : JointSpace} (hb : ‖b‖ ≤ ε) :
    |(f (x + b) - h (x + b)) - (f x - h x)| ≤ κ * ‖b‖ :=
  N.difference_bound N.smooth_past N.bound_past hx hb

/-- Local causal bounds are for the RAW gap and only near the actual region. -/
theorem gap_bounds {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) (hc : ‖z.2‖ ≤ z.1) :
    (1 - κ) * z.1 ≤ shortOverlapGap f z x ∧ shortOverlapGap f z x ≤ (1 + κ) * z.1 := by
  have hb := abs_le.mp (N.future_difference hx hz)
  have hm := mul_le_mul_of_nonneg_left hc N.slope_nonneg
  dsimp [shortOverlapGap]
  constructor <;> nlinarith

theorem gap_nonneg {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) (hc : ‖z.2‖ ≤ z.1) :
    0 ≤ shortOverlapGap f z x :=
  (mul_nonneg (sub_nonneg.mpr N.slope_lt_one.le) ((norm_nonneg _).trans hc)).trans
    (N.gap_bounds hx hz hc).1

/-- The noncausal norm estimate used for a displacement extension is local too. -/
theorem abs_gap_le {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) : |shortOverlapGap f z x| ≤ 2 * ‖z‖ := by
  have hb : |f x - f (x + z.2)| ≤ ‖z‖ := by
    rw [abs_sub_comm]
    exact (N.future_difference hx hz).trans
      ((mul_le_of_le_one_left (norm_nonneg _) N.slope_lt_one.le).trans (norm_snd_le z))
  have ht : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  calc
    |shortOverlapGap f z x| = |z.1 + (f x - f (x + z.2))| := by congr 1; unfold shortOverlapGap; ring
    _ ≤ |z.1| + |f x - f (x + z.2)| := abs_add _ _
    _ ≤ 2 * ‖z‖ := by linarith

/-- A positive raw causal gap forces the translated endpoint back into the
positive region. This is the missing step before any raw-germ differentiation. -/
theorem partner_positive {x : JointSpace} (hx : x ∈ graphClosedPositive h)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) (hc : ‖z.2‖ ≤ z.1)
    (hp : 0 < h x - shortOverlapGap f z x) : 0 < h (x + z.2) := by
  have hb := (abs_le.mp (N.past_difference hx hz)).2
  have hκ : κ * ‖z.2‖ ≤ z.1 :=
    (mul_le_of_le_one_left (norm_nonneg _) N.slope_lt_one.le).trans hc
  dsimp [shortOverlapGap] at hp
  linarith

/-- Translated raw gaps are continuous on the fixed compact source region;
no global continuity of irrelevant exterior raw values is assumed. -/
theorem continuousOn_gap {z : Displacement} (hz : ‖z.2‖ ≤ ε) :
    ContinuousOn (shortOverlapGap f z) (graphClosedPositive h) := by
  intro x hx
  have h0 := add_mem hx (show ‖(0 : JointSpace)‖ ≤ ε by simpa using N.radius_pos.le)
  have hfx : ContinuousAt (fun y : JointSpace => f y) x := by
    simpa using (N.smooth_future (x + 0) h0).continuousAt
  have ht : ContinuousAt (fun y : JointSpace => y + z.2) x :=
    continuousAt_id.add continuousAt_const
  exact ((continuousAt_const.sub ((N.smooth_future _ (add_mem hx hz)).continuousAt.comp (f := fun y : JointSpace => y + z.2) ht)).add
    hfx).continuousWithinAt

end RawFaceNeighborhood

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- Global causal envelope gaps vanish unless BOTH endpoints have positive
height. The inequalities use the two envelope bounds separately. -/
theorem envelope_gap_le_heights (z : Displacement) (hc : ‖z.2‖ ≤ z.1) (x : JointSpace) :
    hf.upperEnvelope (x + z.2) - z.1 - hf.lowerEnvelope x ≤ max 0 (h x) ∧
    hf.upperEnvelope (x + z.2) - z.1 - hf.lowerEnvelope x ≤ max 0 (h (x + z.2)) := by
  have shift {g : Spatial → ℝ} (hg : StrictGraphLipschitz g) :
      |g (x + z.2) - g x| ≤ z.1 := by
    obtain ⟨k, _, hk, hl⟩ := hg
    have hb := hl (x + z.2) x
    have he : spatialDistance ((x + z.2 : JointSpace) : Spatial) x = ‖z.2‖ := by
      change ‖x - (x + z.2)‖ = ‖z.2‖
      simp
    rw [he] at hb
    exact hb.trans ((mul_le_of_le_one_left (norm_nonneg _) hk.le).trans hc)
  have hu := (abs_le.mp (shift hf.strictGraphLipschitz_upper)).2
  have hl := (abs_le.mp (shift hf.strictGraphLipschitz_lower)).2
  have h0 := hf.envelope_gap x
  have h1 := hf.envelope_gap (x + z.2)
  constructor <;> linarith

/-- Raw/envelope positive-part equality is proved BEFORE differentiating.
The equality is restricted to sources in the closed positive region, not to
arbitrary exterior raw data. It includes null vectors and the vertex. -/
theorem raw_envelope_positivePart {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) (hc : ‖z.2‖ ≤ z.1)
    {x : JointSpace} (hx : x ∈ graphClosedPositive h) :
    max 0 (hf.upperEnvelope (x + z.2) - z.1 - hf.lowerEnvelope x) =
      max 0 (h x - shortOverlapGap f z x) := by
  by_cases hy : 0 < h (x + z.2)
  · rw [hf.upper_eq _ (subset_closure hy), hf.lower_eq x hx]
    congr 1
    unfold shortOverlapGap
    ring
  · have hraw : h x - shortOverlapGap f z x ≤ 0 :=
      le_of_not_gt (fun hp => hy (N.partner_positive hx hz hc hp))
    have henv := (hf.envelope_gap_le_heights z hc x).2
    rw [max_eq_left (le_of_not_gt hy)] at henv
    rw [max_eq_left henv, max_eq_left hraw]

/-- The actual overlap, using the smooth raw future only after positive-part
agreement. No same-height planar overlap or reference limit occurs. -/
theorem translatedOverlap_eq_shortGap {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) (hc : ‖z.2‖ ≤ z.1) :
    translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) =
      ∫ x : JointSpace in {x : JointSpace | 0 < h x}, max 0 (h x - shortOverlapGap f z x) := by
  have hb : Bornology.IsBounded (twoGraphRegion hf.lowerEnvelope hf.upperEnvelope) := by
    rw [← hf.region_eq_twoGraphRegion]
    exact hf.isBounded_region
  rw [hf.region_eq_twoGraphRegion]
  change translatedOverlap _ (Fin.cons z.1 z.2) = _
  rw [translatedOverlap_twoGraph_causal hf.strictGraphLipschitz_lower hf.strictGraphLipschitz_upper hb
    ((displacementSpacetime_mem_causalFuture z).mpr hc)]
  let e := WithLp.equiv 2 (Fin 3 → ℝ)
  have he : MeasurableEmbedding e := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).integral_comp he]
  have hm : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toRegularHeight.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  rw [← integral_indicator hm]
  apply integral_congr_ae
  filter_upwards with x
  change max 0 (hf.upperEnvelope (x + z.2) - z.1 - hf.lowerEnvelope x) = _
  by_cases hx : 0 < h x
  · rw [indicator_of_mem (show x ∈ {x : JointSpace | 0 < h x} from hx)]
    exact hf.raw_envelope_positivePart N hz hc (subset_closure hx)
  · rw [indicator_of_not_mem (show x ∉ {x : JointSpace | 0 < h x} from hx)]
    have hb := (hf.envelope_gap_le_heights z hc x).1
    rw [max_eq_left (le_of_not_gt hx)] at hb
    exact max_eq_left hb

/-- Absolute integrability precedes the signed interior/collar splitting. -/
theorem integrableOn_shortOverlapGap {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) :
    IntegrableOn (shortOverlapGap f z) {x : JointSpace | 0 < h x} :=
  ((N.continuousOn_gap hz).integrableOn_compact hf.toRegularHeight.isCompact_closedPositive).mono_set
    subset_closure

/-- The absolute source identity retains the volume, time-linear slice and
entire moving collar. It does not yet assert a Taylor expansion or limit. -/
theorem translatedOverlap_eq_fixed_sub_gap_add_collar {ε κ : ℝ}
    (N : RawFaceNeighborhood h f ε κ) {z : Displacement} (hz : ‖z.2‖ ≤ ε)
    (hc : ‖z.2‖ ≤ z.1) :
    translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) =
      (∫ x : JointSpace in {x : JointSpace | 0 < h x}, h x) -
      (∫ x : JointSpace in {x : JointSpace | 0 < h x}, shortOverlapGap f z x) +
        shortOverlapCollarCorrection h f z := by
  rw [hf.translatedOverlap_eq_shortGap N hz hc]
  have hh : IntegrableOn (fun x : JointSpace => h x) {x : JointSpace | 0 < h x} :=
    (hf.toRegularHeight.continuousOn_closedPositive.integrableOn_compact
      hf.toRegularHeight.isCompact_closedPositive).mono_set subset_closure
  have hq := hf.integrableOn_shortOverlapGap N hz
  have he (x : JointSpace) : max 0 (h x - shortOverlapGap f z x) =
      h x - shortOverlapGap f z x + max 0 (shortOverlapGap f z x - h x) := by
    rcases le_total (h x) (shortOverlapGap f z x) with hl | hl
    · rw [max_eq_left (sub_nonpos.mpr hl), max_eq_right (sub_nonneg.mpr hl)]; ring
    · rw [max_eq_right (sub_nonneg.mpr hl), max_eq_left (sub_nonpos.mpr hl)]; ring
  simp_rw [he]
  have hi : IntegrableOn (fun x => max 0 (shortOverlapGap f z x - h x)) {x : JointSpace | 0 < h x} := by
    simpa only [Pi.sub_apply, max_comm] using (hq.sub hh).pos_part
  simpa only [Pi.sub_apply, shortOverlapCollarCorrection] using
    (integral_add (hh.sub hq) hi).trans
      (congrArg (fun a => a + shortOverlapCollarCorrection h f z) (integral_sub hh hq))

end AdmissibleIndependentTwoFace
end BoundaryDraft
