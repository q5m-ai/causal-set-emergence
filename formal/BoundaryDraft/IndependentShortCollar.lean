import BoundaryDraft.IndependentShortGerm
import BoundaryDraft.ShortOverlapTaylor

/-!
# The actual independent-envelope moving collar

The fixed regular-height atlas and its C² Jacobians are reused. Raw future
values are evaluated only in the derived neighborhood. In particular, root
positivity is obtained by an intermediate-value argument on nonnegative height
fibres, not by applying a global Lipschitz bound to an arbitrary raw germ.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ControlledCollarAtlas
variable {h f : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- A root in the actual nonnegative-height fibre is the uniform IFT root.
This avoids estimating clipped envelopes or raw exterior values at negative roots. -/
theorem exists_actual_collarFibre_independent (hf : AdmissibleIndependentTwoFace h f)
    (i : Fin A.count) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : SurfacePlane × Displacement → ℝ,
      (∀ y ∈ (A.charts i).closedDisk, η (y, 0) = 0) ∧
      (∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Displacement) δ,
        ContDiffAt ℝ 3 η (y, z) ∧
          η (y, z) = (A.charts i).movingGap f ((y, z), η (y, z))) ∧
      ∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Displacement) δ,
        ‖z.2‖ ≤ z.1 →
        (∫ t in (0 : ℝ)..A.width,
          (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)) *
            max 0 ((A.charts i).movingGap f ((y, z), t) - t)) =
          A.movingFibre i f y (fun z => η (y, z)) z := by
  let c := A.charts i
  obtain ⟨a, κ, N⟩ := hf.exists_rawFaceNeighborhood
  obtain ⟨ε, δ₀, hε, hδ₀, η, hη₀, hη⟩ := c.exists_uniform_movingRoots hf.toRegularHeightPair
  let δ := min a (min δ₀ (min ε A.width / 4))
  have hδ : 0 < δ := lt_min N.radius_pos
    (lt_min hδ₀ (div_pos (lt_min hε A.width_pos) (by norm_num)))
  have hzδ (z : Displacement) (hz : z ∈ Metric.ball (0 : Displacement) δ) :
      ‖z.2‖ ≤ a ∧ z ∈ Metric.ball (0 : Displacement) δ₀ ∧
        2 * ‖z‖ < ε ∧ 2 * ‖z‖ < A.width := by
    have hz' : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have ha := min_le_left a (min δ₀ (min ε A.width / 4))
    have hr := min_le_right a (min δ₀ (min ε A.width / 4))
    have h1 := min_le_left δ₀ (min ε A.width / 4)
    have h2 := min_le_right δ₀ (min ε A.width / 4)
    have he := min_le_left ε A.width
    have hw := min_le_right ε A.width
    refine ⟨(norm_snd_le z).trans (hz'.le.trans ha),
      Metric.ball_subset_ball (hr.trans h1) hz, ?_, ?_⟩ <;>
      dsimp only [δ] at hz' <;> nlinarith [norm_nonneg z]
  refine ⟨δ, hδ, η, hη₀, ?_, ?_⟩
  · intro y hy z hz
    exact ⟨(hη y hy z (hzδ z hz).2.1).1, (hη y hy z (hzδ z hz).2.1).2.2.1⟩
  · intro y hy z hz hcausal
    have hηp := hη y hy z (hzδ z hz).2.1
    have hroot := hηp.2.2.1
    have htarget (t : ℝ) (ht : t ∈ Icc 0 A.width) :
        jointHeightCoordinates.symm (t, y) ∈ c.chart.target :=
      c.ball_subset (c.rectangle_subset t
        ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩ y hy)
    have hclosed (t : ℝ) (ht : t ∈ Icc 0 A.width) :
        c.movingPoint ((y, z), t) ∈ graphClosedPositive h :=
      c.symm_mem_closedPositive _ (htarget t ht) ht.1
    have hbound (t : ℝ) (ht : t ∈ Icc 0 A.width) :
        |c.movingGap f ((y, z), t)| ≤ 2 * ‖z‖ := N.abs_gap_le (hclosed t ht) (hzδ z hz).1
    have hnonneg (t : ℝ) (ht : t ∈ Icc 0 A.width) : 0 ≤ c.movingGap f ((y, z), t) :=
      N.gap_nonneg (hclosed t ht) (hzδ z hz).1 hcausal
    have hΦ : ContinuousOn (fun t => c.movingPoint ((y, z), t)) (Icc 0 A.width) :=
      c.chart.symm.continuousOn.comp
        (jointHeightCoordinates.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
          htarget
    have hqc : ContinuousOn (fun t => c.movingGap f ((y, z), t)) (Icc 0 A.width) :=
      (N.continuousOn_gap (hzδ z hz).1).comp hΦ hclosed
    have hηpos : η (y, z) ∈ Icc 0 A.width := by
      have hg : ContinuousOn (fun t => t - c.movingGap f ((y, z), t)) (Icc 0 A.width) :=
        continuousOn_id.sub hqc
      obtain ⟨t, ht, he⟩ := intermediate_value_Icc A.width_pos.le hg
        (show (0 : ℝ) ∈ Icc (0 - c.movingGap f ((y, z), 0))
          (A.width - c.movingGap f ((y, z), A.width)) from
          ⟨by linarith [hnonneg 0 ⟨le_rfl, A.width_pos.le⟩], by
            have hb := (le_abs_self _).trans (hbound A.width ⟨A.width_pos.le, le_rfl⟩)
            linarith [(hzδ z hz).2.2.2]⟩)
      have heq : t = c.movingGap f ((y, z), t) := sub_eq_zero.mp he
      have htε : |t| < ε := by rw [heq]; exact (hbound t ht).trans_lt (hzδ z hz).2.2.1
      rwa [hηp.2.2.2 t htε heq] at ht
    have hwc : ContinuousOn
        (fun t => c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)))
        (Icc 0 A.width) :=
      (c.continuousOn_weightedJacobian (A.weights i) (A.weights i).contMDiff.continuous).comp
        (jointHeightCoordinates.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
          htarget
    apply MovingCollar.integral_positivePart_eq_root hηpos hqc hwc
      (hnonneg 0 ⟨le_rfl, A.width_pos.le⟩)
      (((le_abs_self _).trans (hbound A.width ⟨A.width_pos.le, le_rfl⟩)).trans_lt (hzδ z hz).2.2.2) hroot
    intro t ht he
    exact hηp.2.2.2 t (by rw [he]; exact (hbound t ht).trans_lt (hzδ z hz).2.2.1) he

/-- Only the regular collar is transported through the height atlas; the
fixed positive-height interior is never subjected to coarea. -/
theorem shortOverlapCollarCorrection_eq_sum_independent (hf : AdmissibleIndependentTwoFace h f)
    {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
    (z : Displacement) (hzε : ‖z.2‖ ≤ ε) (hz : 2 * ‖z‖ < A.width) :
    shortOverlapCollarCorrection h f z =
      ∑ i, ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p *
          max 0 (shortOverlapGap f z ((A.charts i).chart.symm p) -
            h ((A.charts i).chart.symm p)) := by
  have hopen : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toRegularHeight.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  have he : shortOverlapCollarCorrection h f z =
      ∫ x in {x : JointSpace | 0 < h x ∧ h x < A.width},
        max 0 (shortOverlapGap f z x - h x) := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hopen (fun _ hx => hx.1)
    intro x hx
    apply max_eq_left
    have hh : A.width ≤ h x := le_of_not_gt (fun ht => hx.2 ⟨hx.1, ht⟩)
    have hb := (le_abs_self (shortOverlapGap f z x)).trans (N.abs_gap_le (subset_closure hx.1) hzε)
    linarith
  rw [he, setIntegral_congr_set (hf.toRegularHeight.ae_openCollar_eq_closedCollar A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩))]
  apply A.integral_closedCollar_eq_sum hf.toRegularHeight
  have hc : ContinuousOn (fun x => max 0 (shortOverlapGap f z x - h x)) (graphClosedCollar h A.width) :=
    continuousOn_const.sup (((N.continuousOn_gap hzε).mono inter_subset_left).sub
      (hf.toRegularHeight.continuousOn_closedPositive.mono inter_subset_left))
  exact hc.integrableOn_compact (hf.toRegularHeight.isCompact_closedCollar A.width)

/-- Signed Fubini follows from continuous compact domination on each fixed
chart rectangle, with local rather than global raw-future continuity. -/
theorem integral_chart_correction_independent {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
    (i : Fin A.count) (z : Displacement) (hz : ‖z.2‖ ≤ ε) :
    (∫ p in (A.charts i).parameterRegion A.width,
      (A.charts i).weightedJacobian (A.weights i) p *
        max 0 (shortOverlapGap f z ((A.charts i).chart.symm p) - h ((A.charts i).chart.symm p))) =
      ∫ y in (A.charts i).disk, ∫ t in (0 : ℝ)..A.width,
        (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)) *
          max 0 ((A.charts i).movingGap f ((y, z), t) - t) := by
  let c := A.charts i
  let F : ℝ × SurfacePlane → ℝ := fun p =>
    c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm p) *
      max 0 (c.movingGap f ((p.2, z), p.1) - p.1)
  have htarget (p : ℝ × SurfacePlane) (hp : p ∈ Icc 0 A.width ×ˢ c.closedDisk) :
      jointHeightCoordinates.symm p ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset p.1
      ⟨(neg_nonpos.mpr c.width_pos.le).trans hp.1.1, hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)
  have hΦ : ContinuousOn (fun p : ℝ × SurfacePlane => c.chart.symm (jointHeightCoordinates.symm p))
      (Icc 0 A.width ×ˢ c.closedDisk) :=
    c.chart.symm.continuousOn.comp jointHeightCoordinates.symm.continuous.continuousOn htarget
  have hq : ContinuousOn (fun p : ℝ × SurfacePlane => c.movingGap f ((p.2, z), p.1))
      (Icc 0 A.width ×ˢ c.closedDisk) :=
    (N.continuousOn_gap hz).comp hΦ (fun p hp => c.symm_mem_closedPositive _ (htarget p hp) hp.1.1)
  have hF : ContinuousOn F (Icc 0 A.width ×ˢ c.closedDisk) :=
    ((c.continuousOn_weightedJacobian (A.weights i) (A.weights i).contMDiff.continuous).comp
      jointHeightCoordinates.symm.continuous.continuousOn htarget).mul
        (continuousOn_const.sup (hq.sub continuous_fst.continuousOn))
  have hi : IntegrableOn F (Icc 0 A.width ×ˢ c.disk) :=
    (hF.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
      (prod_mono Subset.rfl Metric.ball_subset_closedBall)
  have hpre : jointHeightCoordinates.symm ⁻¹' c.parameterRegion A.width = Icc 0 A.width ×ˢ c.disk := by
    ext p
    change jointHeightCoordinates (jointHeightCoordinates.symm p) ∈ Icc 0 A.width ×ˢ c.disk ↔ _
    rw [jointHeightCoordinates.apply_symm_apply]
  rw [← (jointHeightCoordinates_symm_measurePreserving.restrict_preimage_emb
    jointHeightCoordinates.symm.toHomeomorph.measurableEmbedding (c.parameterRegion A.width)).integral_comp
      jointHeightCoordinates.symm.toHomeomorph.measurableEmbedding, hpre]
  have heq : (∫ p : ℝ × SurfacePlane in Icc 0 A.width ×ˢ c.disk,
      c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm p) *
        max 0 (shortOverlapGap f z (c.chart.symm (jointHeightCoordinates.symm p)) -
          h (c.chart.symm (jointHeightCoordinates.symm p)))) =
        ∫ p in Icc 0 A.width ×ˢ c.disk, F p := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_ball)
    intro p hp
    dsimp only
    rw [c.height_symm _ (htarget p ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩)]
    rfl
  rw [heq, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hi' : Integrable F ((volume.restrict (Icc 0 A.width)).prod (volume.restrict c.disk)) := by
    simpa only [Measure.volume_eq_prod, Measure.prod_restrict] using hi
  rw [integral_prod_symm F hi']
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  dsimp only
  rw [intervalIntegral.integral_of_le A.width_pos.le, ← integral_Icc_eq_integral_Ioc]

include A in
set_option maxHeartbeats 800000 in
/-- The complete class-E collar has a derived C³ extension with vanishing
one-jet and its full canonical surface Hessian, on a common fixed ball. -/
theorem exists_collarCorrection_twoJet_independent (hf : AdmissibleIndependentTwoFace h f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Displacement → ℝ,
      ContDiffAt ℝ 3 V 0 ∧ V 0 = 0 ∧ fderiv ℝ V 0 = 0 ∧
      (∀ v w : Displacement, fderiv ℝ (fderiv ℝ V) 0 v w =
        ∫ x, (shortGapLinear f x v * shortGapLinear f x w) / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        V z = shortOverlapCollarCorrection h f z := by
  classical
  obtain ⟨ε, κ, N⟩ := hf.exists_rawFaceNeighborhood
  choose d hd η hη₀ hη heq using A.exists_actual_collarFibre_independent hf
  let V : Fin A.count → Displacement → ℝ := fun i => A.chartCorrection i f (η i)
  have hj (i : Fin A.count) := A.chartCorrection_twoJet hf.toRegularHeightPair i (hd i) (η i) (hη₀ i) (hη i)
  have hsmooth (i : Fin A.count) : ContDiffAt ℝ 3 (V i) 0 := (hj i).1
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ δ < ε ∧ δ < A.width / 4 ∧ ∀ i, δ < d i :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds ((gt_mem_nhds N.radius_pos).and
        ((gt_mem_nhds (div_pos A.width_pos (by norm_num))).and
          (eventually_all.mpr fun i => gt_mem_nhds (hd i)))))
  obtain ⟨δ, hδ, hδε, hδw, hδd⟩ := hsmall.exists
  refine ⟨δ, hδ, fun z => ∑ i, V i z, ContDiffAt.sum (fun i _ => hsmooth i), ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_eq_zero (fun i _ => (hj i).2.1)
  · rw [fderiv_sum (fun i _ => (hsmooth i).differentiableAt (by norm_num))]
    exact Finset.sum_eq_zero (fun i _ => (hj i).2.2.1)
  · intro v w
    have he : fderiv ℝ (fun z => ∑ i, V i z) =ᶠ[𝓝 (0 : Displacement)]
        (fun z => ∑ i, fderiv ℝ (V i) z) := by
      filter_upwards [eventually_all.mpr (fun i => (hsmooth i).eventually (by simp))] with z hz
      exact fderiv_sum (fun i _ => (hz i).differentiableAt (by norm_num))
    rw [he.fderiv_eq, fderiv_sum (fun i _ =>
      ((hsmooth i).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.sum_apply]
    calc
      _ = ∑ i, ∫ y in (A.charts i).disk, A.movingWeight i (y, 0) *
          shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) v *
          shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) w :=
        Finset.sum_congr rfl (fun i _ => (hj i).2.2.2 v w)
      _ = _ := A.sum_chartCorrection_hessian hf.toRegularHeightPair v w
  · intro z hz hc
    have hzn : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzε := (norm_snd_le z).trans (hzn.le.trans hδε.le)
    rw [A.shortOverlapCollarCorrection_eq_sum_independent hf N z hzε (by nlinarith [norm_nonneg z])]
    apply Finset.sum_congr rfl
    intro i _
    rw [A.integral_chart_correction_independent N i z hzε]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact (heq i y (Metric.ball_subset_closedBall hy) z
      (by simpa only [Metric.mem_ball, dist_zero_right] using hzn.trans (hδd i)) hc).symm

end ControlledCollarAtlas
end BoundaryDraft
