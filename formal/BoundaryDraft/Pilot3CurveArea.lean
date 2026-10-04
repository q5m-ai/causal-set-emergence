import BoundaryDraft.Pilot3Curve
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The variable-speed Hausdorff curve area formula

Local finiteness, absolute continuity and exact shrinking-interval density
are derived from one-dimensional distortion and tangent-line normalization.
Lebesgue differentiation identifies the canonical Hausdorff pullback; no area
formula or chosen measure is a hypothesis.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace BoundaryDraft

theorem pilot3CurvePullback_locallyFinite {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    IsLocallyFiniteMeasure (pilot3CurvePullback g) := by
  constructor
  intro x
  obtain ⟨r, hr, _, hb⟩ := pilot3Curve_local_measure_bounds g hg.continuous univ isOpen_univ
    hg.contDiffOn x (mem_univ x) (1 / 2) (by norm_num)
      (by exact_mod_cast (show (1 / 2 : ℝ) < 1 by norm_num))
  refine ⟨ball x r, ball_mem_nhds x hr, (hb _ (Subset.refl _)).2.trans_lt ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top isBounded_ball.measure_lt_top

theorem pilot3CurvePullback_absolutelyContinuous {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    pilot3CurvePullback g ≪ volume := by
  intro s hs
  apply measure_null_of_locally_null s
  intro x _
  obtain ⟨r, hr, _, hb⟩ := pilot3Curve_local_measure_bounds g hg.continuous univ isOpen_univ
    hg.contDiffOn x (mem_univ x) (1 / 2) (by norm_num)
      (by exact_mod_cast (show (1 / 2 : ℝ) < 1 by norm_num))
  refine ⟨ball x r ∩ s, ?_, ?_⟩
  · simpa only [inter_comm] using inter_mem_nhdsWithin s (ball_mem_nhds x hr)
  apply le_antisymm _ (zero_le _)
  have hz : volume (ball x r ∩ s) = 0 := measure_mono_null inter_subset_right hs
  simpa only [hz, mul_zero] using (hb (ball x r ∩ s) inter_subset_left).2

theorem pilot3CurvePullback_tendsto_closedBall_ratio {g : ℝ → ℝ} (hg : Continuous g)
    (U : Set ℝ) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) (x : ℝ) (hx : x ∈ U) :
    Tendsto (fun r => pilot3CurvePullback g (closedBall x r) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (pilot3CurveJacobian g x))) := by
  let j := pilot3CurveJacobian g x
  have hb (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ((1 - ε) * j) ≤ pilot3CurvePullback g (closedBall x r) / volume (closedBall x r) ∧
      pilot3CurvePullback g (closedBall x r) / volume (closedBall x r) ≤ ENNReal.ofReal ((1 + ε) * j) := by
    obtain ⟨R, hR, _, hbounds⟩ := pilot3Curve_local_measure_bounds g hg U hU hgU x hx
      ⟨ε, hε.1.le⟩ hε.1 hε.2
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hR)] with r hr0 hrR
    have hvol0 : volume (closedBall x r) ≠ 0 := (measure_closedBall_pos volume x hr0).ne'
    have hvoltop : volume (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
    have hh := hbounds (closedBall x r) (closedBall_subset_ball hrR)
    have hlo := ENNReal.div_le_div_right hh.1 (volume (closedBall x r))
    have hup := ENNReal.div_le_div_right hh.2 (volume (closedBall x r))
    rw [ENNReal.mul_div_cancel_right hvol0 hvoltop] at hlo hup
    exact ⟨hlo, hup⟩
  have hl : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) * j)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal j)) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 - ε) * j)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa only [sub_zero, one_mul] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hu : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * j)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal j)) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 + ε) * j)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa only [add_zero, one_mul] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one))
  apply tendsto_order.2
  constructor
  · intro c hc
    obtain ⟨ε, hε, hcε⟩ := (he.and ((tendsto_order.1 hl).1 c hc)).exists
    exact (hb ε hε).mono fun r hr => hcε.trans_le hr.1
  · intro c hc
    obtain ⟨ε, hε, hεc⟩ := (he.and ((tendsto_order.1 hu).2 c hc)).exists
    exact (hb ε hε).mono fun r hr => hr.2.trans_lt hεc

/-- Canonical one-measure equals the actual speed-weighted parameter measure. -/
theorem pilot3CurvePullback_eq_withDensity {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    pilot3CurvePullback g = volume.withDensity (fun x => ENNReal.ofReal (pilot3CurveJacobian g x)) := by
  letI := pilot3CurvePullback_locallyFinite hg
  have hd : (pilot3CurvePullback g).rnDeriv volume =ᵐ[volume]
      (fun x => ENNReal.ofReal (pilot3CurveJacobian g x)) := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv (pilot3CurvePullback g) volume] with x hx
    exact tendsto_nhds_unique hx (pilot3CurvePullback_tendsto_closedBall_ratio hg.continuous
      univ isOpen_univ hg.contDiffOn x (mem_univ x))
  rw [← Measure.withDensity_rnDeriv_eq (pilot3CurvePullback g) volume
    (pilot3CurvePullback_absolutelyContinuous hg)]
  exact withDensity_congr_ae hd

theorem continuous_pilot3CurveJacobian {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (pilot3CurveJacobian g) := by
  have hc := hg.continuous_fderiv le_rfl
  change Continuous (fun u => ‖pilot3Coordinates.symm (fderiv ℝ g u 1, (1 : ℝ))‖)
  exact (pilot3Coordinates.symm.continuous.comp ((hc.clm_apply continuous_const).prodMk continuous_const)).norm

theorem measurable_pilot3CurveJacobian (g : ℝ → ℝ) : Measurable (pilot3CurveJacobian g) := by
  change Measurable (fun u => ‖pilot3Coordinates.symm (fderiv ℝ g u 1, (1 : ℝ))‖)
  have he : Continuous (fun L : ℝ →L[ℝ] ℝ => L 1) := continuous_id.clm_apply continuous_const
  exact (pilot3Coordinates.symm.continuous.measurable.comp
    ((he.measurable.comp (measurable_fderiv ℝ g)).prodMk measurable_const)).norm

theorem pilot3_hausdorff_restrict_curve {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    (μH[1] : Measure Pilot3Space).restrict (range (pilot3Curve g)) =
      Measure.map (pilot3Curve g) (volume.withDensity (fun u => ENNReal.ofReal (pilot3CurveJacobian g u))) := by
  rw [← pilot3CurvePullback_eq_withDensity hg]
  exact ((continuous_measurableEmbedding_pilot3Curve hg.continuous).map_comap _).symm

/-- Equality of measures on every Borel parameter subset, not just total lengths. -/
theorem pilot3_hausdorff_restrict_curve_image {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (μH[1] : Measure Pilot3Space).restrict (pilot3Curve g '' s) =
      Measure.map (pilot3Curve g) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (pilot3CurveJacobian g u))) := by
  let hf := continuous_measurableEmbedding_pilot3Curve hg.continuous
  rw [← restrict_withDensity hs]
  have he := hf.restrict_map (volume.withDensity (fun u => ENNReal.ofReal (pilot3CurveJacobian g u)))
    (pilot3Curve g '' s)
  rw [hf.injective.preimage_image, ← pilot3_hausdorff_restrict_curve hg,
    Measure.restrict_restrict_of_subset (image_subset_range _ _)] at he
  exact he

end BoundaryDraft
