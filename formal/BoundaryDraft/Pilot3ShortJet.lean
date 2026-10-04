import BoundaryDraft.Pilot3ShortCollar
import BoundaryDraft.Pilot3AtlasRegularity
import BoundaryDraft.MovingCollarJet

/-!
# The direct-origin absolute overlap two-jet for `SmoothPilot3`

The extension is constructed from the unchanged smooth pilot alone. Its
constant point volume, time-linear slice area, spatial gradient, bulk future
Hessian and complete canonical surface square are all retained. Only the
collar is partitioned. This is a geometry producer, not an action-limit or
sample-wise convergence theorem.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

/-- First displacement differential of the actual lost vertical slice. -/
def pilot3ShortGapLinear (f : Pilot3Space → ℝ) (x : Pilot3Space) : Pilot3Spacetime →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ Pilot3Space -
    (fderiv ℝ f x).comp (ContinuousLinearMap.snd ℝ ℝ Pilot3Space)

@[simp] theorem pilot3ShortGapLinear_apply (f : Pilot3Space → ℝ) (x : Pilot3Space) (z : Pilot3Spacetime) :
    pilot3ShortGapLinear f x z = z.1 - fderiv ℝ f x z.2 := rfl

namespace Pilot3CollarChart
variable {h f : Pilot3Space → ℝ} (c : Pilot3CollarChart h)

/-- At zero displacement the chart-height differential cancels, leaving the
actual future differential rather than a tangent-plane replacement. -/
theorem hasFDerivAt_movingGap_zero (hf : SmoothPilot3 h f) (y : ℝ)
    (hy : y ∈ c.closedDisk) :
    HasFDerivAt (fun p : Pilot3Spacetime × ℝ => c.movingGap f ((y, p.1), p.2))
      ((pilot3ShortGapLinear f (c.chart.symm (pilot3Coordinates.symm (0, y)))).comp
        (ContinuousLinearMap.fst ℝ Pilot3Spacetime ℝ)) (0, 0) := by
  let x := c.chart.symm (pilot3Coordinates.symm (0, y))
  let φ : Pilot3Spacetime × ℝ → Pilot3Space := fun p => c.movingPoint ((y, p.1), p.2)
  have ht : pilot3Coordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hx : x ∈ pilot3ClosedPositive h := c.symm_mem_closedPositive _ ht le_rfl
  have hφ : ContDiffAt ℝ 3 φ (0, 0) :=
    (c.contDiffAt_symm_three _ ht).comp (0, 0)
      (pilot3Coordinates.symm.contDiff.contDiffAt.comp (0, 0)
        (contDiffAt_snd.prodMk contDiffAt_const))
  let D := fderiv ℝ f x
  have hD : HasFDerivAt f D x :=
    ((hf.future_contDiffAt_three x hx).differentiableAt (by norm_num)).hasFDerivAt
  have hDb : HasFDerivAt f D (φ (0, 0) + (0 : Pilot3Spacetime).2) := by
    simpa [φ, x, movingPoint] using hD
  let S : Pilot3Spacetime × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ Pilot3Space).comp (ContinuousLinearMap.fst ℝ Pilot3Spacetime ℝ)
  let B : Pilot3Spacetime × ℝ →L[ℝ] Pilot3Space :=
    (ContinuousLinearMap.snd ℝ ℝ Pilot3Space).comp (ContinuousLinearMap.fst ℝ Pilot3Spacetime ℝ)
  have hφD : HasFDerivAt φ (fderiv ℝ φ (0, 0)) (0, 0) :=
    (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have he : HasFDerivAt (fun p : Pilot3Spacetime × ℝ => c.movingGap f ((y, p.1), p.2))
      (S - D.comp (fderiv ℝ φ (0, 0) + B) + D.comp (fderiv ℝ φ (0, 0))) (0, 0) :=
    (S.hasFDerivAt.sub (hDb.comp (0, 0) (hφD.add B.hasFDerivAt))).add (hD.comp (0, 0) hφD)
  apply he.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change v.1.1 - D (fderiv ℝ φ (0, 0) v + v.1.2) + D (fderiv ℝ φ (0, 0) v) =
    v.1.1 - D v.1.2
  rw [map_add]
  ring

end Pilot3CollarChart
namespace Pilot3CollarAtlas
variable {h f : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

/-- The existing chart Jacobian and partition, in base-first order. -/
def movingWeight (i : Fin A.count) (p : ℝ × ℝ) : ℝ :=
  (A.charts i).weightedJacobian (A.weights i) (pilot3Coordinates.symm (p.2, p.1))

theorem contDiffAt_movingWeight (i : Fin A.count) (y : ℝ)
    (hy : y ∈ (A.charts i).closedDisk) : ContDiffAt ℝ 2 (A.movingWeight i) (y, 0) := by
  let c := A.charts i
  have ht : pilot3Coordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hw : ContDiffAt ℝ ∞ (A.weights i) (c.chart.symm (pilot3Coordinates.symm (0, y))) :=
    (A.weights i).contMDiff.contDiff.contDiffAt
  exact ((c.contDiffAt_weightedJacobian (A.weights i) _ ht hw).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp (y, 0)
    (pilot3Coordinates.symm.contDiff.contDiffAt.comp (y, 0)
      (contDiffAt_snd.prodMk contDiffAt_fst))

/-- The chosen uniform actual root determines a fixed-disk extension. -/
def chartCorrection (i : Fin A.count) (f : Pilot3Space → ℝ)
    (η : ℝ × Pilot3Spacetime → ℝ) (z : Pilot3Spacetime) : ℝ :=
  ∫ y in (A.charts i).disk,
    MovingCollar.parametricFibre (A.movingWeight i) ((A.charts i).movingGap f) η (y, z)

set_option maxHeartbeats 800000 in
/-- True moving-fibre jets integrate to the chart Hessian. The root premises
are discharged by `exists_actual_collarFibre` in the complete theorem below. -/
theorem chartCorrection_twoJet (hf : SmoothPilot3 h f) (i : Fin A.count)
    {δ : ℝ} (hδ : 0 < δ) (η : ℝ × Pilot3Spacetime → ℝ)
    (hη₀ : ∀ y ∈ (A.charts i).closedDisk, η (y, 0) = 0)
    (hη : ∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ,
      ContDiffAt ℝ 3 η (y, z) ∧ η (y, z) = (A.charts i).movingGap f ((y, z), η (y, z))) :
    ContDiffAt ℝ 3 (A.chartCorrection i f η) 0 ∧ A.chartCorrection i f η 0 = 0 ∧
      fderiv ℝ (A.chartCorrection i f η) 0 = 0 ∧
      ∀ v w : Pilot3Spacetime,
        fderiv ℝ (fderiv ℝ (A.chartCorrection i f η)) 0 v w =
          ∫ y in (A.charts i).disk, A.movingWeight i (y, 0) *
            pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) v *
            pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) w := by
  let c := A.charts i
  let W := A.movingWeight i
  let q := c.movingGap f
  let μ : Measure ℝ := volume.restrict c.disk
  have hm : μ.restrict c.closedDisk = μ := by
    dsimp only [μ, Pilot3CollarChart.disk, Pilot3CollarChart.closedDisk]
    rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_right.mpr Metric.ball_subset_closedBall]
  have hr (y : ℝ) (hy : y ∈ c.closedDisk) :
      ∀ᶠ z in 𝓝 (0 : Pilot3Spacetime), η (y, z) = q ((y, z), η (y, z)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Pilot3Spacetime) hδ] with z hz
    exact (hη y hy z hz).2
  have hηy (y : ℝ) (hy : y ∈ c.closedDisk) :
      ContDiffAt ℝ 3 (fun z : Pilot3Spacetime => η (y, z)) 0 :=
    (hη y hy 0 (Metric.mem_ball_self hδ)).1.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hqy (y : ℝ) (hy : y ∈ c.closedDisk) :
      ContDiffAt ℝ 3 (fun p : Pilot3Spacetime × ℝ => q ((y, p.1), p.2)) (0, 0) :=
    (c.contDiffAt_movingGap_zero hf y hy).comp (0, 0)
      ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  have hWy (y : ℝ) (hy : y ∈ c.closedDisk) :
      ContDiffAt ℝ 2 (fun t => W (y, t)) 0 :=
    (A.contDiffAt_movingWeight i y hy).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  let F : Pilot3Spacetime × ℝ → ℝ := fun p => MovingCollar.parametricFibre W q η (p.2, p.1)
  have hF (y : ℝ) (hy : y ∈ c.closedDisk) : ContDiffAt ℝ 2 F (0, y) :=
    (MovingCollar.contDiffAt_parametricFibre_two (hη₀ y hy) (A.contDiffAt_movingWeight i y hy)
      ((c.contDiffAt_movingGap_zero hf y hy).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
      ((hη y hy 0 (Metric.mem_ball_self hδ)).1.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))).comp
        (0, y) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hj := MovingCollar.integral_twoJet (μ := μ) (F := F) (x₀ := (0 : Pilot3Spacetime))
    (K := c.closedDisk) (isCompact_closedBall _ _) hF
  simp only [IntegrableOn, hm] at hj
  have hone (y : ℝ) (hy : y ∈ c.closedDisk) :
      F (0, y) = 0 ∧ fderiv ℝ (fun z => F (z, y)) 0 = 0 :=
    MovingCollar.fibre_vanishing_oneJet (W := fun t => W (y, t))
      (q := fun p : Pilot3Spacetime × ℝ => q ((y, p.1), p.2)) (η := fun z => η (y, z))
      (hWy y hy) (hqy y hy) (hηy y hy) (hη₀ y hy) (hr y hy)
  have htwo (y : ℝ) (hy : y ∈ c.closedDisk) (v w : Pilot3Spacetime) :
      fderiv ℝ (fderiv ℝ (fun z => F (z, y))) 0 v w = W (y, 0) *
        pilot3ShortGapLinear f (c.chart.symm (pilot3Coordinates.symm (0, y))) v *
        pilot3ShortGapLinear f (c.chart.symm (pilot3Coordinates.symm (0, y))) w := by
    have he := MovingCollar.fderiv_fderiv_fibre (W := fun t => W (y, t))
      (q := fun p : Pilot3Spacetime × ℝ => q ((y, p.1), p.2)) (η := fun z => η (y, z))
      (hWy y hy) (hqy y hy) (hηy y hy) (hη₀ y hy)
      (fun t => by simp [q, Pilot3CollarChart.movingGap]) (hr y hy) v w
    rw [(c.hasFDerivAt_movingGap_zero hf y hy).fderiv] at he
    exact he
  have heF : (fun z => ∫ y in c.closedDisk, F (z, y) ∂μ) = A.chartCorrection i f η := by
    funext z
    change (∫ y, F (z, y) ∂μ.restrict c.closedDisk) = _
    rw [hm]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← heF]
    exact MovingCollar.contDiffAt_averagedFibre (μ := μ) (W := W) (q := q) (η := η)
      (K := c.closedDisk) (isCompact_closedBall _ _) hδ
      (A.contDiffAt_movingWeight i) (c.contDiffAt_movingGap_zero hf)
      (fun y hy => (hη y hy 0 (Metric.mem_ball_self hδ)).1) hη₀
      (fun y hy z hz => (hη y hy z hz).2)
  · apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact (hone y (Metric.ball_subset_closedBall hy)).1
  · have he := hj.2.2.1.fderiv
    change fderiv ℝ (A.chartCorrection i f η) 0 = ∫ y, fderiv ℝ (fun z => F (z, y)) 0 ∂μ at he
    rw [he]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact (hone y (Metric.ball_subset_closedBall hy)).2
  · intro v w
    have he := hj.2.2.2
    change fderiv ℝ (fderiv ℝ (A.chartCorrection i f η)) 0 =
      ∫ y, fderiv ℝ (fderiv ℝ (fun z => F (z, y))) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.2.1,
      ContinuousLinearMap.integral_apply (hj.2.1.apply_continuousLinearMap v)]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact htwo y (Metric.ball_subset_closedBall hy) v w

/-- The complete partition gives the fixed canonical Hausdorff-one surface
measure, with the reciprocal norm of the actual height gradient. -/
theorem sum_chartCorrection_hessian (hf : SmoothPilot3 h f) (v w : Pilot3Spacetime) :
    (∑ i, ∫ y in (A.charts i).disk, A.movingWeight i (y, 0) *
      pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) v *
      pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) w) =
        ∫ x, (pilot3ShortGapLinear f x v * pilot3ShortGapLinear f x w) / ‖pilot3Gradient h x‖
          ∂pilot3SurfaceMeasure h := by
  have hD : ContinuousOn (fderiv ℝ f) (pilot3ClosedPositive h) :=
    fun x hx => ((hf.future_contDiffAt_three x hx).fderiv_right (m := 2)
      (by norm_num)).continuousAt.continuousWithinAt
  have hc (u : Pilot3Spacetime) : ContinuousOn (fun x => pilot3ShortGapLinear f x u) (pilot3ClosedPositive h) :=
    continuousOn_const.sub (hD.clm_apply continuousOn_const)
  have he := A.weightedHeightDensity_eq_sum hf.toPilot3RegularHeight
    (fun x => pilot3ShortGapLinear f x v * pilot3ShortGapLinear f x w) ((hc v).mul (hc w)) 0
      ⟨le_rfl, A.width_pos.le⟩
  rw [pilot3WeightedHeightDensity_zero] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  change (A.movingWeight i (y, 0) *
      pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) v) *
      pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) w =
    A.movingWeight i (y, 0) *
      (pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) v *
        pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) w)
  exact mul_assoc _ _ _

include A in
set_option maxHeartbeats 800000 in
/-- Geometry alone supplies the complete collar C³ extension, vanishing
one-jet, and canonical bilinear surface term on a single fixed causal ball. -/
theorem exists_collarCorrection_twoJet (hf : SmoothPilot3 h f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Pilot3Spacetime → ℝ,
      ContDiffAt ℝ 3 V 0 ∧ V 0 = 0 ∧ fderiv ℝ V 0 = 0 ∧
      (∀ v w : Pilot3Spacetime, fderiv ℝ (fderiv ℝ V) 0 v w =
        ∫ x, (pilot3ShortGapLinear f x v * pilot3ShortGapLinear f x w) / ‖pilot3Gradient h x‖
          ∂pilot3SurfaceMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ, ‖z.2‖ ≤ z.1 →
        V z = pilot3ShortCollarCorrection h f z := by
  classical
  choose d hd η hη₀ hη heq using A.exists_actual_collarFibre hf
  let V : Fin A.count → Pilot3Spacetime → ℝ := fun i => A.chartCorrection i f (η i)
  have hj (i : Fin A.count) := A.chartCorrection_twoJet hf i (hd i) (η i) (hη₀ i) (hη i)
  have hsmooth (i : Fin A.count) : ContDiffAt ℝ 3 (V i) 0 := (hj i).1
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ δ < A.width / 4 ∧ ∀ i, δ < d i :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds ((gt_mem_nhds (div_pos A.width_pos (by norm_num))).and
        (eventually_all.mpr fun i => gt_mem_nhds (hd i))))
  obtain ⟨δ, hδ, hδw, hδd⟩ := hsmall.exists
  refine ⟨δ, hδ, fun z => ∑ i, V i z, ContDiffAt.sum (fun i _ => hsmooth i), ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_eq_zero (fun i _ => (hj i).2.1)
  · rw [fderiv_sum (fun i _ => (hsmooth i).differentiableAt (by norm_num))]
    exact Finset.sum_eq_zero (fun i _ => (hj i).2.2.1)
  · intro v w
    have he : fderiv ℝ (fun z => ∑ i, V i z) =ᶠ[𝓝 (0 : Pilot3Spacetime)]
        (fun z => ∑ i, fderiv ℝ (V i) z) := by
      filter_upwards [eventually_all.mpr (fun i => (hsmooth i).eventually (by simp))] with z hz
      exact fderiv_sum (fun i _ => (hz i).differentiableAt (by norm_num))
    rw [he.fderiv_eq, fderiv_sum (fun i _ =>
      ((hsmooth i).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.sum_apply]
    calc
      _ = ∑ i, ∫ y in (A.charts i).disk, A.movingWeight i (y, 0) *
          pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) v *
          pilot3ShortGapLinear f ((A.charts i).chart.symm (pilot3Coordinates.symm (0, y))) w :=
        Finset.sum_congr rfl (fun i _ => (hj i).2.2.2 v w)
      _ = _ := A.sum_chartCorrection_hessian hf v w
  · intro z hz hc
    have hzn : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [A.shortCollarCorrection_eq_sum hf z (by nlinarith [norm_nonneg z])]
    apply Finset.sum_congr rfl
    intro i _
    rw [A.integral_chart_correction hf i z]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact (heq i y (Metric.ball_subset_closedBall hy) z
      (by simpa only [Metric.mem_ball, dist_zero_right] using hzn.trans (hδd i)) hc).symm

end Pilot3CollarAtlas

/-- The fixed-domain future-face increment. No collar charts are used here. -/
def pilot3ShortBulk (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime) : ℝ :=
  ∫ x in {x | 0 < h x}, f (x + z.2) - f x

private theorem pilot3_hasFDerivAt_bulkSlice {g : Pilot3Space → ℝ} {x : Pilot3Space}
    (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (fun z : Pilot3Spacetime => g (x + z.2) - g x)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.snd ℝ ℝ Pilot3Space)) 0 := by
  have ht : HasFDerivAt (fun z : Pilot3Spacetime => x + z.2)
      (ContinuousLinearMap.snd ℝ ℝ Pilot3Space) 0 := by
    simpa only [zero_add] using (hasFDerivAt_const x (0 : Pilot3Spacetime)).add
      (hasFDerivAt_snd (p := (0 : Pilot3Spacetime)) (𝕜 := ℝ))
  have hg' : HasFDerivAt g (fderiv ℝ g x) (x + (0 : Pilot3Spacetime).2) := by
    simpa using hg.hasFDerivAt
  exact (hg'.comp (f := fun z : Pilot3Spacetime => x + z.2) 0 ht).sub_const (g x)

private theorem pilot3_fderiv_fderiv_bulkSlice {g : Pilot3Space → ℝ} {x : Pilot3Space}
    (hg : ContDiffAt ℝ 3 g x) (v w : Pilot3Spacetime) :
    fderiv ℝ (fderiv ℝ (fun z : Pilot3Spacetime => g (x + z.2) - g x)) 0 v w =
      fderiv ℝ (fderiv ℝ g) x v.2 w.2 := by
  let S : Pilot3Spacetime →L[ℝ] Pilot3Space := ContinuousLinearMap.snd ℝ ℝ Pilot3Space
  let T : Pilot3Spacetime → Pilot3Space := fun z => x + z.2
  have hT (z : Pilot3Spacetime) : HasFDerivAt T S z := by
    simpa only [zero_add] using (hasFDerivAt_const x z).add
      (hasFDerivAt_snd (p := z) (𝕜 := ℝ))
  have he : fderiv ℝ (fun z : Pilot3Spacetime => g (x + z.2) - g x) =ᶠ[𝓝 0]
      (fun z => (fderiv ℝ g (T z)).comp S) := by
    have hh : ∀ᶠ z in 𝓝 (0 : Pilot3Spacetime), ContDiffAt ℝ 3 g (T z) := by
      have ht : Tendsto T (𝓝 (0 : Pilot3Spacetime)) (𝓝 x) := by
        simpa [T] using (hT 0).continuousAt.tendsto
      exact ht.eventually (hg.eventually (by simp))
    filter_upwards [hh] with z hz
    exact (((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z (hT z)).sub_const (g x)).fderiv
  have hD : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) (T 0) := by
    simpa [T] using ((hg.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hH := (hD.comp 0 (hT 0)).clm_comp (hasFDerivAt_const S (0 : Pilot3Spacetime))
  have hHeq := hH.fderiv
  dsimp only [Function.comp_apply] at hHeq
  rw [he.fderiv_eq, hHeq]
  simp [ContinuousLinearMap.comp_apply, S]

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

/-- Joint smoothness and compact parameter differentiation keep every point
of the fixed interior, including positive-height critical points. -/
theorem contDiffAt_shortBulk : ContDiffAt ℝ 3 (pilot3ShortBulk h f) 0 := by
  let μ : Measure Pilot3Space := volume.restrict {x | 0 < h x}
  have hs := hf.toPilot3RegularHeight.isCompact_closedPositive
  have he : (fun z : Pilot3Spacetime => ∫ x in pilot3ClosedPositive h,
      f (x + z.2) - f x ∂μ) = pilot3ShortBulk h f := by
    funext z
    have hm : μ.restrict (pilot3ClosedPositive h) = μ := by
      dsimp [μ]
      rw [Measure.restrict_restrict hs.measurableSet,
        inter_eq_right.mpr (show {x | 0 < h x} ⊆ pilot3ClosedPositive h from subset_closure)]
    change ∫ x, (f (x + z.2) - f x) ∂μ.restrict (pilot3ClosedPositive h) = _
    rw [hm]
    rfl
  rw [← he]
  apply MovingCollar.contDiffAt_integral_compact 3 hs
    (F := fun p : Pilot3Spacetime × Pilot3Space => f (p.2 + p.1.2) - f p.2)
  intro x hx
  have hfx := hf.future_contDiffAt_three x hx
  have hfb : ContDiffAt ℝ 3 f (x + (0 : Pilot3Spacetime).2) := by simpa using hfx
  exact (hfb.comp (0, x) (contDiffAt_snd.add contDiffAt_fst.snd)).sub
    (hfx.comp (0, x) contDiffAt_snd)

/-- Fixed-domain two-jet with the actual future Hessian. -/
theorem shortBulk_twoJet : ContDiffAt ℝ 3 (pilot3ShortBulk h f) 0 ∧
    pilot3ShortBulk h f 0 = 0 ∧
    (∀ v : Pilot3Spacetime, fderiv ℝ (pilot3ShortBulk h f) 0 v =
      ∫ x in {x | 0 < h x}, fderiv ℝ f x v.2) ∧
    ∀ v w : Pilot3Spacetime, fderiv ℝ (fderiv ℝ (pilot3ShortBulk h f)) 0 v w =
      ∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x v.2 w.2 := by
  let μ : Measure Pilot3Space := volume.restrict {x | 0 < h x}
  let F : Pilot3Spacetime × Pilot3Space → ℝ := fun p => f (p.2 + p.1.2) - f p.2
  have hm : μ.restrict (pilot3ClosedPositive h) = μ := by
    dsimp only [μ]
    rw [Measure.restrict_restrict hf.toPilot3RegularHeight.isCompact_closedPositive.measurableSet,
      inter_eq_right.mpr (show {x | 0 < h x} ⊆ pilot3ClosedPositive h from subset_closure)]
  have hF (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) : ContDiffAt ℝ 2 F (0, x) := by
    have hfx := hf.future_contDiffAt_three x hx
    have hfb : ContDiffAt ℝ 3 f (x + (0 : Pilot3Spacetime).2) := by simpa using hfx
    exact ((hfb.comp (0, x) (contDiffAt_snd.add contDiffAt_fst.snd)).sub
      (hfx.comp (0, x) contDiffAt_snd)).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hj := MovingCollar.integral_twoJet (μ := μ) (F := F) (x₀ := (0 : Pilot3Spacetime))
    hf.toPilot3RegularHeight.isCompact_closedPositive hF
  simp only [IntegrableOn, hm] at hj
  refine ⟨hf.contDiffAt_shortBulk, by simp [pilot3ShortBulk], ?_, ?_⟩
  · intro v
    have he := hj.2.2.1.fderiv
    change fderiv ℝ (pilot3ShortBulk h f) 0 = ∫ x, fderiv ℝ (fun z => F (z, x)) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.1]
    apply setIntegral_congr_fun hf.toPilot3RegularHeight.isOpen_positive.measurableSet
    intro x hx
    have hd := pilot3_hasFDerivAt_bulkSlice
      ((hf.future_contDiffAt_three x (subset_closure hx)).differentiableAt (by norm_num))
    exact congrArg (fun L : Pilot3Spacetime →L[ℝ] ℝ => L v) hd.fderiv
  · intro v w
    have he := hj.2.2.2
    change fderiv ℝ (fderiv ℝ (pilot3ShortBulk h f)) 0 =
      ∫ x, fderiv ℝ (fderiv ℝ (fun z => F (z, x))) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.2.1,
      ContinuousLinearMap.integral_apply (hj.2.1.apply_continuousLinearMap v)]
    apply setIntegral_congr_fun hf.toPilot3RegularHeight.isOpen_positive.measurableSet
    intro x hx
    exact pilot3_fderiv_fderiv_bulkSlice (hf.future_contDiffAt_three x (subset_closure hx)) v w

/-- Absolute integrability of the canonical surface Hessian. -/
theorem integrable_shortGapLinear_pair (v w : Pilot3Spacetime) :
    Integrable (fun x => (pilot3ShortGapLinear f x v * pilot3ShortGapLinear f x w) / ‖pilot3Gradient h x‖)
      (pilot3SurfaceMeasure h) := by
  obtain ⟨A⟩ := hf.toPilot3RegularHeight.exists_collarAtlas
  have hD : ContinuousOn (fderiv ℝ f) (pilot3ClosedPositive h) :=
    fun x hx => ((hf.future_contDiffAt_three x hx).fderiv_right (m := 2)
      (by norm_num)).continuousAt.continuousWithinAt
  have hc (u : Pilot3Spacetime) : ContinuousOn (fun x => pilot3ShortGapLinear f x u) (pilot3ClosedPositive h) :=
    continuousOn_const.sub (hD.clm_apply continuousOn_const)
  exact A.integrable_level_weight_div hf.toPilot3RegularHeight
    (fun x => pilot3ShortGapLinear f x v * pilot3ShortGapLinear f x w) ((hc v).mul (hc w)) 0
      ⟨le_rfl, A.width_pos.le⟩

/-- Exact absolute identity before taking derivatives. No planar comparison
cancels the point volume or the moving time slice. -/
theorem overlap_eq_absolute_bulk (z : Pilot3Spacetime) (hc : ‖z.2‖ ≤ z.1) :
    pilot3Overlap h f z =
      volume.real (pilot3Region h f) - z.1 * volume.real {x | 0 < h x} +
        pilot3ShortBulk h f z + pilot3ShortCollarCorrection h f z := by
  have hi : IntegrableOn (fun _ : Pilot3Space => z.1) {x | 0 < h x} :=
    (continuous_const.continuousOn.integrableOn_compact
      hf.toPilot3RegularHeight.isCompact_closedPositive).mono_set subset_closure
  have hq : IntegrableOn (pilot3ShortGap f z) {x | 0 < h x} := by
    simpa only [one_mul] using hf.integrableOn_weighted_shortGap (fun _ => 1) continuousOn_const z
  have he : pilot3ShortBulk h f z = z.1 * volume.real {x | 0 < h x} -
      ∫ x in {x | 0 < h x}, pilot3ShortGap f z x := by
    calc
      _ = ∫ x in {x | 0 < h x}, z.1 - pilot3ShortGap f z x := by
        apply integral_congr_ae
        filter_upwards with x
        unfold pilot3ShortGap
        ring
      _ = _ := by rw [integral_sub hi hq]; simp [mul_comm]
  have ha := hf.weightedOverlap_eq_bulk_add_correction (fun _ => 1) continuousOn_const z hc
  simp only [one_mul] at ha
  change pilot3Overlap h f z = _ at ha
  rw [← hf.volume_region] at ha
  rw [ha, he]
  dsimp only [pilot3ShortCollarCorrection, Measure.real]
  ring

set_option maxHeartbeats 800000 in
/-- The complete absolute overlap C³ extension and two-jet, derived solely
from the unchanged `SmoothPilot3`. The surface term uses the independently
fixed canonical line measure, and equality holds for the actual covariogram
on the entire causal ball, including the vertex and null displacements. -/
theorem exists_absoluteOverlap_twoJet :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Pilot3Spacetime → ℝ,
      ContDiffAt ℝ 3 F 0 ∧ F 0 = volume.real (pilot3Region h f) ∧
      (∀ v : Pilot3Spacetime, fderiv ℝ F 0 v =
        -v.1 * volume.real {x | 0 < h x} +
          ∫ x in {x | 0 < h x}, inner (𝕜 := ℝ) (pilot3Gradient f x) v.2) ∧
      (∀ v w : Pilot3Spacetime, fderiv ℝ (fderiv ℝ F) 0 v w =
        (∫ x in {x | 0 < h x}, fderiv ℝ (fderiv ℝ f) x v.2 w.2) +
        ∫ x, ((v.1 - inner (𝕜 := ℝ) (pilot3Gradient f x) v.2) *
          (w.1 - inner (𝕜 := ℝ) (pilot3Gradient f x) w.2)) / ‖pilot3Gradient h x‖
          ∂pilot3SurfaceMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ, ‖z.2‖ ≤ z.1 → F z = pilot3Overlap h f z := by
  obtain ⟨A⟩ := hf.toPilot3RegularHeight.exists_collarAtlas
  obtain ⟨δ, hδ, V, hV, hV₀, hV₁, hV₂, heV⟩ := A.exists_collarCorrection_twoJet hf
  obtain ⟨hB, hB₀, hB₁, hB₂⟩ := hf.shortBulk_twoJet
  let L : Pilot3Spacetime →L[ℝ] ℝ :=
    (-volume.real {x | 0 < h x}) • ContinuousLinearMap.fst ℝ ℝ Pilot3Space
  let U : Pilot3Spacetime → ℝ := fun z => volume.real (pilot3Region h f) + L z
  have hU : ContDiff ℝ 3 U := contDiff_const.add L.contDiff
  have hUD (z : Pilot3Spacetime) : fderiv ℝ U z = L := by
    simpa only [zero_add] using
      ((hasFDerivAt_const (volume.real (pilot3Region h f)) z).add L.hasFDerivAt).fderiv
  let F : Pilot3Spacetime → ℝ := fun z => U z + pilot3ShortBulk h f z + V z
  have hF : ContDiffAt ℝ 3 F 0 := (hU.contDiffAt.add hB).add hV
  refine ⟨δ, hδ, F, hF, by simp [F, U, hB₀, hV₀], ?_, ?_, ?_⟩
  · intro v
    dsimp only [F]
    rw [fderiv_add ((hU.differentiable (by norm_num) 0).add (hB.differentiableAt (by norm_num)))
      (hV.differentiableAt (by norm_num)), fderiv_add (hU.differentiable (by norm_num) 0)
        (hB.differentiableAt (by norm_num)), hV₁, hUD]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, add_zero, hB₁]
    simp only [pilot3_differential_eq_inner]
    dsimp [L]
    ring
  · intro v w
    have heD : fderiv ℝ F =ᶠ[𝓝 (0 : Pilot3Spacetime)]
        (fun z => L + fderiv ℝ (pilot3ShortBulk h f) z + fderiv ℝ V z) := by
      filter_upwards [hB.eventually (by simp), hV.eventually (by simp)] with z hzB hzV
      dsimp only [F]
      rw [fderiv_add ((hU.differentiable (by norm_num) z).add (hzB.differentiableAt (by norm_num)))
        (hzV.differentiableAt (by norm_num)), fderiv_add (hU.differentiable (by norm_num) z)
          (hzB.differentiableAt (by norm_num)), hUD]
    have hDB := (hB.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hDV := (hV.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    rw [heD.fderiv_eq, fderiv_add (differentiableAt_const L |>.add hDB) hDV,
      fderiv_const_add L]
    simp only [ContinuousLinearMap.add_apply, hB₂, hV₂,
      pilot3ShortGapLinear_apply, pilot3_differential_eq_inner]
  · intro z hz hc
    rw [hf.overlap_eq_absolute_bulk z hc]
    dsimp only [F, U]
    rw [heV z hz hc]
    dsimp [L]
    ring

end SmoothPilot3
end BoundaryDraft
