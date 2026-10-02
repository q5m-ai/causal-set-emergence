import BoundaryDraft.TwoFaceShortOverlapJet
import BoundaryDraft.MovingCollarJet
import BoundaryDraft.GraphWeightedCoarea
import BoundaryDraft.TwoFaceAngularJet

/-!
# Identification of the actual overlap's displacement two-jet

The C³ extension is constructed in `TwoFaceShortOverlapJet`. Here its actual
fibre derivatives are integrated and identified with the fixed spatial and
canonical joint coefficients. No overlap Taylor premise is introduced.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The first displacement differential of the lost vertical slice. -/
def shortGapLinear (f : Spatial → ℝ) (x : JointSpace) : Displacement →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ JointSpace -
    (fderiv ℝ (fun y : JointSpace => f y) x).comp (ContinuousLinearMap.snd ℝ ℝ JointSpace)

@[simp] theorem shortGapLinear_apply (f : Spatial → ℝ) (x : JointSpace) (z : Displacement) :
    shortGapLinear f x z = z.1 - fderiv ℝ (fun y : JointSpace => f y) x z.2 := rfl

namespace CollarHeightChart

variable {h f : Spatial → ℝ} (c : CollarHeightChart h)

/-- The height differential cancels at zero displacement. The surviving
parameter differential is the actual future graph differential. -/
theorem hasFDerivAt_movingGap_zero (hf : RegularHeightPair h f) (y : SurfacePlane)
    (hy : y ∈ c.closedDisk) :
    HasFDerivAt (fun p : Displacement × ℝ => c.movingGap f ((y, p.1), p.2))
      ((shortGapLinear f (c.chart.symm (jointHeightCoordinates.symm (0, y)))).comp
        (ContinuousLinearMap.fst ℝ Displacement ℝ)) (0, 0) := by
  let x := c.chart.symm (jointHeightCoordinates.symm (0, y))
  let φ : Displacement × ℝ → JointSpace := fun p => c.movingPoint ((y, p.1), p.2)
  have ht : jointHeightCoordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hx : x ∈ graphClosedPositive h := c.symm_mem_closedPositive _ ht le_rfl
  have hφ : ContDiffAt ℝ 3 φ (0, 0) :=
    (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds ht)).comp (0, 0)
      (jointHeightCoordinates.symm.contDiff.contDiffAt.comp (0, 0)
        (contDiffAt_snd.prodMk contDiffAt_const))
  let D := fderiv ℝ (fun u : JointSpace => f u) x
  have hD : HasFDerivAt (fun u : JointSpace => f u) D x :=
    ((hf.smooth_future x hx).differentiableAt (by norm_num)).hasFDerivAt
  have hDb : HasFDerivAt (fun u : JointSpace => f u) D
      (φ (0, 0) + (0 : Displacement).2) := by simpa [φ, x, movingPoint] using hD
  let S : Displacement × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ JointSpace).comp (ContinuousLinearMap.fst ℝ Displacement ℝ)
  let B : Displacement × ℝ →L[ℝ] JointSpace :=
    (ContinuousLinearMap.snd ℝ ℝ JointSpace).comp (ContinuousLinearMap.fst ℝ Displacement ℝ)
  have hφD : HasFDerivAt φ (fderiv ℝ φ (0, 0)) (0, 0) :=
    (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have he : HasFDerivAt (fun p : Displacement × ℝ => c.movingGap f ((y, p.1), p.2))
      (S - D.comp (fderiv ℝ φ (0, 0) + B) + D.comp (fderiv ℝ φ (0, 0))) (0, 0) :=
    (S.hasFDerivAt.sub (hDb.comp (0, 0) (hφD.add B.hasFDerivAt))).add (hD.comp (0, 0) hφD)
  apply he.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change v.1.1 - D (fderiv ℝ φ (0, 0) v + v.1.2) + D (fderiv ℝ φ (0, 0) v) =
    v.1.1 - D v.1.2
  rw [map_add]
  ring

end CollarHeightChart

namespace ControlledCollarAtlas

variable {h f : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- The C² Jacobian in planar-first order. -/
def movingWeight (i : Fin A.count) (p : SurfacePlane × ℝ) : ℝ :=
  (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (p.2, p.1))

theorem contDiffAt_movingWeight (i : Fin A.count) (y : SurfacePlane)
    (hy : y ∈ (A.charts i).closedDisk) : ContDiffAt ℝ 2 (A.movingWeight i) (y, 0) := by
  let c := A.charts i
  have ht : jointHeightCoordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hw : ContDiffAt ℝ 2 (A.weights i) (c.chart.symm (jointHeightCoordinates.symm (0, y))) :=
    (A.weights i).contMDiff.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  exact (c.contDiffAt_weightedJacobian ht hw).comp (y, 0)
    (jointHeightCoordinates.symm.contDiff.contDiffAt.comp (y, 0)
      (contDiffAt_snd.prodMk contDiffAt_fst))

/-- The chosen uniform root gives a concrete fixed-disk extension. -/
def chartCorrection (i : Fin A.count) (f : Spatial → ℝ)
    (η : SurfacePlane × Displacement → ℝ) (z : Displacement) : ℝ :=
  ∫ y in (A.charts i).disk,
    MovingCollar.parametricFibre (A.movingWeight i) ((A.charts i).movingGap f) η (y, z)

set_option maxHeartbeats 800000 in
/-- Integrating the true fibre jets yields the explicit chart Hessian. The
root hypotheses below are furnished by `exists_actual_collarFibre`. -/
theorem chartCorrection_twoJet (hf : RegularHeightPair h f) (i : Fin A.count)
    {δ : ℝ} (hδ : 0 < δ) (η : SurfacePlane × Displacement → ℝ)
    (hη₀ : ∀ y ∈ (A.charts i).closedDisk, η (y, 0) = 0)
    (hη : ∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Displacement) δ,
      ContDiffAt ℝ 3 η (y, z) ∧ η (y, z) = (A.charts i).movingGap f ((y, z), η (y, z))) :
    ContDiffAt ℝ 3 (A.chartCorrection i f η) 0 ∧ A.chartCorrection i f η 0 = 0 ∧
      fderiv ℝ (A.chartCorrection i f η) 0 = 0 ∧
      ∀ v w : Displacement,
        fderiv ℝ (fderiv ℝ (A.chartCorrection i f η)) 0 v w =
          ∫ y in (A.charts i).disk, A.movingWeight i (y, 0) *
            shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) v *
            shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) w := by
  let c := A.charts i
  let W := A.movingWeight i
  let q := c.movingGap f
  let μ : Measure SurfacePlane := volume.restrict c.disk
  have hm : μ.restrict c.closedDisk = μ := by
    dsimp only [μ, CollarHeightChart.disk, CollarHeightChart.closedDisk]
    rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_right.mpr Metric.ball_subset_closedBall]
  have hr (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
      ∀ᶠ z in 𝓝 (0 : Displacement), η (y, z) = q ((y, z), η (y, z)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Displacement) hδ] with z hz
    exact (hη y hy z hz).2
  have hηy (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
      ContDiffAt ℝ 3 (fun z : Displacement => η (y, z)) 0 :=
    (hη y hy 0 (Metric.mem_ball_self hδ)).1.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hqy (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
      ContDiffAt ℝ 3 (fun p : Displacement × ℝ => q ((y, p.1), p.2)) (0, 0) :=
    (c.contDiffAt_movingGap_zero hf y hy).comp (0, 0)
      ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  have hWy (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
      ContDiffAt ℝ 2 (fun t => W (y, t)) 0 :=
    (A.contDiffAt_movingWeight i y hy).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  let F : Displacement × SurfacePlane → ℝ := fun p => MovingCollar.parametricFibre W q η (p.2, p.1)
  have hF (y : SurfacePlane) (hy : y ∈ c.closedDisk) : ContDiffAt ℝ 2 F (0, y) :=
    (MovingCollar.contDiffAt_parametricFibre_two (hη₀ y hy) (A.contDiffAt_movingWeight i y hy)
      ((c.contDiffAt_movingGap_zero hf y hy).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))
      ((hη y hy 0 (Metric.mem_ball_self hδ)).1.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))).comp
        (0, y) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hj := MovingCollar.integral_twoJet (μ := μ) (F := F) (x₀ := (0 : Displacement))
    (K := c.closedDisk) (isCompact_closedBall _ _) hF
  simp only [IntegrableOn, hm] at hj
  have hone (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
      F (0, y) = 0 ∧ fderiv ℝ (fun z => F (z, y)) 0 = 0 :=
    MovingCollar.fibre_vanishing_oneJet (W := fun t => W (y, t))
      (q := fun p : Displacement × ℝ => q ((y, p.1), p.2)) (η := fun z => η (y, z))
      (hWy y hy) (hqy y hy) (hηy y hy) (hη₀ y hy) (hr y hy)
  have htwo (y : SurfacePlane) (hy : y ∈ c.closedDisk) (v w : Displacement) :
      fderiv ℝ (fderiv ℝ (fun z => F (z, y))) 0 v w = W (y, 0) *
        shortGapLinear f (c.chart.symm (jointHeightCoordinates.symm (0, y))) v *
        shortGapLinear f (c.chart.symm (jointHeightCoordinates.symm (0, y))) w := by
    have he := MovingCollar.fderiv_fderiv_fibre (W := fun t => W (y, t))
      (q := fun p : Displacement × ℝ => q ((y, p.1), p.2)) (η := fun z => η (y, z))
      (hWy y hy) (hqy y hy) (hηy y hy) (hη₀ y hy)
      (fun t => by simp [q, CollarHeightChart.movingGap]) (hr y hy) v w
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

/-- Canonical normalization of the summed chart Hessians. -/
theorem sum_chartCorrection_hessian (hf : RegularHeightPair h f) (v w : Displacement) :
    (∑ i, ∫ y in (A.charts i).disk, A.movingWeight i (y, 0) *
      shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) v *
      shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) w) =
        ∫ x, (shortGapLinear f x v * shortGapLinear f x w) / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h := by
  have hD : ContinuousOn (fderiv ℝ (fun x : JointSpace => f x)) (graphClosedPositive h) :=
    fun x hx => ((hf.smooth_future x hx).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
  have hc (u : Displacement) : ContinuousOn (fun x => shortGapLinear f x u) (graphClosedPositive h) :=
    continuousOn_const.sub (hD.clm_apply continuousOn_const)
  have he := A.graphWeightedHeightDensity_eq_sum hf.toRegularHeight
    (fun x => shortGapLinear f x v * shortGapLinear f x w) ((hc v).mul (hc w)) 0
      ⟨le_rfl, A.width_pos.le⟩
  rw [graphWeightedHeightDensity, graphLevelMeasure_zero] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  change (A.movingWeight i (y, 0) *
      shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) v) *
      shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) w =
    A.movingWeight i (y, 0) *
      (shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) v *
        shortGapLinear f ((A.charts i).chart.symm (jointHeightCoordinates.symm (0, y))) w)
  exact mul_assoc _ _ _

include A in
set_option maxHeartbeats 800000 in
/-- The complete actual collar correction has zero one-jet and the explicit
canonical surface Hessian. All root and regularity hypotheses are discharged. -/
theorem exists_collarCorrection_twoJet (hf : AdmissibleTwoFace h f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Displacement → ℝ,
      ContDiffAt ℝ 3 V 0 ∧ V 0 = 0 ∧ fderiv ℝ V 0 = 0 ∧
      (∀ v w : Displacement, fderiv ℝ (fderiv ℝ V) 0 v w =
        ∫ x, (shortGapLinear f x v * shortGapLinear f x w) / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        V z = shortOverlapCollarCorrection h f z := by
  classical
  choose d hd η hη₀ hη heq using A.exists_actual_collarFibre hf
  let V : Fin A.count → Displacement → ℝ := fun i => A.chartCorrection i f (η i)
  have hj (i : Fin A.count) := A.chartCorrection_twoJet hf.toRegularHeightPair i (hd i) (η i) (hη₀ i) (hη i)
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
    rw [A.shortOverlapCollarCorrection_eq_sum hf z (by nlinarith [norm_nonneg z])]
    apply Finset.sum_congr rfl
    intro i _
    rw [A.integral_chart_correction hf i z]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact (heq i y (Metric.ball_subset_closedBall hy) z
      (by simpa only [Metric.mem_ball, dist_zero_right] using hzn.trans (hδd i)) hc).symm

end ControlledCollarAtlas

/-- The fixed-domain single-face term in the actual overlap difference. -/
def shortOverlapBulk (h f : Spatial → ℝ) (z : Displacement) : ℝ :=
  ∫ x in {x : JointSpace | 0 < h x}, f (x + z.2) - f x

private theorem hasFDerivAt_bulkSlice {g : JointSpace → ℝ} {x : JointSpace}
    (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (fun z : Displacement => g (x + z.2) - g x)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.snd ℝ ℝ JointSpace)) 0 := by
  have ht : HasFDerivAt (fun z : Displacement => x + z.2)
      (ContinuousLinearMap.snd ℝ ℝ JointSpace) 0 := by
    simpa only [zero_add] using (hasFDerivAt_const x (0 : Displacement)).add
      (hasFDerivAt_snd (p := (0 : Displacement)) (𝕜 := ℝ))
  have hg' : HasFDerivAt g (fderiv ℝ g x) (x + (0 : Displacement).2) := by
    simpa using hg.hasFDerivAt
  exact (hg'.comp (f := fun z : Displacement => x + z.2) 0 ht).sub_const (g x)

private theorem fderiv_fderiv_bulkSlice {g : JointSpace → ℝ} {x : JointSpace}
    (hg : ContDiffAt ℝ 3 g x) (v w : Displacement) :
    fderiv ℝ (fderiv ℝ (fun z : Displacement => g (x + z.2) - g x)) 0 v w =
      fderiv ℝ (fderiv ℝ g) x v.2 w.2 := by
  let S : Displacement →L[ℝ] JointSpace := ContinuousLinearMap.snd ℝ ℝ JointSpace
  let T : Displacement → JointSpace := fun z => x + z.2
  have hT (z : Displacement) : HasFDerivAt T S z := by
    simpa only [zero_add] using (hasFDerivAt_const x z).add
      (hasFDerivAt_snd (p := z) (𝕜 := ℝ))
  have he : fderiv ℝ (fun z : Displacement => g (x + z.2) - g x) =ᶠ[𝓝 0]
      (fun z => (fderiv ℝ g (T z)).comp S) := by
    have hh : ∀ᶠ z in 𝓝 (0 : Displacement), ContDiffAt ℝ 3 g (T z) := by
      have ht : Tendsto T (𝓝 (0 : Displacement)) (𝓝 x) := by
        simpa [T] using (hT 0).continuousAt.tendsto
      exact ht.eventually (hg.eventually (by simp))
    filter_upwards [hh] with z hz
    exact (((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z (hT z)).sub_const (g x)).fderiv
  have hD : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) (T 0) := by
    simpa [T] using ((hg.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hH := (hD.comp 0 (hT 0)).clm_comp (hasFDerivAt_const S (0 : Displacement))
  have hHeq := hH.fderiv
  dsimp only [Function.comp_apply] at hHeq
  rw [he.fderiv_eq, hHeq]
  simp [ContinuousLinearMap.comp_apply, S]

namespace RegularHeightPair

variable {h f : Spatial → ℝ} (hf : RegularHeightPair h f)
include hf

/-- The fixed-domain source two-jet, with the actual future graph gradient
and Hessian and no noncriticality assumption in the interior. -/
theorem shortOverlapBulk_twoJet : ContDiffAt ℝ 3 (shortOverlapBulk h f) 0 ∧
    shortOverlapBulk h f 0 = 0 ∧
    (∀ v : Displacement, fderiv ℝ (shortOverlapBulk h f) 0 v =
      ∫ x in {x : JointSpace | 0 < h x}, fderiv ℝ (fun y : JointSpace => f y) x v.2) ∧
    ∀ v w : Displacement, fderiv ℝ (fderiv ℝ (shortOverlapBulk h f)) 0 v w =
      ∫ x in {x : JointSpace | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x v.2 w.2 := by
  let μ : Measure JointSpace := volume.restrict {x : JointSpace | 0 < h x}
  let F : Displacement × JointSpace → ℝ := fun p => f (p.2 + p.1.2) - f p.2
  have hm : μ.restrict (graphClosedPositive h) = μ := by
    dsimp only [μ]
    rw [Measure.restrict_restrict hf.toRegularHeight.isCompact_closedPositive.measurableSet,
      inter_eq_right.mpr (show {x : JointSpace | 0 < h x} ⊆ graphClosedPositive h from subset_closure)]
  have hF (x : JointSpace) (hx : x ∈ graphClosedPositive h) : ContDiffAt ℝ 2 F (0, x) := by
    have hfx := hf.smooth_future x hx
    have hfb : ContDiffAt ℝ 3 (fun y : JointSpace => f y) (x + (0 : Displacement).2) := by simpa using hfx
    exact ((hfb.comp (0, x) (contDiffAt_snd.add contDiffAt_fst.snd)).sub
      (hfx.comp (0, x) contDiffAt_snd)).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hj := MovingCollar.integral_twoJet (μ := μ) (F := F) (x₀ := (0 : Displacement))
    hf.toRegularHeight.isCompact_closedPositive hF
  simp only [IntegrableOn, hm] at hj
  refine ⟨hf.contDiffAt_shortOverlapBulk, by simp [shortOverlapBulk], ?_, ?_⟩
  · intro v
    have he := hj.2.2.1.fderiv
    change fderiv ℝ (shortOverlapBulk h f) 0 = ∫ x, fderiv ℝ (fun z => F (z, x)) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.1]
    apply setIntegral_congr_fun
      (hf.toRegularHeight.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
    intro x hx
    have hd := hasFDerivAt_bulkSlice ((hf.smooth_future x (subset_closure hx)).differentiableAt (by norm_num))
    exact congrArg (fun L : Displacement →L[ℝ] ℝ => L v) hd.fderiv
  · intro v w
    have he := hj.2.2.2
    change fderiv ℝ (fderiv ℝ (shortOverlapBulk h f)) 0 =
      ∫ x, fderiv ℝ (fderiv ℝ (fun z => F (z, x))) 0 ∂μ at he
    rw [he, ContinuousLinearMap.integral_apply hj.2.1,
      ContinuousLinearMap.integral_apply (hj.2.1.apply_continuousLinearMap v)]
    apply setIntegral_congr_fun
      (hf.toRegularHeight.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
    intro x hx
    exact fderiv_fderiv_bulkSlice (hf.smooth_future x (subset_closure hx)) v w

end RegularHeightPair

namespace AdmissibleTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- Compatibility with the original source two-jet contract. -/
theorem shortOverlapBulk_twoJet : ContDiffAt ℝ 3 (shortOverlapBulk h f) 0 ∧
    shortOverlapBulk h f 0 = 0 ∧
    (∀ v : Displacement, fderiv ℝ (shortOverlapBulk h f) 0 v =
      ∫ x in {x : JointSpace | 0 < h x}, fderiv ℝ (fun y : JointSpace => f y) x v.2) ∧
    ∀ v w : Displacement, fderiv ℝ (fderiv ℝ (shortOverlapBulk h f)) 0 v w =
      ∫ x in {x : JointSpace | 0 < h x},
        fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x v.2 w.2 :=
  hf.toRegularHeightPair.shortOverlapBulk_twoJet

theorem integrable_shortGapLinear_pair (v w : Displacement) :
    Integrable (fun x => (shortGapLinear f x v * shortGapLinear f x w) / ‖graphGradient h x‖)
      (graphSurfaceMeasure h) := by
  obtain ⟨A⟩ := hf.toAdmissibleGraphCap.exists_controlledCollarAtlas
  have hD : ContinuousOn (fderiv ℝ (fun x : JointSpace => f x)) (graphClosedPositive h) :=
    fun x hx => ((hf.smooth_future x hx).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
  have hc (u : Displacement) : ContinuousOn (fun x => shortGapLinear f x u) (graphClosedPositive h) :=
    continuousOn_const.sub (hD.clm_apply continuousOn_const)
  simpa only [graphLevelMeasure_zero] using
    A.integrable_graphLevel_weight_div hf.toAdmissibleGraphCap
      (fun x => shortGapLinear f x v * shortGapLinear f x w) ((hc v).mul (hc w)) 0
        ⟨le_rfl, A.width_pos.le⟩

set_option maxHeartbeats 800000 in
/-- The actual overlap-difference extension with its explicit first two
jets. This is derived from unchanged admissibility, including the complete
canonical surface term and the true bulk Hessian. -/
theorem exists_overlapDifference_twoJet :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Displacement → ℝ, ContDiffAt ℝ 3 F 0 ∧ F 0 = 0 ∧
      (∀ v : Displacement, fderiv ℝ F 0 v =
        ∫ x in {x : JointSpace | 0 < h x}, inner (𝕜 := ℝ) (graphGradient f x) v.2) ∧
      (∀ v w : Displacement, fderiv ℝ (fderiv ℝ F) 0 v w =
        (∫ x in {x : JointSpace | 0 < h x},
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x v.2 w.2) +
        ∫ x, (inner (𝕜 := ℝ) (graphGradient f x) v.2 * inner (𝕜 := ℝ) (graphGradient f x) w.2 -
          v.1 * inner (𝕜 := ℝ) (graphGradient f x) w.2 -
          w.1 * inner (𝕜 := ℝ) (graphGradient f x) v.2) / ‖graphGradient h x‖
            ∂graphSurfaceMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        F z = translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) -
          translatedOverlap (graphCapRegion h) (displacementSpacetime z) := by
  obtain ⟨A⟩ := hf.toAdmissibleGraphCap.exists_controlledCollarAtlas
  obtain ⟨d, hd, V, hV, hV₀, hV₁, hV₂, heV⟩ := A.exists_collarCorrection_twoJet hf
  let hp := hf.toAdmissibleGraphCap.twoFace_planar
  obtain ⟨e, he, W, hW, hW₀, hW₁, hW₂, heW⟩ := A.exists_collarCorrection_twoJet hp
  obtain ⟨hB, hB₀, hB₁, hB₂⟩ := hf.shortOverlapBulk_twoJet
  let F : Displacement → ℝ := fun z => shortOverlapBulk h f z + V z - W z
  have hF : ContDiffAt ℝ 3 F 0 := (hB.add hV).sub hW
  have hdB := hB.differentiableAt (by norm_num)
  have hdV := hV.differentiableAt (by norm_num)
  have hdW := hW.differentiableAt (by norm_num)
  refine ⟨min d e, lt_min hd he, F, hF, by simp [F, hB₀, hV₀, hW₀], ?_, ?_, ?_⟩
  · intro v
    have hD : fderiv ℝ F 0 = fderiv ℝ (shortOverlapBulk h f) 0 := by
      dsimp only [F]
      rw [fderiv_sub (hdB.add hdV) hdW, fderiv_add hdB hdV, hV₁, hW₁, add_zero, sub_zero]
    rw [hD, hB₁]
    apply integral_congr_ae
    filter_upwards with x
    exact graph_differential_eq_inner f x v.2
  · intro v w
    have heD : fderiv ℝ F =ᶠ[𝓝 (0 : Displacement)]
        (fun z => fderiv ℝ (shortOverlapBulk h f) z + fderiv ℝ V z - fderiv ℝ W z) := by
      filter_upwards [hB.eventually (by simp), hV.eventually (by simp), hW.eventually (by simp)] with z hzB hzV hzW
      dsimp only [F]
      rw [fderiv_sub ((hzB.differentiableAt (by norm_num)).add (hzV.differentiableAt (by norm_num)))
        (hzW.differentiableAt (by norm_num)),
        fderiv_add (hzB.differentiableAt (by norm_num)) (hzV.differentiableAt (by norm_num))]
    have hDB := (hB.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hDV := (hV.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hDW := (hW.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    rw [heD.fderiv_eq, fderiv_sub (hDB.add hDV) hDW, fderiv_add hDB hDV]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    rw [hB₂, hV₂, hW₂]
    rw [add_sub_assoc]
    congr 1
    rw [← integral_sub (hf.integrable_shortGapLinear_pair v w) (hp.integrable_shortGapLinear_pair v w)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [shortGapLinear_apply, fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, sub_zero,
      graph_differential_eq_inner]
    ring
  · intro z hz hc
    rw [hf.translatedOverlap_sub_planar z hc]
    dsimp only [F, shortOverlapBulk]
    rw [heV z (Metric.ball_subset_ball (min_le_left d e) hz) hc,
      heW z (Metric.ball_subset_ball (min_le_right d e) hz) hc]

/-- The polynomial already used by the angular analysis is exactly the
Taylor polynomial of the derived actual overlap extension. This identifies
all coefficients without replacing the original polynomial definition. -/
theorem exists_overlapDifference_taylorPolynomial :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Displacement → ℝ, ContDiffAt ℝ 3 F 0 ∧ F 0 = 0 ∧
      (∀ z : Displacement, twoFaceShortPolynomial h f z =
        fderiv ℝ F 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ F) 0 z z) ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        F z = translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) -
          translatedOverlap (graphCapRegion h) (displacementSpacetime z) := by
  obtain ⟨δ, hδ, F, hF, hF₀, hF₁, hF₂, heF⟩ := hf.exists_overlapDifference_twoJet
  refine ⟨δ, hδ, F, hF, hF₀, ?_, heF⟩
  intro z
  rw [twoFaceShortPolynomial, hF₁, hF₂]
  have he : (∫ x, (inner (𝕜 := ℝ) (graphGradient f x) z.2 ^ 2 -
      2 * z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2) / ‖graphGradient h x‖ ∂graphSurfaceMeasure h) =
      ∫ x, (inner (𝕜 := ℝ) (graphGradient f x) z.2 * inner (𝕜 := ℝ) (graphGradient f x) z.2 -
        z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2 -
        z.1 * inner (𝕜 := ℝ) (graphGradient f x) z.2) / ‖graphGradient h x‖ ∂graphSurfaceMeasure h := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he]
  ring

end AdmissibleTwoFace
end BoundaryDraft
