import BoundaryDraft.Pilot3Coarea
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Finite-order derivative control on the fixed collar rectangles

The actual inverse Jacobian and smooth partition are differentiated. For
any fixed finite order there is one bound for all charts, heights and base
parameters. This is geometric control, not an assumed overlap jet or a
uniform bound over all derivative orders simultaneously.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

namespace Pilot3HeightChart
variable {h : Pilot3Space → ℝ} (c : Pilot3HeightChart h)

theorem contDiffAt_det_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    ContDiffAt ℝ ∞ (fun q => (fderiv ℝ c.chart.symm q).toLinearMap.det) p := by
  have hd := (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)).fderiv_right (m := ∞) (by simp)
  have he (i j : Fin 2) : ContDiffAt ℝ ∞
      (fun q => fderiv ℝ c.chart.symm q (EuclideanSpace.basisFun (Fin 2) ℝ i) j) p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j).contDiff.contDiffAt.comp p (hd.clm_apply contDiffAt_const)
  have hform : (fun q => (fderiv ℝ c.chart.symm q).toLinearMap.det) = fun q =>
      (fderiv ℝ c.chart.symm q (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0) *
        (fderiv ℝ c.chart.symm q (EuclideanSpace.basisFun (Fin 2) ℝ 1) 1) -
      (fderiv ℝ c.chart.symm q (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1) *
        (fderiv ℝ c.chart.symm q (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0) := by
    ext q
    rw [pilot3_det_eq_frame, Matrix.det_fin_two]
    rfl
  rw [hform]
  exact ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))

theorem contDiffAt_weightedJacobian (w : Pilot3Space → ℝ) (p : Pilot3Space) (hp : p ∈ c.chart.target)
    (hw : ContDiffAt ℝ ∞ w (c.chart.symm p)) : ContDiffAt ℝ ∞ (c.weightedJacobian w) p :=
  (hw.comp p (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp))).mul
    ((c.contDiffAt_det_symm p hp).abs (c.det_fderiv_symm_ne_zero p hp))

end Pilot3HeightChart
namespace Pilot3CollarAtlas
variable {h : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

theorem contDiffAt_weightedLocalTerm (w : Pilot3Space → ℝ)
    (hw : ∀ x ∈ pilot3ClosedPositive h, ContDiffAt ℝ ∞ w x) (i : Fin A.count)
    (p : ℝ × ℝ) (hp : p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => A.weightedLocalTerm w i q.1 q.2) p := by
  let c := A.charts i
  have hpT : pilot3Coordinates.symm p ∈ c.chart.target := c.ball_subset
    (c.rectangle_subset p.1 ⟨(neg_nonpos.mpr c.width_pos.le).trans hp.1.1,
      hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)
  have hc := c.contDiffAt_weightedJacobian (A.weights i) _ hpT (A.weights i).contMDiff.contDiff.contDiffAt
  have hW := (hw _ (c.symm_mem_closedPositive _ hpT hp.1.1)).comp (pilot3Coordinates.symm p)
    (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hpT))
  exact (hc.mul hW).comp p pilot3Coordinates.symm.contDiff.contDiffAt

theorem exists_uniform_weighted_derivative_bound (w : Pilot3Space → ℝ)
    (hw : ∀ x ∈ pilot3ClosedPositive h, ContDiffAt ℝ ∞ w x) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ i, ∀ p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk,
      ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ => A.weightedLocalTerm w i q.1 q.2) p‖ ≤ B := by
  classical
  have hc (i : Fin A.count) : ContinuousOn
      (iteratedFDeriv ℝ n (fun q : ℝ × ℝ => A.weightedLocalTerm w i q.1 q.2))
      (Icc 0 A.width ×ˢ (A.charts i).closedDisk) := fun p hp =>
    ((A.contDiffAt_weightedLocalTerm w hw i p hp).iteratedFDeriv_right (m := 0)
      (by simp only [zero_add]; exact WithTop.coe_le_coe.mpr le_top)).continuousAt.continuousWithinAt
  have hb : ∀ i, ∃ B : ℝ, ∀ p ∈ Icc 0 A.width ×ˢ (A.charts i).closedDisk,
      ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ => A.weightedLocalTerm w i q.1 q.2) p‖ ≤ B :=
    fun i => (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn (hc i)
  choose B hB using hb
  have hnonneg : 0 ≤ ∑ i, max (B i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨1 + ∑ i, max (B i) 0, by linarith, fun i p hp => ?_⟩
  have hi : max (B i) 0 ≤ ∑ j, max (B j) 0 :=
    Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)
  exact (hB i p hp).trans ((le_max_left _ _).trans (hi.trans (le_add_of_nonneg_left zero_le_one)))

end Pilot3CollarAtlas
end BoundaryDraft
