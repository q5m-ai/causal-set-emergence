import BoundaryDraft.Pilot3Levels
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Constructed smooth coordinate height charts

Both directions are smooth on actual open neighborhoods. In particular the
construction never treats the set of smooth-order `ContDiffAt` points as open.
The remaining spatial coordinate is retained after an orthogonal permutation,
so every inverse level slice is an actual scalar graph in the spatial plane.
-/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

/-- Geometric chart data only. Area, coarea, jets and limits are NOT fields. -/
structure Pilot3HeightChart (h : Pilot3Space → ℝ) where
  chart : PartialHomeomorph Pilot3Space Pilot3Space
  height : ∀ y, chart y 0 = h y
  contDiff : ContDiffOn ℝ ∞ chart chart.source
  contDiff_symm : ContDiffOn ℝ ∞ chart.symm chart.target
  contDiff_height : ContDiffOn ℝ ∞ h chart.source
  regular : ∀ y ∈ chart.source, fderiv ℝ h y ≠ 0
  rotation : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space
  base : ∀ y, chart y 1 = rotation y 1

private def pilot3CoordinateDerivative (L : Pilot3Space →L[ℝ] ℝ)
    (R : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space) : Pilot3Space →L[ℝ] Pilot3Space :=
  pilot3Coordinates.symm.toContinuousLinearMap.comp
    (L.prod ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).comp R.toContinuousLinearEquiv.toContinuousLinearMap))

private theorem pilot3CoordinateDerivative_injective (L : Pilot3Space →L[ℝ] ℝ)
    (R : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space)
    (hL : L (R.symm (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≠ 0) :
    Function.Injective (pilot3CoordinateDerivative L R) := by
  apply (injective_iff_map_eq_zero _).2
  intro v hv
  have hcoord := congrArg pilot3Coordinates hv
  change (L v, R v 1) = (0, 0) at hcoord
  have hLv : L v = 0 := congrArg Prod.fst hcoord
  have hbase : R v 1 = 0 := congrArg Prod.snd hcoord
  have he : R v = (R v 0) • EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, hbase]
  have hev : v = (R v 0) • R.symm (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    simpa using congrArg R.symm he
  have hz : R v 0 = 0 := by
    rw [hev, map_smul, smul_eq_mul] at hLv
    exact (mul_eq_zero.mp hLv).resolve_right hL
  rw [hz, zero_smul] at hev
  exact hev

private def pilot3CoordinateEquiv (L : Pilot3Space →L[ℝ] ℝ)
    (R : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space)
    (hL : L (R.symm (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≠ 0) : Pilot3Space ≃L[ℝ] Pilot3Space :=
  (LinearEquiv.ofBijective (pilot3CoordinateDerivative L R).toLinearMap
    ⟨pilot3CoordinateDerivative_injective L R hL,
      (LinearMap.injective_iff_surjective).mp (pilot3CoordinateDerivative_injective L R hL)⟩).toContinuousLinearEquiv

namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
include hh

/-- A nonzero component remains nonzero on a neighborhood; there the inverse
function theorem applies at EVERY point, yielding a common smooth inverse. -/
theorem exists_heightChart (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h)
    (hr : fderiv ℝ h x ≠ 0) : ∃ c : Pilot3HeightChart h, x ∈ c.chart.source := by
  let L := fderiv ℝ h x
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, L (EuclideanSpace.basisFun (Fin 2) ℝ j) ≠ 0 := by
    by_contra! hn
    apply hr
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext
    intro i
    exact hn i
  let R : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)
  have hR : R.symm (EuclideanSpace.basisFun (Fin 2) ℝ 0) = EuclideanSpace.basisFun (Fin 2) ℝ j := by
    dsimp only [R]
    rw [LinearIsometryEquiv.piLpCongrLeft_symm]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single]
    simp
  let v := R.symm (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hxv : fderiv ℝ h x v ≠ 0 := by simpa only [v, hR] using hj
  have hdc := ((hh.smoothAt x hx).fderiv_right (m := 0) (by simp)).continuousAt
  have hev : Continuous (fun A : Pilot3Space →L[ℝ] ℝ => A v) := continuous_id.clm_apply continuous_const
  have hcv := hev.continuousAt.comp hdc
  obtain ⟨N, hNsub, hN, hxN⟩ := mem_nhds_iff.mp
    (hcv.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hxv))
  obtain ⟨W, hW, hxW, hsW⟩ := hh.smooth_near x hx
  let U := W ∩ N
  have hU : IsOpen U := hW.inter hN
  have hs : ContDiffOn ℝ ∞ h U := hsW.mono inter_subset_left
  have hn : ∀ y ∈ U, fderiv ℝ h y v ≠ 0 := fun y hy => hNsub hy.2
  let F := fun y : Pilot3Space => pilot3Coordinates.symm (h y, R y 1)
  have hF : ∀ y ∈ U, ContDiffAt ℝ ∞ F y := fun y hy =>
    pilot3Coordinates.symm.contDiff.contDiffAt.comp y
      ((hs.contDiffAt (hU.mem_nhds hy)).prodMk
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff.contDiffAt.comp y R.contDiff.contDiffAt))
  have hD : ∀ y (hy : y ∈ U), HasFDerivAt F
      (pilot3CoordinateEquiv (fderiv ℝ h y) R (hn y hy) : Pilot3Space →L[ℝ] Pilot3Space) y := by
    intro y hy
    exact pilot3Coordinates.symm.hasFDerivAt.comp y
      (((hs.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.prodMk
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt.comp y R.toContinuousLinearEquiv.hasFDerivAt))
  have hxU : x ∈ U := ⟨hxW, hxN⟩
  let e := (hF x hxU).toPartialHomeomorph F (hD x hxU) (by simp)
  let E := e.restrOpen U hU
  have hxE : x ∈ E.source := ⟨(hF x hxU).mem_toPartialHomeomorph_source (hD x hxU) (by simp), hxU⟩
  refine ⟨{
    chart := E
    height := fun _ => rfl
    contDiff := fun y hy => (hF y hy.2).contDiffWithinAt
    contDiff_symm := ?_
    contDiff_height := hs.mono inter_subset_right
    regular := ?_
    rotation := R
    base := fun _ => rfl }, hxE⟩
  · intro p hp
    have hy := (E.map_target hp).2
    have hi : ContDiffAt ℝ ∞ E.symm p := E.contDiffAt_symm hp (hD _ hy) (hF _ hy)
    exact hi.contDiffWithinAt
  · intro y hy hz
    have hv := hn y hy.2
    rw [hz, ContinuousLinearMap.zero_apply] at hv
    exact hv rfl

end Pilot3RegularHeight

namespace Pilot3HeightChart
variable {h : Pilot3Space → ℝ} (c : Pilot3HeightChart h)

theorem base_symm (p : Pilot3Space) (hp : p ∈ c.chart.target) : c.rotation (c.chart.symm p) 1 = p 1 := by
  rw [← c.base, c.chart.right_inv hp]

/-- A global smooth representative of the inverse on a smaller ball. -/
theorem exists_inverse_extension (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    ∃ (k : Pilot3Space → Pilot3Space) (r : ℝ), ContDiff ℝ ∞ k ∧ 0 < r ∧
      Metric.ball p r ⊆ c.chart.target ∧ EqOn k c.chart.symm (Metric.ball p r) := by
  obtain ⟨R, hR, hRT⟩ := Metric.mem_nhds_iff.mp (c.chart.open_target.mem_nhds hp)
  let b : ContDiffBump p := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let k : Pilot3Space → Pilot3Space := fun y => b y • c.chart.symm y
  have hsupp : tsupport b ⊆ c.chart.target := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [b]; linarith)).trans hRT
  refine ⟨k, R / 4, ?_, by positivity, (Metric.ball_subset_ball (by linarith)).trans hRT, ?_⟩
  · apply contDiff_iff_contDiffAt.2
    intro y
    by_cases hy : y ∈ tsupport b
    · exact b.contDiffAt.smul (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds (hsupp hy)))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [not_mem_tsupport_iff_eventuallyEq.1 hy] with z hz
      change b z • c.chart.symm z = 0
      simp [hz]
  · intro y hy
    change b y • c.chart.symm y = c.chart.symm y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]

end Pilot3HeightChart
end BoundaryDraft
