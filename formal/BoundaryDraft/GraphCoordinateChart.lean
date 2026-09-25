import BoundaryDraft.GraphChart

/-!
# Coordinate height charts

Choose a nonzero coordinate of the differential and retain the other two
coordinates. Unlike an unspecified complement in the implicit-function
constructor, this choice expresses inverse slices as scalar graphs after an
ambient isometry. It is intended for the canonical scalar-graph area theorem.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A height chart whose two base coordinates are ordinary orthogonal spatial
coordinates, up to an ambient isometry. -/
structure CoordinateHeightChart (h : Spatial → ℝ) extends RegularHeightChart h where
  rotation : JointSpace ≃ₗᵢ[ℝ] JointSpace
  base : ∀ y, surfaceGraphBase (chart y) = surfaceGraphBase (rotation y)

private def coordinateHeightDerivative (L : JointSpace →L[ℝ] ℝ)
    (R : JointSpace ≃ₗᵢ[ℝ] JointSpace) : JointSpace →L[ℝ] JointSpace :=
  jointHeightCoordinates.symm.toContinuousLinearMap.comp
    (L.prod (surfaceGraphBaseL.comp R.toContinuousLinearEquiv.toContinuousLinearMap))

private theorem coordinateHeightDerivative_injective (L : JointSpace →L[ℝ] ℝ)
    (R : JointSpace ≃ₗᵢ[ℝ] JointSpace)
    (hL : L (R.symm (EuclideanSpace.basisFun (Fin 3) ℝ 0)) ≠ 0) :
    Function.Injective (coordinateHeightDerivative L R) := by
  apply (injective_iff_map_eq_zero _).2
  intro v hv
  have hcoord := congrArg jointHeightCoordinates hv
  change (L v, surfaceGraphBase (R v)) = (0, 0) at hcoord
  have hLv : L v = 0 := congrArg Prod.fst hcoord
  have hbase : surfaceGraphBase (R v) = 0 := congrArg Prod.snd hcoord
  have he : R v = (R v 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
    · have hb := congrArg (fun z : SurfacePlane => z j) hbase
      simpa [surfaceGraphBase, surfaceGraphBaseL, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply] using hb
  have hev : v = (R v 0) • R.symm (EuclideanSpace.basisFun (Fin 3) ℝ 0) := by
    simpa using congrArg R.symm he
  have hz : R v 0 = 0 := by
    rw [hev, map_smul, smul_eq_mul] at hLv
    exact (mul_eq_zero.mp hLv).resolve_right hL
  rw [hz, zero_smul] at hev
  exact hev

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- Every noncritical point has a C³ height chart with scalar-graph slices in
orthogonal ambient coordinates. The coordinate choice is proved available
from nonvanishing of the actual differential. -/
theorem exists_coordinateHeightChart (x : JointSpace) (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    ∃ c : CoordinateHeightChart h, x ∈ c.chart.source := by
  let L := fderiv ℝ (fun y : JointSpace => h y) x
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, L (EuclideanSpace.basisFun (Fin 3) ℝ j) ≠ 0 := by
    by_contra! hn
    apply hr
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    exact hn i
  let R : JointSpace ≃ₗᵢ[ℝ] JointSpace :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 j)
  have hR : R.symm (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
      EuclideanSpace.basisFun (Fin 3) ℝ j := by
    dsimp only [R]
    rw [LinearIsometryEquiv.piLpCongrLeft_symm]
    simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single]
    simp
  let B := coordinateHeightDerivative L R
  have hB : Function.Injective B := coordinateHeightDerivative_injective L R (by rwa [hR])
  let A : JointSpace ≃L[ℝ] JointSpace :=
    (LinearEquiv.ofBijective B.toLinearMap
      ⟨hB, (LinearMap.injective_iff_surjective).mp hB⟩).toContinuousLinearEquiv
  let F := fun y : JointSpace => jointHeightCoordinates.symm (h y, surfaceGraphBase (R y))
  have hF : ContDiffAt ℝ 3 F x := jointHeightCoordinates.symm.contDiff.contDiffAt.comp x
    ((hh.smooth_near x hx).prodMk (surfaceGraphBaseL.contDiff.contDiffAt.comp x R.contDiff.contDiffAt))
  have hD : HasFDerivAt F (A : JointSpace →L[ℝ] JointSpace) x :=
    jointHeightCoordinates.symm.hasFDerivAt.comp x
      (((hh.smooth_near x hx).differentiableAt (by norm_num)).hasFDerivAt.prodMk
        (surfaceGraphBaseL.hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt))
  let e := hF.toPartialHomeomorph F hD (by norm_num)
  have hxE : x ∈ e.source := hF.mem_toPartialHomeomorph_source hD (by norm_num)
  have hi : ContDiffAt ℝ 3 e.symm (e x) := by
    apply e.contDiffAt_symm (e.map_source hxE)
    · simpa only [e.left_inv hxE] using hD
    · simpa only [e.left_inv hxE] using hF
  obtain ⟨W, hW, hxW, hsW⟩ := hi.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ (e x)), univ_inter] at hsW
  obtain ⟨U, hU, hxU, hsU, hrU⟩ := hh.exists_regular_neighborhood x hx hr
  let E := ((e.restrOpen U hU).symm.restrOpen W hW).symm
  refine ⟨{
    chart := E
    height := fun _ => rfl
    contDiff := ?_
    contDiff_symm := hsW.mono inter_subset_right
    contDiff_height := hsU.mono (fun _ hy => hy.1.2)
    regular := fun y hy => hrU y hy.1.2
    rotation := R
    base := fun _ => rfl }, ⟨⟨hxE, hxU⟩, hxW⟩⟩
  intro y hy
  exact (jointHeightCoordinates.symm.contDiff.contDiffAt.comp y
    ((hsU.contDiffAt (hU.mem_nhds hy.1.2)).prodMk
      (surfaceGraphBaseL.contDiff.contDiffAt.comp y R.contDiff.contDiffAt))).contDiffWithinAt

end AdmissibleGraphCap

namespace CoordinateHeightChart

variable {h : Spatial → ℝ} (c : CoordinateHeightChart h)

/-- A globally C¹ inverse representative on a smaller target ball. The cutoff
vanishes before reaching any uncontrolled part of the partial inverse. -/
theorem exists_inverse_extension (p : JointSpace) (hp : p ∈ c.chart.target) :
    ∃ (k : JointSpace → JointSpace) (r : ℝ), ContDiff ℝ 1 k ∧ 0 < r ∧
      Metric.ball p r ⊆ c.chart.target ∧ EqOn k c.chart.symm (Metric.ball p r) := by
  obtain ⟨R, hR, hRT⟩ := Metric.mem_nhds_iff.mp (c.chart.open_target.mem_nhds hp)
  let b : ContDiffBump p := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let k : JointSpace → JointSpace := fun y => b y • c.chart.symm y
  have hsupp : tsupport b ⊆ c.chart.target := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [b]; linarith)).trans hRT
  refine ⟨k, R / 4, ?_, by positivity, (Metric.ball_subset_ball (by linarith)).trans hRT, ?_⟩
  · apply contDiff_iff_contDiffAt.2
    intro y
    by_cases hy : y ∈ tsupport b
    · exact b.contDiffAt.smul
        ((c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds (hsupp hy))).of_le (by norm_num))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [not_mem_tsupport_iff_eventuallyEq.1 hy] with z hz
      change b z • c.chart.symm z = 0
      simp [hz]
  · intro y hy
    change b y • c.chart.symm y = c.chart.symm y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_smul]

/-- On the target, the rotated inverse has the prescribed planar coordinates.
Only its first spatial coordinate is an implicit scalar function. -/
theorem base_symm (p : JointSpace) (hp : p ∈ c.chart.target) :
    surfaceGraphBase (c.rotation (c.chart.symm p)) = surfaceGraphBase p := by
  rw [← c.base, c.chart.right_inv hp]

end CoordinateHeightChart
end BoundaryDraft
