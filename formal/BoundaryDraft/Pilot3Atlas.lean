import BoundaryDraft.Pilot3JointCharts
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A constructed finite smooth collar atlas

A finite joint cover extends to a whole noncritical closed positive collar.
Every chart has a fixed compact parameter rectangle and a smooth subordinate
partition; area/coarea laws are proved from these data, not fields of them.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Manifold
noncomputable section
namespace BoundaryDraft

def pilot3ClosedCollar (h : Pilot3Space → ℝ) (δ : ℝ) : Set Pilot3Space :=
  pilot3ClosedPositive h ∩ {x | h x ≤ δ}

structure Pilot3CollarChart (h : Pilot3Space → ℝ) extends Pilot3SliceChart h where
  center_zero : center 0 = 0

private theorem pilot3Coordinates_norm_le (a b : ℝ) : ‖pilot3Coordinates.symm (a, b)‖ ≤ |a| + |b| := by
  have hs := pilot3Coordinates_norm_sq a b
  have hn := norm_nonneg (pilot3Coordinates.symm (a, b))
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]

namespace Pilot3CollarChart
variable {h : Pilot3Space → ℝ} (c : Pilot3CollarChart h)

def width : ℝ := c.radius / 4

def disk : Set ℝ := Metric.ball (c.center 1) c.width

def closedDisk : Set ℝ := Metric.closedBall (c.center 1) c.width

theorem width_pos : 0 < c.width := div_pos c.radius_pos (by norm_num)

/-- The same compact rectangle works at every nearby height. -/
theorem rectangle_subset (t : ℝ) (ht : t ∈ Icc (-c.width) c.width) (u : ℝ) (hu : u ∈ c.closedDisk) :
    pilot3Curve (fun _ => t) u ∈ Metric.ball c.center c.radius := by
  have he : pilot3Curve (fun _ => t) u - c.center = pilot3Coordinates.symm (t, u - c.center 1) := by
    apply pilot3Coordinates.injective
    rw [map_sub, pilot3Coordinates.apply_symm_apply]
    change (t - c.center 0, u - c.center 1) = _
    rw [c.center_zero, sub_zero]
  have hd : dist (pilot3Curve (fun _ => t) u) c.center ≤ |t| + dist u (c.center 1) := by
    rw [dist_eq_norm, he, Real.dist_eq]
    exact pilot3Coordinates_norm_le _ _
  have ha : |t| ≤ c.width := abs_le.mpr ht
  have hu' : dist u (c.center 1) ≤ c.width := hu
  have hr := c.radius_pos
  change dist (pilot3Curve (fun _ => t) u) c.center < c.radius
  dsimp [width] at ha hu'
  linarith

def patch : Set Pilot3Space := c.chart.source ∩ c.chart ⁻¹'
  (pilot3Coordinates ⁻¹' (Ioo (-c.width) c.width ×ˢ c.disk))

theorem isOpen_patch : IsOpen c.patch :=
  c.chart.isOpen_inter_preimage ((isOpen_Ioo.prod Metric.isOpen_ball).preimage pilot3Coordinates.continuous)

theorem center_mem_patch {x : Pilot3Space} (hx : x ∈ c.chart.source) (hcenter : c.center = c.chart x) :
    x ∈ c.patch := by
  refine ⟨hx, ?_⟩
  change c.chart x 0 ∈ Ioo (-c.width) c.width ∧ c.chart x 1 ∈ c.disk
  rw [← hcenter, c.center_zero]
  exact ⟨⟨neg_neg_of_pos c.width_pos, c.width_pos⟩, Metric.mem_ball_self c.width_pos⟩

theorem disk_subset_sliceDomain (t : ℝ) (ht : t ∈ Icc (-c.width) c.width) : c.disk ⊆ c.sliceDomain t :=
  fun _ hu => c.rectangle_subset t ht _ (Metric.ball_subset_closedBall hu)

theorem mem_slice_image_of_mem_patch (x : Pilot3Space) (hx : x ∈ c.patch) (t : ℝ) (hxt : h x = t) :
    x ∈ c.slice t '' c.disk := by
  have hrect : c.chart x 0 ∈ Ioo (-c.width) c.width ∧ c.chart x 1 ∈ c.disk := hx.2
  have he : pilot3Curve (fun _ => t) (c.chart x 1) = c.chart x := by
    rw [← hxt, ← c.height x]
    exact pilot3Curve_height_base _
  have ht : t ∈ Icc (-c.width) c.width := by
    rw [c.height x, hxt] at hrect
    exact ⟨hrect.1.1.le, hrect.1.2.le⟩
  refine ⟨c.chart x 1, hrect.2, ?_⟩
  rw [c.slice_eq_symm t _ (c.disk_subset_sliceDomain t ht hrect.2), he, c.chart.left_inv hx.1]

def parameterRegion (δ : ℝ) : Set Pilot3Space := pilot3Coordinates ⁻¹' (Icc 0 δ ×ˢ c.disk)

theorem measurableSet_parameterRegion (δ : ℝ) : MeasurableSet (c.parameterRegion δ) :=
  (measurableSet_Icc.prod measurableSet_ball).preimage pilot3Coordinates.continuous.measurable

theorem parameterRegion_subset_target (δ : ℝ) (hδ : δ ≤ c.width) : c.parameterRegion δ ⊆ c.chart.target := by
  intro p hp
  have hp' : p 0 ∈ Icc 0 δ ∧ p 1 ∈ c.disk := hp
  have ht : p 0 ∈ Icc (-c.width) c.width :=
    ⟨(neg_nonpos.mpr c.width_pos.le).trans hp'.1.1, hp'.1.2.trans hδ⟩
  have hb := c.rectangle_subset _ ht _ (Metric.ball_subset_closedBall hp'.2)
  rw [pilot3Curve_height_base] at hb
  exact c.ball_subset hb

theorem parameterImage_subset_closedCollar (δ : ℝ) (hδ : δ ≤ c.width) :
    c.chart.symm '' c.parameterRegion δ ⊆ pilot3ClosedCollar h δ := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' : p 0 ∈ Icc 0 δ ∧ p 1 ∈ c.disk := hp
  have hpT := c.parameterRegion_subset_target δ hδ hp
  exact ⟨c.symm_mem_closedPositive p hpT hp'.1.1, (c.height_symm p hpT).le.trans hp'.1.2⟩

theorem mem_parameterImage_of_mem_patch (δ : ℝ) (x : Pilot3Space) (hx : x ∈ c.patch) (hxt : h x ∈ Icc 0 δ) :
    x ∈ c.chart.symm '' c.parameterRegion δ := by
  refine ⟨c.chart x, ?_, c.chart.left_inv hx.1⟩
  change c.chart x 0 ∈ Icc 0 δ ∧ c.chart x 1 ∈ c.disk
  exact ⟨by rwa [c.height], hx.2.2⟩

end Pilot3CollarChart

/-- Constructed finite geometric cover and smooth partition, with no analytic
transformation or limiting conclusion among its fields. -/
structure Pilot3CollarAtlas (h : Pilot3Space → ℝ) where
  width : ℝ
  width_pos : 0 < width
  count : ℕ
  charts : Fin count → Pilot3CollarChart h
  width_lt : ∀ i, width < (charts i).width
  noncritical : ∀ x ∈ pilot3ClosedCollar h width, fderiv ℝ h x ≠ 0
  covers : pilot3ClosedCollar h width ⊆ ⋃ i, (charts i).patch
  weights : SmoothPartitionOfUnity (Fin count) 𝓘(ℝ, Pilot3Space) Pilot3Space (pilot3ClosedCollar h width)
  subordinate : weights.IsSubordinate (fun i => (charts i).patch)

namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
include hh

theorem isCompact_closedCollar (δ : ℝ) : IsCompact (pilot3ClosedCollar h δ) := by
  apply hh.isCompact_closedPositive.of_isClosed_subset _ inter_subset_left
  exact hh.continuousOn_closedPositive.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic

/-- Finite collar construction for EVERY regular height, independent of slope
bounds, component count or the existence of positive-height critical points. -/
theorem exists_collarAtlas : Nonempty (Pilot3CollarAtlas h) := by
  classical
  have hcharts : ∀ x : pilot3SpatialJoint h, ∃ c : Pilot3CollarChart h, x.val ∈ c.patch := by
    intro x
    obtain ⟨c, hxC, hcenter⟩ := hh.exists_sliceChart x.val x.property.1 (hh.regular_zero x.val x.property.1 x.property.2)
    have hc0 : c.center 0 = 0 := by rw [hcenter, c.height, x.property.2]
    let C : Pilot3CollarChart h := { c with center_zero := hc0 }
    exact ⟨C, C.center_mem_patch hxC hcenter⟩
  choose C hC using hcharts
  obtain ⟨T, hT⟩ := hh.isCompact_joint.elim_finite_subcover (fun x => (C x).patch)
    (fun x => (C x).isOpen_patch) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hC ⟨x, hx⟩⟩)
  let n := Fintype.card T
  let charts : Fin n → Pilot3CollarChart h := fun i => C ((Fintype.equivFin T).symm i).val
  have hcover : pilot3SpatialJoint h ⊆ ⋃ i, (charts i).patch := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hT hx)
    refine mem_iUnion.mpr ⟨(Fintype.equivFin T) ⟨j, hj⟩, ?_⟩
    simpa only [charts, Equiv.symm_apply_apply] using hxj
  obtain ⟨δ₀, hδ₀, hband⟩ := hh.exists_band_subset_joint_neighborhood _
    (isOpen_iUnion fun i => (charts i).isOpen_patch) hcover
  obtain ⟨δ₁, hδ₁, hreg⟩ := hh.exists_noncritical_band
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, (∀ i, δ < (charts i).width) ∧ δ < δ₀ ∧ δ < δ₁ := by
    apply nhdsWithin_le_nhds
    exact (eventually_all.mpr fun i => gt_mem_nhds (charts i).width_pos).and
      ((gt_mem_nhds hδ₀).and (gt_mem_nhds hδ₁))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hwidth, hδ₀', hδ₁'⟩ := (hpos.and hsmall).exists
  have hcover' : pilot3ClosedCollar h δ ⊆ ⋃ i, (charts i).patch :=
    fun x hx => hband x hx.1 (hx.2.trans hδ₀'.le)
  obtain ⟨w, hw⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Pilot3Space)
    (hh.isCompact_closedCollar δ).isClosed (fun i => (charts i).patch)
    (fun i => (charts i).isOpen_patch) hcover'
  exact ⟨{
    width := δ
    width_pos := hδ
    count := n
    charts := charts
    width_lt := hwidth
    noncritical := fun x hx => hreg x hx.1 (hx.2.trans hδ₁'.le)
    covers := hcover'
    weights := w
    subordinate := hw }⟩

end Pilot3RegularHeight
end BoundaryDraft
