import BoundaryDraft.GraphSliceTransport
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A finite controlled collar atlas

Joint-centered charts have fixed planar disks and a common interval of height
parameters. Compactness extends a finite cover of the joint to a whole closed
collar. A smooth subordinate partition of unity accounts for all overlaps.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal Manifold
noncomputable section
namespace BoundaryDraft

/-- The closed positive collar. Admissibility already implies nonnegative
height throughout `graphClosedPositive`. -/
def graphClosedCollar (h : Spatial → ℝ) (δ : ℝ) : Set JointSpace :=
  graphClosedPositive h ∩ {x | h x ≤ δ}

/-- A joint-centered chart. The radius determines both a fixed planar disk
and a height interval strictly inside the controlled target ball. -/
structure CollarHeightChart (h : Spatial → ℝ) extends SliceHeightChart h where
  center_zero : center 0 = 0

private theorem heightCoordinates_norm_le (p : ℝ × SurfacePlane) :
    ‖jointHeightCoordinates.symm p‖ ≤ |p.1| + ‖p.2‖ := by
  have hsq : ‖jointHeightCoordinates.symm p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    change (∑ i : Fin 3, (Fin.cons p.1 (p.2 : Fin 2 → ℝ) i) ^ 2) =
      p.1 ^ 2 + ∑ i : Fin 2, (p.2 i) ^ 2
    rw [Fin.sum_univ_succ]
    rfl
  have ha := abs_nonneg p.1
  have hb := norm_nonneg p.2
  have hc := norm_nonneg (jointHeightCoordinates.symm p)
  nlinarith [sq_abs p.1, mul_nonneg ha hb]

namespace CollarHeightChart

variable {h : Spatial → ℝ} (c : CollarHeightChart h)

def width : ℝ := c.radius / 4

def disk : Set SurfacePlane := Metric.ball (surfaceGraphBase c.center) c.width

def closedDisk : Set SurfacePlane := Metric.closedBall (surfaceGraphBase c.center) c.width

theorem width_pos : 0 < c.width := div_pos c.radius_pos (by norm_num)

/-- A fixed compact parameter rectangle lies strictly inside the target.
This leaves room for both surface transport and uniform local domination. -/
theorem rectangle_subset (t : ℝ) (ht : t ∈ Icc (-c.width) c.width)
    (u : SurfacePlane) (hu : u ∈ c.closedDisk) :
    surfaceGraph (fun _ => t) u ∈ Metric.ball c.center c.radius := by
  have he : surfaceGraph (fun _ => t) u - c.center =
      jointHeightCoordinates.symm (t, u - surfaceGraphBase c.center) := by
    apply jointHeightCoordinates.injective
    rw [map_sub, jointHeightCoordinates.apply_symm_apply]
    change (t - c.center 0, u - surfaceGraphBase c.center) = _
    rw [c.center_zero, sub_zero]
  have hdist : dist (surfaceGraph (fun _ => t) u) c.center ≤
      |t| + dist u (surfaceGraphBase c.center) := by
    rw [dist_eq_norm, he, dist_eq_norm]
    exact heightCoordinates_norm_le _
  have habs : |t| ≤ c.width := abs_le.mpr ht
  have hu' : dist u (surfaceGraphBase c.center) ≤ c.width := hu
  have hr := c.radius_pos
  change dist (surfaceGraph (fun _ => t) u) c.center < c.radius
  dsimp [width] at habs hu'
  linarith

/-- The chart patch used for the cover and partition supports. -/
def patch : Set JointSpace := c.chart.source ∩ c.chart ⁻¹'
  (jointHeightCoordinates ⁻¹' (Ioo (-c.width) c.width ×ˢ c.disk))

theorem isOpen_patch : IsOpen c.patch :=
  c.chart.isOpen_inter_preimage
    ((isOpen_Ioo.prod Metric.isOpen_ball).preimage jointHeightCoordinates.continuous)

theorem center_mem_patch {x : JointSpace} (hx : x ∈ c.chart.source)
    (hcenter : c.center = c.chart x) : x ∈ c.patch := by
  refine ⟨hx, ?_⟩
  change c.chart x 0 ∈ Ioo (-c.width) c.width ∧
    surfaceGraphBase (c.chart x) ∈ c.disk
  rw [← hcenter, c.center_zero]
  exact ⟨⟨neg_neg_of_pos c.width_pos, c.width_pos⟩,
    Metric.mem_ball_self c.width_pos⟩

/-- All nearby slices use this same open planar disk. -/
theorem disk_subset_sliceDomain (t : ℝ) (ht : t ∈ Icc (-c.width) c.width) :
    c.disk ⊆ c.sliceDomain t :=
  fun _ hu => c.rectangle_subset t ht _ (Metric.ball_subset_closedBall hu)

/-- Every point of a level in the partition patch has a unique slice
parameter in the fixed disk. No seam or discarded boundary is involved. -/
theorem mem_slice_image_of_mem_patch (x : JointSpace) (hx : x ∈ c.patch)
    (t : ℝ) (hxt : h x = t) : x ∈ c.slice t '' c.disk := by
  have hrect : c.chart x 0 ∈ Ioo (-c.width) c.width ∧
      surfaceGraphBase (c.chart x) ∈ c.disk := hx.2
  have he : surfaceGraph (fun _ => t) (surfaceGraphBase (c.chart x)) = c.chart x := by
    rw [← hxt, ← c.height x]
    exact surfaceGraph_height_base _
  have ht : t ∈ Icc (-c.width) c.width := by
    rw [c.height x, hxt] at hrect
    exact ⟨hrect.1.1.le, hrect.1.2.le⟩
  refine ⟨surfaceGraphBase (c.chart x), hrect.2, ?_⟩
  rw [c.slice_eq_symm t _ (c.disk_subset_sliceDomain t ht hrect.2), he, c.chart.left_inv hx.1]

/-- The fixed disk times the closed interval of heights, in Euclidean
three-dimensional parameter coordinates. -/
def parameterRegion (δ : ℝ) : Set JointSpace :=
  jointHeightCoordinates ⁻¹' (Icc 0 δ ×ˢ c.disk)

theorem measurableSet_parameterRegion (δ : ℝ) : MeasurableSet (c.parameterRegion δ) :=
  (measurableSet_Icc.prod measurableSet_ball).preimage jointHeightCoordinates.continuous.measurable

theorem parameterRegion_subset_target (δ : ℝ) (hδ : δ ≤ c.width) :
    c.parameterRegion δ ⊆ c.chart.target := by
  intro p hp
  have hp' : p 0 ∈ Icc 0 δ ∧ surfaceGraphBase p ∈ c.disk := hp
  have ht : p 0 ∈ Icc (-c.width) c.width :=
    ⟨(neg_nonpos.mpr c.width_pos.le).trans hp'.1.1, hp'.1.2.trans hδ⟩
  have hball := c.rectangle_subset _ ht _ (Metric.ball_subset_closedBall hp'.2)
  rw [surfaceGraph_height_base] at hball
  exact c.ball_subset hball

theorem parameterImage_subset_closedCollar (δ : ℝ) (hδ : δ ≤ c.width) :
    c.chart.symm '' c.parameterRegion δ ⊆ graphClosedCollar h δ := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' : p 0 ∈ Icc 0 δ ∧ surfaceGraphBase p ∈ c.disk := hp
  have hpT := c.parameterRegion_subset_target δ hδ hp
  exact ⟨c.symm_mem_closedPositive p hpT hp'.1.1,
    (c.height_symm p hpT).le.trans hp'.1.2⟩

theorem mem_parameterImage_of_mem_patch (δ : ℝ) (x : JointSpace)
    (hx : x ∈ c.patch) (hxt : h x ∈ Icc 0 δ) :
    x ∈ c.chart.symm '' c.parameterRegion δ := by
  refine ⟨c.chart x, ?_, c.chart.left_inv hx.1⟩
  change c.chart x 0 ∈ Icc 0 δ ∧ surfaceGraphBase (c.chart x) ∈ c.disk
  exact ⟨by rwa [c.height], hx.2.2⟩

end CollarHeightChart

/-- A finite smooth atlas covering an entire closed collar. Transformation
laws are inherited proved theorems of each chart, not fields of this record. -/
structure ControlledCollarAtlas (h : Spatial → ℝ) where
  width : ℝ
  width_pos : 0 < width
  count : ℕ
  charts : Fin count → CollarHeightChart h
  width_lt : ∀ i, width < (charts i).width
  noncritical : ∀ x ∈ graphClosedCollar h width,
    fderiv ℝ (fun y : JointSpace => h y) x ≠ 0
  covers : graphClosedCollar h width ⊆ ⋃ i, (charts i).patch
  weights : SmoothPartitionOfUnity (Fin count) 𝓘(ℝ, JointSpace) JointSpace (graphClosedCollar h width)
  subordinate : weights.IsSubordinate (fun i => (charts i).patch)

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem isCompact_closedCollar (δ : ℝ) : IsCompact (graphClosedCollar h δ) := by
  apply hh.toGraphCapData.isCompact_closedPositive.of_isClosed_subset _ inter_subset_left
  exact hh.continuousOn_closedPositive.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic

/-- Construct a finite controlled atlas, choosing its width strictly within
the checked noncritical band. Positive-height critical points beyond it are
unrestricted; no flow or transformation law is assumed. -/
theorem exists_controlledCollarAtlas : Nonempty (ControlledCollarAtlas h) := by
  classical
  have hcharts : ∀ x : graphJoint h, ∃ c : CollarHeightChart h, x.val ∈ c.patch := by
    intro x
    obtain ⟨c, hxC, hcenter⟩ := hh.exists_sliceHeightChart x.val x.property.1
      (hh.regular_zero x.val x.property.1 x.property.2)
    have hc0 : c.center 0 = 0 := by rw [hcenter, c.height, x.property.2]
    let C : CollarHeightChart h := { c with center_zero := hc0 }
    exact ⟨C, C.center_mem_patch hxC hcenter⟩
  choose C hC using hcharts
  obtain ⟨T, hT⟩ := hh.isCompact_joint.elim_finite_subcover (fun x => (C x).patch)
    (fun x => (C x).isOpen_patch) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hC ⟨x, hx⟩⟩)
  let n := Fintype.card T
  let charts : Fin n → CollarHeightChart h := fun i => C ((Fintype.equivFin T).symm i).val
  have hcover : graphJoint h ⊆ ⋃ i, (charts i).patch := by
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
  have hcover' : graphClosedCollar h δ ⊆ ⋃ i, (charts i).patch :=
    fun x hx => hband x hx.1 (hx.2.trans hδ₀'.le)
  obtain ⟨w, hw⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, JointSpace)
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

end AdmissibleGraphCap
end BoundaryDraft
