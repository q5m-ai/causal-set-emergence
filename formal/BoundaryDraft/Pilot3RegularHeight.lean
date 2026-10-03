import BoundaryDraft.Pilot3Contract
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Slope-independent regular-height geometry in the Euclidean plane

Compactness, the noncritical band and local level charts use no spacelike
height bound. The architecture follows `RegularHeight` in the checked 4D
package, without transferring any of its analytic coefficients or estimates.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

theorem pilot3Gradient_norm (h : Pilot3Space → ℝ) (x : Pilot3Space) :
    ‖pilot3Gradient h x‖ = ‖fderiv ℝ h x‖ :=
  (InnerProductSpace.toDual ℝ Pilot3Space).symm.norm_map _

theorem pilot3_differential_eq_inner (h : Pilot3Space → ℝ) (x v : Pilot3Space) :
    fderiv ℝ h x v = inner (𝕜 := ℝ) (pilot3Gradient h x) v := by
  change _ = (InnerProductSpace.toDual ℝ Pilot3Space)
    ((InnerProductSpace.toDual ℝ Pilot3Space).symm _) v
  rw [LinearIsometryEquiv.apply_symm_apply]

def pilot3TangentSpace (h : Pilot3Space → ℝ) (x : Pilot3Space) : Submodule ℝ Pilot3Space :=
  LinearMap.ker (fderiv ℝ h x)

namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
include hh

theorem smoothAt (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    ContDiffAt ℝ ∞ h x := by
  obtain ⟨U, hU, hxU, hs⟩ := hh.smooth_near x hx
  exact hs.contDiffAt (hU.mem_nhds hxU)

theorem isOpen_positive : IsOpen {x | 0 < h x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact (hh.smoothAt x (subset_closure hx)).continuousAt.preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hx)

theorem isCompact_closedPositive : IsCompact (pilot3ClosedPositive h) :=
  hh.bounded_positive.isCompact_closure

theorem continuousOn_closedPositive : ContinuousOn h (pilot3ClosedPositive h) :=
  fun x hx => (hh.smoothAt x hx).continuousAt.continuousWithinAt

theorem continuousOn_fderiv : ContinuousOn (fderiv ℝ h) (pilot3ClosedPositive h) :=
  fun x hx => ((hh.smoothAt x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt

theorem joint_eq_frontier : pilot3SpatialJoint h = frontier {x | 0 < h x} := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    change h x = 0 at hz
    exact ⟨hx, fun hi => by have := interior_subset hi; change 0 < h x at this; linarith⟩
  · intro hx
    exact ⟨frontier_subset_closure hx, hh.zero_frontier x hx⟩

theorem isCompact_joint : IsCompact (pilot3SpatialJoint h) := by
  rw [hh.joint_eq_frontier]
  exact hh.isCompact_closedPositive.of_isClosed_subset isClosed_frontier frontier_subset_closure

theorem measurableSet_joint : MeasurableSet (pilot3SpatialJoint h) :=
  hh.isCompact_joint.isClosed.measurableSet

theorem nonneg_on_closedPositive (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    0 ≤ h x := by
  by_cases hp : 0 < h x
  · exact hp.le
  · have hf : x ∈ frontier {x | 0 < h x} :=
      ⟨hx, fun hi => hp (show x ∈ {x | 0 < h x} from interior_subset hi)⟩
    exact (hh.zero_frontier x hf).ge

/-- The critical set can be nonempty. Its positive heights, not the points
 themselves, are excluded from the selected boundary band. -/
theorem exists_noncritical_band : ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ pilot3ClosedPositive h, h x ≤ δ → fderiv ℝ h x ≠ 0 := by
  let K := pilot3ClosedPositive h
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hh.isCompact_closedPositive
  let C : Set K := {x | fderiv ℝ h x.val = 0}
  have hC : IsCompact C :=
    (isClosed_eq hh.continuousOn_fderiv.restrict continuous_const).isCompact
  have hpos : ∀ x ∈ C, 0 < h x.val := by
    intro x hx
    refine lt_of_le_of_ne (hh.nonneg_on_closedPositive x.val x.property) ?_
    intro hz
    exact hh.regular_zero x.val x.property hz.symm hx
  obtain ⟨m, hm, hmin⟩ := hC.exists_forall_le'
    hh.continuousOn_closedPositive.restrict.continuousOn hpos
  refine ⟨m / 2, half_pos hm, ?_⟩
  intro x hx hδ hc
  have hle := hmin ⟨x, hx⟩ hc
  dsimp at hle
  linarith

theorem exists_regular_neighborhood (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h)
    (hr : fderiv ℝ h x ≠ 0) :
    ∃ U : Set Pilot3Space, IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ h U ∧
      ∀ y ∈ U, fderiv ℝ h y ≠ 0 := by
  have hc := ((hh.smoothAt x hx).fderiv_right (m := 0) (by simp)).continuousAt
  have hn : {y | fderiv ℝ h y ≠ 0} ∈ 𝓝 x :=
    hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hr)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hn
  obtain ⟨W, hW, hxW, hsmooth⟩ := hh.smooth_near x hx
  exact ⟨W ∩ V, hW.inter hVopen, ⟨hxW, hxV⟩, hsmooth.mono inter_subset_left,
    fun _ hy => hVsub hy.2⟩

theorem gradient_pos (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    0 < ‖pilot3Gradient h x‖ := by
  rw [pilot3Gradient_norm]
  exact norm_pos_iff.mpr (hh.regular_zero x hx.1 hx.2)

theorem inward_norm (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    ‖pilot3Inward h x‖ = 1 := by
  rw [pilot3Inward, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (hh.gradient_pos x hx)]
  exact inv_mul_cancel₀ (hh.gradient_pos x hx).ne'

theorem tangent_finrank (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    Module.finrank ℝ (pilot3TangentSpace h x) = 1 := by
  have hn : (fderiv ℝ h x).toLinearMap ≠ 0 := by
    intro he
    apply hh.regular_zero x hx.1 hx.2
    ext y
    exact LinearMap.congr_fun he y
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have he : Module.finrank ℝ Pilot3Space = 2 := by simp [Pilot3Space, DimensionSpatial]
  rw [he] at hd
  change Module.finrank ℝ (pilot3TangentSpace h x) + 1 = 2 at hd
  omega

/-- A constructed height chart, with the actual tangent inclusion as central
inverse derivative. No atlas, jet or coarea conclusion is assumed. -/
theorem exists_level_chart (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h)
    (hr : fderiv ℝ h x ≠ 0) :
    ∃ e : PartialHomeomorph Pilot3Space (ℝ × pilot3TangentSpace h x),
      x ∈ e.source ∧ e x = (h x, 0) ∧ (∀ y, (e y).1 = h y) ∧
      HasStrictFDerivAt (fun z => e.symm (h x, z)) (pilot3TangentSpace h x).subtypeL 0 := by
  have hd := (hh.smoothAt x hx).hasStrictFDerivAt (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  have hn : (fderiv ℝ h x).toLinearMap ≠ 0 := by
    intro he
    apply hr
    ext y
    exact LinearMap.congr_fun he y
  have hrange := Module.Dual.range_eq_top_of_ne_zero hn
  exact ⟨hd.implicitToPartialHomeomorph _ _ hrange,
    hd.mem_implicitToPartialHomeomorph_source hrange,
    hd.implicitToPartialHomeomorph_self hrange,
    hd.implicitToPartialHomeomorph_fst hrange, hd.to_implicitFunction hrange⟩

/-- Local finiteness precedes any target evaluation or area formula. -/
theorem hausdorff_finiteAt_joint (x : Pilot3Space) (hx : x ∈ pilot3SpatialJoint h) :
    (μH[1] : Measure Pilot3Space).FiniteAtFilter (𝓝[pilot3SpatialJoint h] x) := by
  let L := fderiv ℝ h x
  letI : MeasurableSpace (LinearMap.ker L) := borel _
  letI : BorelSpace (LinearMap.ker L) := ⟨rfl⟩
  have hd : HasStrictFDerivAt h L x := (hh.smoothAt x hx.1).hasStrictFDerivAt (by simp)
  have hn : L.toLinearMap ≠ 0 := by
    intro he
    apply hh.regular_zero x hx.1 hx.2
    ext y
    exact LinearMap.congr_fun he y
  have hrange : LinearMap.range L = ⊤ := Module.Dual.range_eq_top_of_ne_zero hn
  let e := hd.implicitToPartialHomeomorph h L hrange
  let φ := hd.implicitFunction h L hrange (h x)
  have hφ : HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 := hd.to_implicitFunction hrange
  obtain ⟨K, U, hU, hLip⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hdim : Module.finrank ℝ (LinearMap.ker L) = 1 := hh.tangent_finrank x hx
  have hballfinite : (μH[1] : Measure (LinearMap.ker L)) (Metric.ball 0 r) < ⊤ := by
    have hdim' : (Module.finrank ℝ (LinearMap.ker L) : ℝ) = 1 := by exact_mod_cast hdim
    rw [← hdim']
    exact Metric.isBounded_ball.measure_lt_top
  have himage : (μH[1] : Measure Pilot3Space) (φ '' Metric.ball 0 r) < ⊤ := by
    apply ((hLip.mono hball).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)).trans_lt
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top) hballfinite
  refine ⟨φ '' Metric.ball 0 r, ?_, himage⟩
  have hsource : x ∈ e.source := hd.mem_implicitToPartialHomeomorph_source hrange
  have he0 : e x = (h x, 0) := hd.implicitToPartialHomeomorph_self hrange
  have hc : Tendsto (fun y => (e y).2) (𝓝 x) (𝓝 0) := by
    simpa only [ContinuousAt, he0] using (e.continuousAt hsource).snd
  have hnball := hc.eventually (Metric.ball_mem_nhds (0 : LinearMap.ker L) hr)
  have hinv := hd.eq_implicitFunction hrange
  filter_upwards [nhdsWithin_le_nhds hnball, nhdsWithin_le_nhds hinv,
    self_mem_nhdsWithin] with y hy hinvy hyJ
  refine ⟨(e y).2, hy, ?_⟩
  change hd.implicitFunction h L hrange (h x) (e y).2 = y
  rw [hx.2.trans hyJ.2.symm]
  exact hinvy

theorem hausdorff_joint_lt_top : (μH[1] : Measure Pilot3Space) (pilot3SpatialJoint h) < ⊤ :=
  hh.isCompact_joint.measure_lt_top_of_nhdsWithin hh.hausdorff_finiteAt_joint

theorem finite_surfaceMeasure : IsFiniteMeasure (pilot3SurfaceMeasure h) :=
  ⟨by simpa [pilot3SurfaceMeasure] using hh.hausdorff_joint_lt_top⟩

end Pilot3RegularHeight
end BoundaryDraft
