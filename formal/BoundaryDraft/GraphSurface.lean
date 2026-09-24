import BoundaryDraft.GraphAngle
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Canonical Hausdorff surface target and finite regular joints

The surface measure is `(π/4) • μH[2]` in Euclidean space, restricted to the
joint. The coefficient states the normalized Euclidean area convention for
mathlib's diameter-based Hausdorff measure. Its identification with parametric
area (in particular the existing ellipsoid measure) is a separate, still open
obligation. No action or collar density is defined using its desired limit.

Finiteness is proved independently: the implicit function theorem gives local
Lipschitz parametrizations over the actual two-dimensional tangent kernel;
Hausdorff measure decreases up to the Lipschitz constant, and compactness
reduces local finiteness to finiteness of the entire joint.
-/

open MeasureTheory Set Filter
open scoped Topology MeasureTheory ENNReal
noncomputable section
namespace BoundaryDraft

/-- The kernel of the actual Euclidean differential. -/
def graphTangentSpace (h : Spatial → ℝ) (x : JointSpace) : Submodule ℝ JointSpace :=
  LinearMap.ker (fderiv ℝ (fun y : JointSpace => h y) x)

/-- Canonical diameter-Hausdorff measure with the explicitly chosen Euclidean
area coefficient. Agreement with parametric area is not a definition. -/
def graphSurfaceMeasure (h : Spatial → ℝ) : Measure JointSpace :=
  ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure JointSpace).restrict (graphJoint h)

/-- The proposed boundary value, independent of the continuum action. -/
def graphBoundaryIntegral (h : Spatial → ℝ) : ℝ :=
  ∫ x, 1 / ‖graphGradient h x‖ ∂graphSurfaceMeasure h

/-- Open general limit target. Defining this proposition is not its proof. -/
def GraphCapLimitGoal (h : Spatial → ℝ) : Prop :=
  Tendsto (fun ρ => continuumMean ρ (graphCapRegion h)) atTop (𝓝 (graphBoundaryIntegral h))

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem graphTangentSpace_finrank (x : JointSpace) (hx : x ∈ graphJoint h) :
    Module.finrank ℝ (graphTangentSpace h x) = 2 := by
  have hn : (fderiv ℝ (fun y : JointSpace => h y) x).toLinearMap ≠ 0 := by
    intro he
    apply hh.regular_zero x hx.1 hx.2
    ext y
    exact LinearMap.congr_fun he y
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  have he : Module.finrank ℝ JointSpace = 3 := by simp [JointSpace]
  rw [he] at hd
  change Module.finrank ℝ (graphTangentSpace h x) + 1 = 3 at hd
  omega

/-- A genuine height-flattening local chart at each noncritical point of the
closed positive region. Its inverse on the central level has derivative equal
to tangent inclusion. This is constructed, not an admissibility premise. -/
theorem exists_level_chart (x : JointSpace) (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    ∃ e : PartialHomeomorph JointSpace (ℝ × graphTangentSpace h x),
      x ∈ e.source ∧ e x = (h x, 0) ∧ (∀ y, (e y).1 = h y) ∧
      HasStrictFDerivAt (fun z => e.symm (h x, z)) (graphTangentSpace h x).subtypeL 0 := by
  have hd := (hh.smooth_near x hx).hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hn : (fderiv ℝ (fun y : JointSpace => h y) x).toLinearMap ≠ 0 := by
    intro he
    apply hr
    ext y
    exact LinearMap.congr_fun he y
  have hrange := Module.Dual.range_eq_top_of_ne_zero hn
  exact ⟨hd.implicitToPartialHomeomorph _ _ hrange,
    hd.mem_implicitToPartialHomeomorph_source hrange,
    hd.implicitToPartialHomeomorph_self hrange,
    hd.implicitToPartialHomeomorph_fst hrange, hd.to_implicitFunction hrange⟩

/-- The implicit level parametrization has finite two-dimensional Hausdorff
measure near each joint point. This is not an area/Jacobian formula. -/
theorem hausdorff_finiteAt_joint (x : JointSpace) (hx : x ∈ graphJoint h) :
    (μH[2] : Measure JointSpace).FiniteAtFilter (𝓝[graphJoint h] x) := by
  let f := fun y : JointSpace => h y
  let L := fderiv ℝ f x
  letI : MeasurableSpace (LinearMap.ker L) := borel _
  letI : BorelSpace (LinearMap.ker L) := ⟨rfl⟩
  have hd : HasStrictFDerivAt f L x := (hh.smooth_near x hx.1).hasStrictFDerivAt (by norm_num)
  have hn : L.toLinearMap ≠ 0 := by
    intro he
    apply hh.regular_zero x hx.1 hx.2
    ext y
    exact LinearMap.congr_fun he y
  have hrange : LinearMap.range L = ⊤ := Module.Dual.range_eq_top_of_ne_zero hn
  let e := hd.implicitToPartialHomeomorph f L hrange
  let φ := hd.implicitFunction f L hrange (f x)
  have hφ : HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 := hd.to_implicitFunction hrange
  obtain ⟨K, U, hU, hLip⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hdim : Module.finrank ℝ (LinearMap.ker L) = 2 := hh.graphTangentSpace_finrank x hx
  have hballfinite : (μH[2] : Measure (LinearMap.ker L)) (Metric.ball 0 r) < ∞ := by
    have hdim' : (Module.finrank ℝ (LinearMap.ker L) : ℝ) = 2 := by exact_mod_cast hdim
    rw [← hdim']
    exact Metric.isBounded_ball.measure_lt_top
  have himage : (μH[2] : Measure JointSpace) (φ '' Metric.ball 0 r) < ∞ := by
    apply ((hLip.mono hball).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top) hballfinite
  refine ⟨φ '' Metric.ball 0 r, ?_, himage⟩
  have hsource : x ∈ e.source := hd.mem_implicitToPartialHomeomorph_source hrange
  have he0 : e x = (f x, 0) := hd.implicitToPartialHomeomorph_self hrange
  have hc : Tendsto (fun y => (e y).2) (𝓝 x) (𝓝 0) := by
    simpa only [ContinuousAt, he0] using (e.continuousAt hsource).snd
  have hnball := hc.eventually (Metric.ball_mem_nhds (0 : LinearMap.ker L) hr)
  have hinv := hd.eq_implicitFunction hrange
  filter_upwards [nhdsWithin_le_nhds hnball, nhdsWithin_le_nhds hinv,
    self_mem_nhdsWithin] with y hy hinvy hyJ
  refine ⟨(e y).2, hy, ?_⟩
  change hd.implicitFunction f L hrange (f x) (e y).2 = y
  have hheight : f x = f y := hx.2.trans hyJ.2.symm
  rw [hheight]
  exact hinvy

theorem hausdorff_joint_lt_top : (μH[2] : Measure JointSpace) (graphJoint h) < ∞ :=
  hh.isCompact_joint.measure_lt_top_of_nhdsWithin hh.hausdorff_finiteAt_joint

/-- Finiteness of the canonical measure is a theorem, not an admissibility
field or an assumption about the sought boundary integral. -/
theorem finite_graphSurfaceMeasure : IsFiniteMeasure (graphSurfaceMeasure h) := by
  constructor
  simp only [graphSurfaceMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hh.hausdorff_joint_lt_top

theorem continuousOn_graphSlope : ContinuousOn (graphSlope h) (graphClosedPositive h) := by
  have he : graphSlope h = fun x : JointSpace => ‖fderiv ℝ (fun y : JointSpace => h y) x‖ :=
    funext (graphSlope_eq_norm_fderiv h)
  rw [he]
  exact hh.continuousOn_fderiv_closedPositive.norm

theorem continuousOn_reciprocal_slope :
    ContinuousOn (fun x => 1 / ‖graphGradient h x‖) (graphJoint h) :=
  continuousOn_const.div (hh.continuousOn_graphSlope.mono inter_subset_left)
    (fun x hx => (hh.graphSlope_pos x hx).ne')

theorem integrable_reciprocal_slope :
    Integrable (fun x => 1 / ‖graphGradient h x‖) (graphSurfaceMeasure h) := by
  letI := hh.finite_graphSurfaceMeasure
  have hi := hh.continuousOn_reciprocal_slope.integrableOn_compact
    (μ := graphSurfaceMeasure h) hh.isCompact_joint
  simpa only [IntegrableOn, graphSurfaceMeasure, Measure.restrict_smul,
    Measure.restrict_restrict_of_subset (Subset.refl (graphJoint h))] using hi

/-- The proved pointwise angle identity identifies the two canonical integrals.
This is not yet a deterministic-limit or parametric-area identification. -/
theorem graphBoundaryIntegral_eq_angle : graphBoundaryIntegral h =
    ∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h := by
  apply integral_congr_ae
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem hh.measurableSet_joint] with x hx
  exact (hh.graph_angle_identities x hx).2.2.2.2.symm

theorem integrable_jointCoth :
    Integrable (fun x => jointCoth (graphSlope h x)) (graphSurfaceMeasure h) := by
  apply hh.integrable_reciprocal_slope.congr
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem hh.measurableSet_joint] with x hx
  exact (hh.graph_angle_identities x hx).2.2.2.2.symm

end AdmissibleGraphCap
end BoundaryDraft
