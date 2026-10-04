import BoundaryDraft.Pilot3CurveAreaLocal

/-!
# Canonical regular-level measures for the smooth 3D pilot

Levels are restricted to the entire closed positive region. Negative levels
have zero mass; only right-sided regularity at zero will be asserted. Interior
critical levels outside the selected band remain unrestricted.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
noncomputable section
namespace BoundaryDraft

def pilot3Level (h : Pilot3Space → ℝ) (t : ℝ) : Set Pilot3Space :=
  pilot3ClosedPositive h ∩ {x | h x = t}

def pilot3LevelMeasure (h : Pilot3Space → ℝ) (t : ℝ) : Measure Pilot3Space :=
  (μH[1] : Measure Pilot3Space).restrict (pilot3Level h t)

def pilot3HeightDensity (h : Pilot3Space → ℝ) (t : ℝ) : ℝ :=
  ∫ x, 1 / ‖pilot3Gradient h x‖ ∂pilot3LevelMeasure h t

@[simp] theorem pilot3Level_zero (h : Pilot3Space → ℝ) : pilot3Level h 0 = pilot3SpatialJoint h := rfl
@[simp] theorem pilot3LevelMeasure_zero (h : Pilot3Space → ℝ) :
    pilot3LevelMeasure h 0 = pilot3SurfaceMeasure h := rfl

theorem pilot3_hausdorff_finiteAt_regular_level (g : Pilot3Space → ℝ)
    (L : Pilot3Space →L[ℝ] ℝ) (x : Pilot3Space) (hg : HasStrictFDerivAt g L x)
    (hL : L ≠ 0) (S : Set Pilot3Space) (hS : ∀ y ∈ S, g y = g x) :
    (μH[1] : Measure Pilot3Space).FiniteAtFilter (𝓝[S] x) := by
  letI : MeasurableSpace (LinearMap.ker L) := borel _
  letI : BorelSpace (LinearMap.ker L) := ⟨rfl⟩
  have hn : L.toLinearMap ≠ 0 := by
    intro he
    apply hL
    ext y
    exact LinearMap.congr_fun he y
  have hrange := Module.Dual.range_eq_top_of_ne_zero hn
  let e := hg.implicitToPartialHomeomorph g L hrange
  let φ := hg.implicitFunction g L hrange (g x)
  have hφ : HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 := hg.to_implicitFunction hrange
  obtain ⟨K, U, hU, hLip⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hdim : Module.finrank ℝ (LinearMap.ker L) = 1 := by
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    have he : Module.finrank ℝ Pilot3Space = 2 := by simp [Pilot3Space, DimensionSpatial]
    rw [he] at hd
    change Module.finrank ℝ (LinearMap.ker L) + 1 = 2 at hd
    omega
  have hballfinite : (μH[1] : Measure (LinearMap.ker L)) (Metric.ball 0 r) < ⊤ := by
    have hd : (Module.finrank ℝ (LinearMap.ker L) : ℝ) = 1 := by exact_mod_cast hdim
    rw [← hd]
    exact Metric.isBounded_ball.measure_lt_top
  have himage : (μH[1] : Measure Pilot3Space) (φ '' Metric.ball 0 r) < ⊤ := by
    apply ((hLip.mono hball).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)).trans_lt
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top) hballfinite
  refine ⟨φ '' Metric.ball 0 r, ?_, himage⟩
  have hx : x ∈ e.source := hg.mem_implicitToPartialHomeomorph_source hrange
  have he0 : e x = (g x, 0) := hg.implicitToPartialHomeomorph_self hrange
  have hc : Tendsto (fun y => (e y).2) (𝓝 x) (𝓝 0) := by
    simpa only [ContinuousAt, he0] using (e.continuousAt hx).snd
  filter_upwards [nhdsWithin_le_nhds (hc.eventually (Metric.ball_mem_nhds (0 : LinearMap.ker L) hr)),
    nhdsWithin_le_nhds (hg.eq_implicitFunction hrange), self_mem_nhdsWithin] with y hy hinvy hyS
  refine ⟨(e y).2, hy, ?_⟩
  change hg.implicitFunction g L hrange (g x) (e y).2 = y
  rw [← hS y hyS]
  exact hinvy

namespace Pilot3RegularHeight
variable {h : Pilot3Space → ℝ} (hh : Pilot3RegularHeight h)
include hh

theorem isCompact_level (t : ℝ) : IsCompact (pilot3Level h t) := by
  apply hh.isCompact_closedPositive.of_isClosed_subset _ inter_subset_left
  exact hh.continuousOn_closedPositive.preimage_isClosed_of_isClosed isClosed_closure (isClosed_singleton (x := t))

theorem measurableSet_level (t : ℝ) : MeasurableSet (pilot3Level h t) := (hh.isCompact_level t).isClosed.measurableSet

theorem level_eq_empty_of_neg (t : ℝ) (ht : t < 0) : pilot3Level h t = ∅ := by
  apply eq_empty_iff_forall_not_mem.2
  intro x hx
  have hn := hh.nonneg_on_closedPositive x hx.1
  rw [hx.2] at hn
  exact (not_le_of_gt ht) hn

theorem levelMeasure_eq_zero_of_neg (t : ℝ) (ht : t < 0) : pilot3LevelMeasure h t = 0 := by
  simp only [pilot3LevelMeasure, hh.level_eq_empty_of_neg t ht, Measure.restrict_empty]

theorem heightDensity_eq_zero_of_neg (t : ℝ) (ht : t < 0) : pilot3HeightDensity h t = 0 := by
  simp only [pilot3HeightDensity, hh.levelMeasure_eq_zero_of_neg t ht, integral_zero_measure]

theorem hausdorff_level_lt_top (t : ℝ) (hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0) :
    (μH[1] : Measure Pilot3Space) (pilot3Level h t) < ⊤ := by
  apply (hh.isCompact_level t).measure_lt_top_of_nhdsWithin
  intro x hx
  exact pilot3_hausdorff_finiteAt_regular_level _ _ x
    ((hh.smoothAt x hx.1).hasStrictFDerivAt (by simp)) (hreg x hx) _
    (fun y hy => hy.2.trans hx.2.symm)

theorem finite_levelMeasure (t : ℝ) (hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0) :
    IsFiniteMeasure (pilot3LevelMeasure h t) :=
  ⟨by simpa only [pilot3LevelMeasure, Measure.restrict_apply_univ] using hh.hausdorff_level_lt_top t hreg⟩

theorem continuousOn_gradient : ContinuousOn (pilot3Gradient h) (pilot3ClosedPositive h) :=
  (InnerProductSpace.toDual ℝ Pilot3Space).symm.continuous.comp_continuousOn hh.continuousOn_fderiv

theorem integrable_level_reciprocal_gradient (t : ℝ) (hreg : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0) :
    Integrable (fun x => 1 / ‖pilot3Gradient h x‖) (pilot3LevelMeasure h t) := by
  letI := hh.finite_levelMeasure t hreg
  have hc : ContinuousOn (fun x => 1 / ‖pilot3Gradient h x‖) (pilot3Level h t) := by
    apply continuousOn_const.div (hh.continuousOn_gradient.norm.mono inter_subset_left)
    intro x hx
    rw [pilot3Gradient_norm]
    exact norm_ne_zero_iff.mpr (hreg x hx)
  have hi := hc.integrableOn_compact (μ := pilot3LevelMeasure h t) (hh.isCompact_level t)
  simpa only [IntegrableOn, pilot3LevelMeasure, Measure.restrict_restrict_of_subset
    (Subset.refl (pilot3Level h t))] using hi

theorem exists_integrable_level_band : ∃ δ : ℝ, 0 < δ ∧ ∀ t ≤ δ,
    IsFiniteMeasure (pilot3LevelMeasure h t) ∧
      Integrable (fun x => 1 / ‖pilot3Gradient h x‖) (pilot3LevelMeasure h t) := by
  obtain ⟨δ, hδ, hreg⟩ := hh.exists_noncritical_band
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hr : ∀ x ∈ pilot3Level h t, fderiv ℝ h x ≠ 0 := fun x hx => hreg x hx.1 (hx.2.le.trans ht)
  exact ⟨hh.finite_levelMeasure t hr, hh.integrable_level_reciprocal_gradient t hr⟩

theorem exists_band_subset_joint_neighborhood (U : Set Pilot3Space) (hU : IsOpen U)
    (hJU : pilot3SpatialJoint h ⊆ U) : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ pilot3ClosedPositive h, h x ≤ δ → x ∈ U := by
  let K := pilot3ClosedPositive h \ U
  have hK : IsCompact K := hh.isCompact_closedPositive.diff hU
  have hp : ∀ x ∈ K, 0 < h x := by
    intro x hx
    apply lt_of_le_of_ne (hh.nonneg_on_closedPositive x hx.1)
    intro he
    exact hx.2 (hJU ⟨hx.1, he.symm⟩)
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le' (hh.continuousOn_closedPositive.mono diff_subset) hp
  refine ⟨m / 2, half_pos hm, ?_⟩
  intro x hx hδ
  by_contra hxU
  have hle := hmin x (show x ∈ K from ⟨hx, hxU⟩)
  linarith

end Pilot3RegularHeight
end BoundaryDraft
