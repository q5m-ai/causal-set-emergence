import BoundaryDraft.Pilot3Tubes
import Mathlib.MeasureTheory.Group.Prod

/-!
# Exact signed displacement split for the smooth 3D pilot

The sharp short domain is `v < δ`; equality belongs to long. The point term
occurs exactly once, in short. Every component and every causal partner is
retained. These finite-density identities assert no asymptotic theorem.
-/

open MeasureTheory Set Filter
open scoped Classical
noncomputable section
namespace BoundaryDraft

set_option maxHeartbeats 800000

/-- Closed long part of the full future cone, including null displacements. -/
def pilot3LongFuture (δ : ℝ) : Set Pilot3Spacetime :=
  {z | z ∈ dimensionCausalFuture 0 ∧ δ ≤ z.1 + ‖z.2‖}

def pilot3ShortFuture (δ : ℝ) : Set Pilot3Spacetime :=
  dimensionCausalFuture 0 \ pilot3LongFuture δ

theorem measurableSet_pilot3LongFuture (δ : ℝ) : MeasurableSet (pilot3LongFuture δ) :=
  (measurableSet_dimensionCausalFuture 0).inter
    (isClosed_le continuous_const (continuous_fst.add continuous_snd.norm)).measurableSet

theorem measurableSet_pilot3ShortFuture (δ : ℝ) : MeasurableSet (pilot3ShortFuture δ) :=
  (measurableSet_dimensionCausalFuture 0).diff (measurableSet_pilot3LongFuture δ)

theorem pilot3ShortFuture_eq (δ : ℝ) : pilot3ShortFuture δ =
    {z | z ∈ dimensionCausalFuture 0 ∧ z.1 + ‖z.2‖ < δ} := by
  ext z
  simp only [pilot3ShortFuture, pilot3LongFuture, mem_diff, mem_setOf_eq]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, lt_of_not_ge (fun h => hn ⟨hz, h⟩)⟩
  · rintro ⟨hz, hl⟩
    exact ⟨hz, fun h => (not_le_of_gt hl) h.2⟩

theorem pilot3ShortFuture_disjoint_longFuture (δ : ℝ) :
    Disjoint (pilot3ShortFuture δ) (pilot3LongFuture δ) := disjoint_sdiff_self_left

theorem pilot3ShortFuture_union_longFuture (δ : ℝ) :
    pilot3ShortFuture δ ∪ pilot3LongFuture δ = dimensionCausalFuture 0 :=
  diff_union_of_subset (fun _ hz => hz.1)

/-- The unchanged dimension-three signed pair kernel in displacement form. -/
def pilot3DisplacementKernel (ρ : ℝ) (z : Pilot3Spacetime) : ℝ :=
  dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ 0 z

theorem continuous_pilot3DisplacementKernel (ρ : ℝ) : Continuous (pilot3DisplacementKernel ρ) := by
  unfold pilot3DisplacementKernel
  exact Continuous.uncurry_left (f := dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ) 0
    (continuous_dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ)

/-- The point volume is allocated only to this short piece. -/
def pilot3ShortAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
    dimensionPairCoefficient 3 * ρ * ∫ z in pilot3ShortFuture δ,
      pilot3DisplacementKernel ρ z * pilot3Overlap h f z)

/-- Negative signed long contribution, with both density factors retained. -/
def pilot3LongAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  -(dimensionPairCoefficient 3) * ρ ^ (2 / 3 : ℝ) * ρ *
    ∫ z in pilot3LongFuture δ, pilot3DisplacementKernel ρ z * pilot3Overlap h f z

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem measurable_overlap : Measurable (pilot3Overlap h f) := by
  have hm : StronglyMeasurable (fun p : Pilot3Spacetime × Pilot3Spacetime =>
      (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p.2 + p.1)) :=
    ((measurable_const.indicator hf.measurableSet_region).comp
      (measurable_snd.add measurable_fst)).stronglyMeasurable
  change Measurable (fun z => ∫ p in pilot3Region h f,
    (1 : ℝ) * (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p + z))
  simpa only [one_mul] using
    (hm.integral_prod_right' (ν := volume.restrict (pilot3Region h f))).measurable

omit hf in
theorem overlap_nonneg (z : Pilot3Spacetime) : 0 ≤ pilot3Overlap h f z :=
  integral_nonneg fun _ => mul_nonneg zero_le_one (indicator_nonneg (fun _ _ => zero_le_one) _)

theorem overlap_le_volume (z : Pilot3Spacetime) :
    pilot3Overlap h f z ≤ volume.real (pilot3Region h f) := by
  haveI : IsFiniteMeasure (volume.restrict (pilot3Region h f)) :=
    ⟨by simpa using hf.isBounded_region.measure_lt_top⟩
  calc
    _ ≤ ∫ _p in pilot3Region h f, (1 : ℝ) :=
      integral_mono (hf.integrable_overlap_fibre (fun _ => 1) continuousOn_const z)
        (integrable_const _) (fun p => by
          by_cases hp : p + z ∈ pilot3Region h f <;> simp [hp])
    _ = _ := by simp

theorem overlap_eq_zero_of_diam_lt {z : Pilot3Spacetime}
    (hz : Metric.diam (pilot3Region h f) < ‖z‖) : pilot3Overlap h f z = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro p hp
  have hn : p + z ∉ pilot3Region h f := by
    intro hpz
    have hd := Metric.dist_le_diam_of_mem hf.isBounded_region hpz hp
    rw [dist_eq_norm, add_sub_cancel_left] at hd
    exact (not_le_of_gt hz) hd
  simp only [indicator_of_not_mem hn, mul_zero]

theorem hasCompactSupport_overlap : HasCompactSupport (pilot3Overlap h f) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : Pilot3Spacetime) (Metric.diam (pilot3Region h f)))
  intro z hz
  exact hf.overlap_eq_zero_of_diam_lt
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)

/-- Bounded compact domination, before any signed splitting or Fubini. -/
theorem integrable_overlap_weight (w : Pilot3Spacetime → ℝ) (hw : Continuous w) :
    Integrable (fun z => w z * pilot3Overlap h f z) := by
  let K := Metric.closedBall (0 : Pilot3Spacetime) (Metric.diam (pilot3Region h f))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Pilot3Spacetime)
    (Metric.diam (pilot3Region h f))).exists_bound_of_continuousOn hw.continuousOn
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Pilot3Spacetime)
      (Metric.diam (pilot3Region h f))).measure_lt_top⟩
  have hi : IntegrableOn (fun z => w z * pilot3Overlap h f z) K := by
    apply (integrable_const (max 0 C * volume.real (pilot3Region h f))).mono'
      (hw.measurable.mul hf.measurable_overlap).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    rw [norm_mul, Real.norm_eq_abs (pilot3Overlap h f z), abs_of_nonneg (overlap_nonneg z)]
    exact mul_le_mul ((hC z hz).trans (le_max_right _ _)) (hf.overlap_le_volume z)
      (overlap_nonneg z) (le_max_left _ _)
  apply (integrable_indicator_iff measurableSet_closedBall).mpr hi |>.congr
  filter_upwards with z
  by_cases hz : z ∈ K
  · exact indicator_of_mem hz _
  · rw [indicator_of_not_mem hz, hf.overlap_eq_zero_of_diam_lt
      (by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hz), mul_zero]

private def pairSet : Set (Pilot3Spacetime × Pilot3Spacetime) :=
  {p | p.1 ∈ pilot3Region h f ∧ p.2 ∈ pilot3Region h f ∧ p.2 ∈ dimensionCausalFuture p.1}

private theorem measurableSet_pairSet : MeasurableSet (pairSet (h := h) (f := f)) :=
  (hf.measurableSet_region.preimage measurable_fst).inter
    ((hf.measurableSet_region.preimage measurable_snd).inter measurableSet_dimensionCausalRelation)

omit hf in
private theorem pair_shear (w : Pilot3Spacetime → ℝ) (x z : Pilot3Spacetime) :
    (pairSet (h := h) (f := f)).indicator (fun p => w (p.2 - p.1)) (x, x + z) =
      (dimensionCausalFuture 0).indicator w z *
        (pilot3Region h f).indicator
          (fun x => (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (x + z)) x := by
  have he : x + z ∈ dimensionCausalFuture x ↔ z ∈ dimensionCausalFuture 0 := by
    simp [dimensionCausalFuture]
  by_cases hx : x ∈ pilot3Region h f <;> by_cases hy : x + z ∈ pilot3Region h f <;>
    by_cases hz : z ∈ dimensionCausalFuture 0 <;> simp [pairSet, hx, hy, hz, he]

private theorem integral_pair_fibre (w : Pilot3Spacetime → ℝ) (x : Pilot3Spacetime) :
    (∫ y, (pairSet (h := h) (f := f)).indicator (fun p => w (p.2 - p.1)) (x, y)) =
      (pilot3Region h f).indicator
        (fun x => ∫ y in pilot3Region h f ∩ dimensionCausalFuture x, w (y - x)) x := by
  by_cases hx : x ∈ pilot3Region h f
  · rw [indicator_of_mem hx, ← integral_indicator
      (hf.measurableSet_region.inter (measurableSet_dimensionCausalFuture x))]
    congr 1
    ext y
    by_cases hy : y ∈ pilot3Region h f ∩ dimensionCausalFuture x
    · rw [indicator_of_mem (show (x, y) ∈ pairSet (h := h) (f := f) from ⟨hx, hy.1, hy.2⟩),
        indicator_of_mem hy]
    · rw [indicator_of_not_mem (show (x, y) ∉ pairSet (h := h) (f := f) from
        fun hp => hy ⟨hp.2.1, hp.2.2⟩), indicator_of_not_mem hy]
  · simp [pairSet, hx, indicator]

/-- Actual endpoint/displacement shear, with absolute integrability proved first. -/
theorem integral_causalPair_eq_overlap (w : Pilot3Spacetime → ℝ) (hw : Continuous w) :
    (∫ x in pilot3Region h f, ∫ y in pilot3Region h f ∩ dimensionCausalFuture x, w (y - x)) =
      ∫ z in dimensionCausalFuture 0, w z * pilot3Overlap h f z := by
  letI : (volume : Measure Pilot3Spacetime).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let F := (pairSet (h := h) (f := f)).indicator (fun p => w (p.2 - p.1))
  have hi : Integrable F := (integrable_indicator_iff hf.measurableSet_pairSet).mpr
    (((hw.comp (continuous_snd.sub continuous_fst)).continuousOn.integrableOn_compact
      (hf.isCompact_closure_region.prod hf.isCompact_closure_region)).mono_set
        (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩))
  have hmp := measurePreserving_prod_add (volume : Measure Pilot3Spacetime) volume
  have his := (hmp.integrable_comp_emb
    (MeasurableEquiv.shearAddRight Pilot3Spacetime).measurableEmbedding).mpr
      (by simpa only [← Measure.volume_eq_prod] using hi)
  calc
    _ = ∫ p, F p := by
      rw [Measure.volume_eq_prod Pilot3Spacetime Pilot3Spacetime,
        integral_prod _ (by simpa only [← Measure.volume_eq_prod] using hi)]
      simp_rw [F, hf.integral_pair_fibre w]
      rw [integral_indicator hf.measurableSet_region]
    _ = ∫ p : Pilot3Spacetime × Pilot3Spacetime, F (p.1, p.1 + p.2) := by
      rw [Measure.volume_eq_prod Pilot3Spacetime Pilot3Spacetime]
      exact (hmp.integral_comp (MeasurableEquiv.shearAddRight Pilot3Spacetime).measurableEmbedding F).symm
    _ = ∫ z, (dimensionCausalFuture 0).indicator w z * pilot3Overlap h f z := by
      rw [Measure.volume_eq_prod Pilot3Spacetime Pilot3Spacetime]
      calc
        _ = ∫ z, ∫ x, F (x, x + z) := integral_prod_symm _ his
        _ = _ := by
          simp_rw [F, pair_shear, integral_const_mul, integral_indicator hf.measurableSet_region]
          simp only [pilot3Overlap, pilot3WeightedOverlap, one_mul]
    _ = _ := by
      simp_rw [← indicator_mul_left]
      exact integral_indicator (measurableSet_dimensionCausalFuture 0)

theorem action_eq_overlap (ρ : ℝ) : pilot3Action ρ h f =
    ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
      dimensionPairCoefficient 3 * ρ * ∫ z in dimensionCausalFuture 0,
        pilot3DisplacementKernel ρ z * pilot3Overlap h f z) := by
  have he (x y : Pilot3Spacetime) : pilot3DisplacementKernel ρ (y - x) =
      dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ x y := by
    simp [pilot3DisplacementKernel, dimensionBilocalKernel, dimensionIntervalSq]
  have hs := hf.integral_causalPair_eq_overlap _ (continuous_pilot3DisplacementKernel ρ)
  simp_rw [he] at hs
  simp only [pilot3Action, dimensionWeightedAction, Nat.reduceAdd, Nat.cast_ofNat, one_mul,
    integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]
  rw [hs]

/-- Common finite-density interface for both analytic producers. -/
theorem action_eq_short_add_long (ρ δ : ℝ) :
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f + pilot3LongAction ρ δ h f := by
  have hi := (hf.integrable_overlap_weight _ (continuous_pilot3DisplacementKernel ρ)).integrableOn
    (s := dimensionCausalFuture (0 : Pilot3Spacetime))
  have hs := integral_diff (measurableSet_pilot3LongFuture δ)
    (s := dimensionCausalFuture (0 : Pilot3Spacetime)) hi (fun _ hz => hz.1)
  rw [hf.action_eq_overlap ρ, pilot3ShortAction, pilot3LongAction, pilot3ShortFuture, hs]
  ring

end SmoothPilot3
end BoundaryDraft
