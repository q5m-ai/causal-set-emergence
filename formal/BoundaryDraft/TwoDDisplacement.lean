import BoundaryDraft.TwoDCausalOverlap
import Mathlib.MeasureTheory.Group.Prod

/-!
# Exact signed displacement split for the smooth 2D contract

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
def twoDLongFuture (δ : ℝ) : Set TwoDSpacetime :=
  {z | z ∈ dimensionCausalFuture 0 ∧ δ ≤ z.1 + ‖z.2‖}

def twoDShortFuture (δ : ℝ) : Set TwoDSpacetime :=
  dimensionCausalFuture 0 \ twoDLongFuture δ

theorem measurableSet_twoDLongFuture (δ : ℝ) : MeasurableSet (twoDLongFuture δ) :=
  (measurableSet_dimensionCausalFuture 0).inter
    (isClosed_le continuous_const (continuous_fst.add continuous_snd.norm)).measurableSet

theorem measurableSet_twoDShortFuture (δ : ℝ) : MeasurableSet (twoDShortFuture δ) :=
  (measurableSet_dimensionCausalFuture 0).diff (measurableSet_twoDLongFuture δ)

theorem twoDShortFuture_eq (δ : ℝ) : twoDShortFuture δ =
    {z | z ∈ dimensionCausalFuture 0 ∧ z.1 + ‖z.2‖ < δ} := by
  ext z
  simp only [twoDShortFuture, twoDLongFuture, mem_diff, mem_setOf_eq]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, lt_of_not_ge (fun h => hn ⟨hz, h⟩)⟩
  · rintro ⟨hz, hl⟩
    exact ⟨hz, fun h => (not_le_of_gt hl) h.2⟩

theorem twoDShortFuture_disjoint_longFuture (δ : ℝ) :
    Disjoint (twoDShortFuture δ) (twoDLongFuture δ) := disjoint_sdiff_self_left

theorem twoDShortFuture_union_longFuture (δ : ℝ) :
    twoDShortFuture δ ∪ twoDLongFuture δ = dimensionCausalFuture 0 :=
  diff_union_of_subset (fun _ hz => hz.1)

/-- The unchanged dimension-two signed pair kernel in displacement form. -/
def twoDDisplacementKernel (ρ : ℝ) (z : TwoDSpacetime) : ℝ :=
  dimensionBilocalKernel 1 (dimensionIntervalCoefficient 2) ρ 0 z

theorem continuous_twoDDisplacementKernel (ρ : ℝ) : Continuous (twoDDisplacementKernel ρ) := by
  unfold twoDDisplacementKernel
  exact Continuous.uncurry_left (f := dimensionBilocalKernel 1 (dimensionIntervalCoefficient 2) ρ) 0
    (continuous_dimensionBilocalKernel 1 (dimensionIntervalCoefficient 2) ρ)

/-- The point volume is allocated only to this short piece. -/
def twoDShortAction (ρ δ : ℝ) (h f : TwoDSpace → ℝ) : ℝ :=
  ρ ^ (2 / 2 : ℝ) * (dimensionPointCoefficient 2 * volume.real (twoDRegion h f) -
    dimensionPairCoefficient 2 * ρ * ∫ z in twoDShortFuture δ,
      twoDDisplacementKernel ρ z * twoDDisplacementOverlap h f z)

/-- Negative signed long contribution, with both density factors retained. -/
def twoDLongAction (ρ δ : ℝ) (h f : TwoDSpace → ℝ) : ℝ :=
  -(dimensionPairCoefficient 2) * ρ ^ (2 / 2 : ℝ) * ρ *
    ∫ z in twoDLongFuture δ, twoDDisplacementKernel ρ z * twoDDisplacementOverlap h f z

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem measurable_overlap : Measurable (twoDDisplacementOverlap h f) := by
  have hm : StronglyMeasurable (fun p : TwoDSpacetime × TwoDSpacetime =>
      (twoDRegion h f).indicator (fun _ => (1 : ℝ)) (p.2 + p.1)) :=
    ((measurable_const.indicator hf.measurableSet_region).comp
      (measurable_snd.add measurable_fst)).stronglyMeasurable
  change Measurable (fun z => ∫ p in twoDRegion h f,
    (1 : ℝ) * (twoDRegion h f).indicator (fun _ => (1 : ℝ)) (p + z))
  simpa only [one_mul] using
    (hm.integral_prod_right' (ν := volume.restrict (twoDRegion h f))).measurable

omit hf in
theorem overlap_nonneg (z : TwoDSpacetime) : 0 ≤ twoDDisplacementOverlap h f z :=
  integral_nonneg fun _ => mul_nonneg zero_le_one (indicator_nonneg (fun _ _ => zero_le_one) _)

theorem overlap_le_volume (z : TwoDSpacetime) :
    twoDDisplacementOverlap h f z ≤ volume.real (twoDRegion h f) := by
  haveI : IsFiniteMeasure (volume.restrict (twoDRegion h f)) :=
    ⟨by simpa using hf.isBounded_region.measure_lt_top⟩
  calc
    _ ≤ ∫ _p in twoDRegion h f, (1 : ℝ) :=
      integral_mono (hf.integrable_overlap_fibre (fun _ => 1) continuousOn_const z)
        (integrable_const _) (fun p => by
          by_cases hp : p + z ∈ twoDRegion h f <;> simp [hp])
    _ = _ := by simp

theorem overlap_eq_zero_of_diam_lt {z : TwoDSpacetime}
    (hz : Metric.diam (twoDRegion h f) < ‖z‖) : twoDDisplacementOverlap h f z = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro p hp
  have hn : p + z ∉ twoDRegion h f := by
    intro hpz
    have hd := Metric.dist_le_diam_of_mem hf.isBounded_region hpz hp
    rw [dist_eq_norm, add_sub_cancel_left] at hd
    exact (not_le_of_gt hz) hd
  simp only [indicator_of_not_mem hn, mul_zero]

theorem hasCompactSupport_overlap : HasCompactSupport (twoDDisplacementOverlap h f) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : TwoDSpacetime) (Metric.diam (twoDRegion h f)))
  intro z hz
  exact hf.overlap_eq_zero_of_diam_lt
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)

/-- Bounded compact domination, before any signed splitting or Fubini. -/
theorem integrable_overlap_weight (w : TwoDSpacetime → ℝ) (hw : Continuous w) :
    Integrable (fun z => w z * twoDDisplacementOverlap h f z) := by
  let K := Metric.closedBall (0 : TwoDSpacetime) (Metric.diam (twoDRegion h f))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : TwoDSpacetime)
    (Metric.diam (twoDRegion h f))).exists_bound_of_continuousOn hw.continuousOn
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : TwoDSpacetime)
      (Metric.diam (twoDRegion h f))).measure_lt_top⟩
  have hi : IntegrableOn (fun z => w z * twoDDisplacementOverlap h f z) K := by
    apply (integrable_const (max 0 C * volume.real (twoDRegion h f))).mono'
      (hw.measurable.mul hf.measurable_overlap).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    rw [norm_mul, Real.norm_eq_abs (twoDDisplacementOverlap h f z), abs_of_nonneg (overlap_nonneg z)]
    exact mul_le_mul ((hC z hz).trans (le_max_right _ _)) (hf.overlap_le_volume z)
      (overlap_nonneg z) (le_max_left _ _)
  apply (integrable_indicator_iff measurableSet_closedBall).mpr hi |>.congr
  filter_upwards with z
  by_cases hz : z ∈ K
  · exact indicator_of_mem hz _
  · rw [indicator_of_not_mem hz, hf.overlap_eq_zero_of_diam_lt
      (by simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hz), mul_zero]

private def pairSet : Set (TwoDSpacetime × TwoDSpacetime) :=
  {p | p.1 ∈ twoDRegion h f ∧ p.2 ∈ twoDRegion h f ∧ p.2 ∈ dimensionCausalFuture p.1}

private theorem measurableSet_pairSet : MeasurableSet (pairSet (h := h) (f := f)) :=
  (hf.measurableSet_region.preimage measurable_fst).inter
    ((hf.measurableSet_region.preimage measurable_snd).inter measurableSet_dimensionCausalRelation)

omit hf in
private theorem pair_shear (w : TwoDSpacetime → ℝ) (x z : TwoDSpacetime) :
    (pairSet (h := h) (f := f)).indicator (fun p => w (p.2 - p.1)) (x, x + z) =
      (dimensionCausalFuture 0).indicator w z *
        (twoDRegion h f).indicator
          (fun x => (twoDRegion h f).indicator (fun _ => (1 : ℝ)) (x + z)) x := by
  have he : x + z ∈ dimensionCausalFuture x ↔ z ∈ dimensionCausalFuture 0 := by
    simp [dimensionCausalFuture]
  by_cases hx : x ∈ twoDRegion h f <;> by_cases hy : x + z ∈ twoDRegion h f <;>
    by_cases hz : z ∈ dimensionCausalFuture 0 <;> simp [pairSet, hx, hy, hz, he]

private theorem integral_pair_fibre (w : TwoDSpacetime → ℝ) (x : TwoDSpacetime) :
    (∫ y, (pairSet (h := h) (f := f)).indicator (fun p => w (p.2 - p.1)) (x, y)) =
      (twoDRegion h f).indicator
        (fun x => ∫ y in twoDRegion h f ∩ dimensionCausalFuture x, w (y - x)) x := by
  by_cases hx : x ∈ twoDRegion h f
  · rw [indicator_of_mem hx, ← integral_indicator
      (hf.measurableSet_region.inter (measurableSet_dimensionCausalFuture x))]
    congr 1
    ext y
    by_cases hy : y ∈ twoDRegion h f ∩ dimensionCausalFuture x
    · rw [indicator_of_mem (show (x, y) ∈ pairSet (h := h) (f := f) from ⟨hx, hy.1, hy.2⟩),
        indicator_of_mem hy]
    · rw [indicator_of_not_mem (show (x, y) ∉ pairSet (h := h) (f := f) from
        fun hp => hy ⟨hp.2.1, hp.2.2⟩), indicator_of_not_mem hy]
  · simp [pairSet, hx, indicator]

/-- Actual endpoint/displacement shear, with absolute integrability proved first. -/
theorem integral_causalPair_eq_overlap (w : TwoDSpacetime → ℝ) (hw : Continuous w) :
    (∫ x in twoDRegion h f, ∫ y in twoDRegion h f ∩ dimensionCausalFuture x, w (y - x)) =
      ∫ z in dimensionCausalFuture 0, w z * twoDDisplacementOverlap h f z := by
  letI : (volume : Measure TwoDSpacetime).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let F := (pairSet (h := h) (f := f)).indicator (fun p => w (p.2 - p.1))
  have hi : Integrable F := (integrable_indicator_iff hf.measurableSet_pairSet).mpr
    (((hw.comp (continuous_snd.sub continuous_fst)).continuousOn.integrableOn_compact
      (hf.isCompact_closure_region.prod hf.isCompact_closure_region)).mono_set
        (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩))
  have hmp := measurePreserving_prod_add (volume : Measure TwoDSpacetime) volume
  have his := (hmp.integrable_comp_emb
    (MeasurableEquiv.shearAddRight TwoDSpacetime).measurableEmbedding).mpr
      (by simpa only [← Measure.volume_eq_prod] using hi)
  calc
    _ = ∫ p, F p := by
      rw [Measure.volume_eq_prod TwoDSpacetime TwoDSpacetime,
        integral_prod _ (by simpa only [← Measure.volume_eq_prod] using hi)]
      simp_rw [F, hf.integral_pair_fibre w]
      rw [integral_indicator hf.measurableSet_region]
    _ = ∫ p : TwoDSpacetime × TwoDSpacetime, F (p.1, p.1 + p.2) := by
      rw [Measure.volume_eq_prod TwoDSpacetime TwoDSpacetime]
      exact (hmp.integral_comp (MeasurableEquiv.shearAddRight TwoDSpacetime).measurableEmbedding F).symm
    _ = ∫ z, (dimensionCausalFuture 0).indicator w z * twoDDisplacementOverlap h f z := by
      rw [Measure.volume_eq_prod TwoDSpacetime TwoDSpacetime]
      calc
        _ = ∫ z, ∫ x, F (x, x + z) := integral_prod_symm _ his
        _ = _ := by
          simp_rw [F, pair_shear, integral_const_mul, integral_indicator hf.measurableSet_region]
          simp only [twoDDisplacementOverlap, twoDWeightedOverlap, one_mul]
    _ = _ := by
      simp_rw [← indicator_mul_left]
      exact integral_indicator (measurableSet_dimensionCausalFuture 0)

theorem action_eq_overlap (ρ : ℝ) : twoDAction ρ h f =
    ρ ^ (2 / 2 : ℝ) * (dimensionPointCoefficient 2 * volume.real (twoDRegion h f) -
      dimensionPairCoefficient 2 * ρ * ∫ z in dimensionCausalFuture 0,
        twoDDisplacementKernel ρ z * twoDDisplacementOverlap h f z) := by
  have he (x y : TwoDSpacetime) : twoDDisplacementKernel ρ (y - x) =
      dimensionBilocalKernel 1 (dimensionIntervalCoefficient 2) ρ x y := by
    simp [twoDDisplacementKernel, dimensionBilocalKernel, dimensionIntervalSq]
  have hs := hf.integral_causalPair_eq_overlap _ (continuous_twoDDisplacementKernel ρ)
  simp_rw [he] at hs
  simp only [twoDAction, dimensionWeightedAction, Nat.reduceAdd, Nat.cast_ofNat, one_mul,
    integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]
  rw [hs]

/-- Common finite-density interface for both analytic producers. -/
theorem action_eq_short_add_long (ρ δ : ℝ) :
    twoDAction ρ h f = twoDShortAction ρ δ h f + twoDLongAction ρ δ h f := by
  have hi := (hf.integrable_overlap_weight _ (continuous_twoDDisplacementKernel ρ)).integrableOn
    (s := dimensionCausalFuture (0 : TwoDSpacetime))
  have hs := integral_diff (measurableSet_twoDLongFuture δ)
    (s := dimensionCausalFuture (0 : TwoDSpacetime)) hi (fun _ hz => hz.1)
  rw [hf.action_eq_overlap ρ, twoDShortAction, twoDLongAction, twoDShortFuture, hs]
  ring

end SmoothTwoD
end BoundaryDraft
