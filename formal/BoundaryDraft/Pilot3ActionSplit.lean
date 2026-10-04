import BoundaryDraft.Pilot3Overlap
import Mathlib.MeasureTheory.Group.Prod

/-!
# Exact fixed-cutoff split of the existing three-dimensional pilot action

The original region and its actual overlap are retained. The cutoff equality
belongs to long, including null vectors. The point term is allocated once, to
short. Absolute integrability precedes the displacement shear and signed Fubini.
No short or long asymptotic conclusion is assumed here.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

/-- The long part of the full closed future cone, including cutoff equality. -/
def pilot3LongFuture (δ : ℝ) : Set Pilot3Spacetime :=
  {z | ‖z.2‖ ≤ z.1 ∧ δ ≤ z.1 + ‖z.2‖}

/-- Its exact complement in the closed future cone. -/
def pilot3ShortFuture (δ : ℝ) : Set Pilot3Spacetime :=
  dimensionCausalFuture 0 \ pilot3LongFuture δ

theorem pilot3ShortFuture_eq (δ : ℝ) : pilot3ShortFuture δ =
    {z | ‖z.2‖ ≤ z.1 ∧ z.1 + ‖z.2‖ < δ} := by
  ext z
  change (‖z.2 - 0‖ ≤ z.1 - 0 ∧ ¬ (‖z.2‖ ≤ z.1 ∧ δ ≤ z.1 + ‖z.2‖)) ↔
    (‖z.2‖ ≤ z.1 ∧ z.1 + ‖z.2‖ < δ)
  simp only [sub_zero]
  constructor
  · rintro ⟨hc, hn⟩
    exact ⟨hc, lt_of_not_ge (fun h => hn ⟨hc, h⟩)⟩
  · rintro ⟨hc, hs⟩
    exact ⟨hc, fun h => (not_le_of_gt hs) h.2⟩

theorem measurableSet_pilot3LongFuture (δ : ℝ) : MeasurableSet (pilot3LongFuture δ) :=
  ((isClosed_le continuous_snd.norm continuous_fst).inter
    (isClosed_le continuous_const (continuous_fst.add continuous_snd.norm))).measurableSet

theorem measurableSet_pilot3ShortFuture (δ : ℝ) : MeasurableSet (pilot3ShortFuture δ) :=
  (measurableSet_dimensionCausalFuture 0).diff (measurableSet_pilot3LongFuture δ)

theorem pilot3ShortFuture_disjoint_longFuture (δ : ℝ) :
    Disjoint (pilot3ShortFuture δ) (pilot3LongFuture δ) := disjoint_sdiff_self_left

theorem pilot3ShortFuture_union_longFuture (δ : ℝ) :
    pilot3ShortFuture δ ∪ pilot3LongFuture δ = dimensionCausalFuture 0 :=
  diff_union_of_subset (fun z hz => by simpa [dimensionCausalFuture] using hz.1)

/-- The unchanged pair kernel evaluated on a displacement. -/
def pilot3DisplacementKernel (ρ : ℝ) (z : Pilot3Spacetime) : ℝ :=
  dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ 0 z

theorem continuous_pilot3DisplacementKernel (ρ : ℝ) : Continuous (pilot3DisplacementKernel ρ) := by
  unfold pilot3DisplacementKernel
  exact (continuous_dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ).comp
    (f := fun z : Pilot3Spacetime => ((0 : Pilot3Spacetime), z))
    (continuous_const.prodMk continuous_id)

theorem pilot3DisplacementKernel_sub (ρ : ℝ) (x y : Pilot3Spacetime) :
    pilot3DisplacementKernel ρ (y - x) =
      dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ x y := by
  simp [pilot3DisplacementKernel, dimensionBilocalKernel, dimensionIntervalSq]

/-- The actual sharp short observable, with the original point term once. -/
def pilot3ShortAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
    dimensionPairCoefficient 3 * ρ * ∫ z in pilot3ShortFuture δ,
      pilot3DisplacementKernel ρ z * pilot3Overlap h f z)

/-- The signed long pair contribution; the full action subtracts this term. -/
def pilot3LongPairAction (ρ δ : ℝ) (h f : Pilot3Space → ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPairCoefficient 3 * ρ * ∫ z in pilot3LongFuture δ,
    pilot3DisplacementKernel ρ z * pilot3Overlap h f z)

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem measurable_overlap : Measurable (pilot3Overlap h f) := by
  have hm : StronglyMeasurable (fun p : Pilot3Spacetime × Pilot3Spacetime =>
      (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p.2 + p.1)) :=
    ((measurable_const.indicator hf.measurableSet_region).comp
      (measurable_snd.add measurable_fst)).stronglyMeasurable
  unfold pilot3Overlap pilot3WeightedOverlap
  simp only [one_mul]
  exact (hm.integral_prod_right' (ν := volume.restrict (pilot3Region h f))).measurable

omit hf in
theorem overlap_nonneg (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime) :
    0 ≤ pilot3Overlap h f z := by
  apply integral_nonneg
  intro p
  exact mul_nonneg zero_le_one (indicator_nonneg (fun _ _ => zero_le_one) _)

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
  intro x hx
  change 1 * (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (x + z) = 0
  rw [one_mul]
  apply indicator_of_not_mem
  intro hxz
  have hd := Metric.dist_le_diam_of_mem hf.isBounded_region hxz hx
  rw [dist_eq_norm, add_sub_cancel_left] at hd
  exact (not_le_of_gt hz) hd

theorem hasCompactSupport_overlap : HasCompactSupport (pilot3Overlap h f) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Pilot3Spacetime)
    (Metric.diam (pilot3Region h f)))
  intro z hz
  apply hf.overlap_eq_zero_of_diam_lt
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz

private def causalPairSet (h f : Pilot3Space → ℝ) : Set (Pilot3Spacetime × Pilot3Spacetime) :=
  {p | p.1 ∈ pilot3Region h f ∧ p.2 ∈ pilot3Region h f ∧ p.2 ∈ dimensionCausalFuture p.1}

private theorem measurableSet_causalPairSet : MeasurableSet (causalPairSet h f) := by
  have hc : MeasurableSet {p : Pilot3Spacetime × Pilot3Spacetime |
      p.2 ∈ dimensionCausalFuture p.1} :=
    (isClosed_le
      (show Continuous (fun p : Pilot3Spacetime × Pilot3Spacetime => ‖p.2.2 - p.1.2‖) by fun_prop)
      (show Continuous (fun p : Pilot3Spacetime × Pilot3Spacetime => p.2.1 - p.1.1) by fun_prop)).measurableSet
  exact (hf.measurableSet_region.preimage measurable_fst).inter
    ((hf.measurableSet_region.preimage measurable_snd).inter hc)

private theorem integrable_causalPair {w : Pilot3Spacetime → ℝ} (hw : Continuous w) :
    Integrable ((causalPairSet h f).indicator (fun p => w (p.2 - p.1))) := by
  apply (integrable_indicator_iff hf.measurableSet_causalPairSet).mpr
  exact ((hw.comp (continuous_snd.sub continuous_fst)).continuousOn.integrableOn_compact
    (hf.isCompact_closure_region.prod hf.isCompact_closure_region)).mono_set
      (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩)

omit hf in
private theorem causalPair_shear (h f : Pilot3Space → ℝ) (w : Pilot3Spacetime → ℝ)
    (x z : Pilot3Spacetime) :
    (causalPairSet h f).indicator (fun p => w (p.2 - p.1)) (x, x + z) =
      (dimensionCausalFuture 0).indicator w z * (pilot3Region h f).indicator
        (fun x => (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (x + z)) x := by
  classical
  have he : x + z ∈ dimensionCausalFuture x ↔ z ∈ dimensionCausalFuture 0 := by
    simp [dimensionCausalFuture]
  by_cases hx : x ∈ pilot3Region h f <;> by_cases hy : x + z ∈ pilot3Region h f <;>
    by_cases hz : z ∈ dimensionCausalFuture 0 <;>
    simp [causalPairSet, hx, hy, hz, he]

private theorem integral_causalPair_fibre (w : Pilot3Spacetime → ℝ) (x : Pilot3Spacetime) :
    (∫ y, (causalPairSet h f).indicator (fun p => w (p.2 - p.1)) (x, y)) =
      (pilot3Region h f).indicator
        (fun x => ∫ y in pilot3Region h f ∩ dimensionCausalFuture x, w (y - x)) x := by
  classical
  by_cases hx : x ∈ pilot3Region h f
  · rw [indicator_of_mem hx, ← integral_indicator
      (hf.measurableSet_region.inter (measurableSet_dimensionCausalFuture x))]
    congr 1
    ext y
    simp only [Set.indicator, causalPairSet, mem_setOf_eq, mem_inter_iff, hx, true_and]
  · simp [causalPairSet, hx, Set.indicator]

/-- Actual causal pairs become the actual overlap after a measure-preserving
shear. This identity retains every partner component and every signed weight. -/
theorem integral_causalPair_eq_overlap (w : Pilot3Spacetime → ℝ) (hw : Continuous w) :
    (∫ x in pilot3Region h f, ∫ y in pilot3Region h f ∩ dimensionCausalFuture x, w (y - x)) =
      ∫ z in dimensionCausalFuture 0, w z * pilot3Overlap h f z := by
  let F := (causalPairSet h f).indicator (fun p => w (p.2 - p.1))
  have hi := hf.integrable_causalPair hw
  have hmp := measurePreserving_prod_add (volume : Measure Pilot3Spacetime) volume
  have his := (hmp.integrable_comp_emb
    (MeasurableEquiv.shearAddRight Pilot3Spacetime).measurableEmbedding).mpr
      (by simpa only [← Measure.volume_eq_prod] using hi)
  calc
    _ = ∫ p, F p := by
      rw [Measure.volume_eq_prod Pilot3Spacetime Pilot3Spacetime, integral_prod _
        (by simpa only [← Measure.volume_eq_prod] using hi)]
      simp_rw [F, hf.integral_causalPair_fibre w]
      rw [integral_indicator hf.measurableSet_region]
    _ = ∫ p : Pilot3Spacetime × Pilot3Spacetime, F (p.1, p.1 + p.2) := by
      rw [Measure.volume_eq_prod Pilot3Spacetime Pilot3Spacetime]
      exact (hmp.integral_comp
        (MeasurableEquiv.shearAddRight Pilot3Spacetime).measurableEmbedding F).symm
    _ = ∫ z, (dimensionCausalFuture 0).indicator w z * pilot3Overlap h f z := by
      rw [Measure.volume_eq_prod Pilot3Spacetime Pilot3Spacetime]
      calc
        _ = ∫ z, ∫ x, F (x, x + z) := integral_prod_symm _ his
        _ = _ := by
          simp_rw [F, causalPair_shear, integral_const_mul, integral_indicator hf.measurableSet_region,
            pilot3Overlap, pilot3WeightedOverlap, one_mul]
    _ = _ := by
      simp_rw [← indicator_mul_left]
      exact integral_indicator (measurableSet_dimensionCausalFuture 0)

theorem integrableOn_overlap_weight (w : Pilot3Spacetime → ℝ) (hw : Continuous w) :
    IntegrableOn (fun z => w z * pilot3Overlap h f z) (dimensionCausalFuture 0) := by
  have hi := hf.integrable_causalPair hw
  have hmp := measurePreserving_prod_add (volume : Measure Pilot3Spacetime) volume
  have his := (hmp.integrable_comp_emb
    (MeasurableEquiv.shearAddRight Pilot3Spacetime).measurableEmbedding).mpr
      (by simpa only [← Measure.volume_eq_prod] using hi)
  have hj := his.integral_prod_right
  change Integrable (fun z => ∫ x,
    (causalPairSet h f).indicator (fun p => w (p.2 - p.1)) (x, x + z)) at hj
  simp_rw [causalPair_shear, integral_const_mul, integral_indicator hf.measurableSet_region] at hj
  have he : (fun z => (dimensionCausalFuture 0).indicator w z * pilot3Overlap h f z) =
      (fun z => (dimensionCausalFuture 0).indicator w z *
        ∫ x in pilot3Region h f, (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (x + z)) := by
    simp only [pilot3Overlap, pilot3WeightedOverlap, one_mul]
  rw [← he] at hj
  simp_rw [← indicator_mul_left] at hj
  exact (integrable_indicator_iff (measurableSet_dimensionCausalFuture 0)).mp hj

theorem action_eq_overlap (ρ : ℝ) : pilot3Action ρ h f =
    ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * volume.real (pilot3Region h f) -
      dimensionPairCoefficient 3 * ρ * ∫ z in dimensionCausalFuture 0,
        pilot3DisplacementKernel ρ z * pilot3Overlap h f z) := by
  have he := hf.integral_causalPair_eq_overlap _ (continuous_pilot3DisplacementKernel ρ)
  simp_rw [pilot3DisplacementKernel_sub] at he
  simp only [pilot3Action, dimensionWeightedAction, one_mul, integral_const,
    measureReal_restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
  rw [he]

/-- Exact finite-density split, with no asymptotic or cutoff-smallness premise. -/
theorem action_eq_short_sub_long (ρ δ : ℝ) :
    pilot3Action ρ h f = pilot3ShortAction ρ δ h f - pilot3LongPairAction ρ δ h f := by
  have hs := integral_diff (measurableSet_pilot3LongFuture δ)
    (hf.integrableOn_overlap_weight _ (continuous_pilot3DisplacementKernel ρ))
    (show pilot3LongFuture δ ⊆ dimensionCausalFuture 0 from
      fun z hz => by simpa [dimensionCausalFuture] using hz.1)
  rw [hf.action_eq_overlap, pilot3ShortAction, pilot3LongPairAction, pilot3ShortFuture, hs]
  ring

end SmoothPilot3
end BoundaryDraft
