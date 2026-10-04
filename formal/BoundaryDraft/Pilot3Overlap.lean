import BoundaryDraft.Pilot3Geometry

/-!
# Actual causal overlaps for the unchanged smooth 3D pilot

The observable is defined by the original region indicator, not by a gap
formula. Signed spatial weights act only on the first endpoint. Absolute
integrability precedes product Fubini; endpoint ordering then proves L3 of
`notes/dimension-long-null.md` and T5 of `notes/dimension-three-short.md`.
Null displacements, the vertex, empty fibres and exact contacts are included.
No overlap, jet or cancellation field is added to `SmoothPilot3`.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A reusable witness for the EXISTING combined slope budget, not extra
admissibility data. No integral or regularity conclusion is a field. -/
structure Pilot3SlopeControl (h f : Pilot3Space → ℝ) (κ η : ℝ) : Prop where
  height_nonneg : 0 ≤ κ
  future_nonneg : 0 ≤ η
  budget : κ + η < 1
  height_lipschitz : ∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * ‖y - x‖
  future_lipschitz : ∀ x y, |f x - f y| ≤ η * ‖y - x‖

theorem SmoothPilot3.exists_slopeControl {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    ∃ κ η : ℝ, Pilot3SlopeControl h f κ η := by
  obtain ⟨κ, η, hk, he, hb, hh, hF⟩ := hf.slope_budget
  exact ⟨κ, η, hk, he, hb, hh, hF⟩

/-- The original weighted covariogram, retaining every future partner. -/
def pilot3WeightedOverlap (h f w : Pilot3Space → ℝ) (z : Pilot3Spacetime) : ℝ :=
  ∫ p in pilot3Region h f, w p.2 * (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p + z)

def pilot3Overlap (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime) : ℝ :=
  pilot3WeightedOverlap h f (fun _ => 1) z

/-- The globally continuous envelope gap of L3, with only the future translated. -/
def pilot3OverlapGap (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime) (x : Pilot3Space) : ℝ :=
  max 0 (h x) + f (x + z.2) - f x - z.1

/-- The short consumer's actual displacement cost, T5. -/
def pilot3ShortGap (f : Pilot3Space → ℝ) (z : Pilot3Spacetime) (x : Pilot3Space) : ℝ :=
  z.1 - f (x + z.2) + f x

namespace Pilot3SlopeControl
variable {h f : Pilot3Space → ℝ} {κ η : ℝ} (C : Pilot3SlopeControl h f κ η)
include C

theorem lower_lipschitz (x y : Pilot3Space) :
    |(f x - max 0 (h x)) - (f y - max 0 (h y))| ≤ (κ + η) * ‖y - x‖ := by
  calc
    _ = |(f x - f y) - (max 0 (h x) - max 0 (h y))| := by congr 1; ring
    _ ≤ |f x - f y| + |max 0 (h x) - max 0 (h y)| := abs_sub _ _
    _ ≤ η * ‖y - x‖ + κ * ‖y - x‖ := add_le_add (C.future_lipschitz x y) (C.height_lipschitz x y)
    _ = _ := by ring

theorem future_increment (x b : Pilot3Space) : |f (x + b) - f x| ≤ η * ‖b‖ := by
  simpa only [abs_sub_comm, add_sub_cancel_left] using C.future_lipschitz x (x + b)

/-- Both selected endpoints are valid even for null or zero displacements. -/
theorem causal_endpoint_order (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space) :
    f (x + z.2) - z.1 ≤ f x ∧
      (f (x + z.2) - max 0 (h (x + z.2))) - z.1 ≤ f x - max 0 (h x) := by
  have ht := (norm_nonneg z.2).trans hz
  have hu := (abs_le.mp (C.future_increment x z.2)).2
  have hl := (abs_le.mp (C.lower_lipschitz (x + z.2) x)).2
  rw [norm_sub_rev, add_sub_cancel_left] at hl
  have hη : η ≤ 1 := by linarith [C.budget, C.height_nonneg]
  have hu' := (mul_le_mul_of_nonneg_left hz C.future_nonneg).trans
    (mul_le_of_le_one_left ht hη)
  have hl' := (mul_le_mul_of_nonneg_left hz (add_nonneg C.height_nonneg C.future_nonneg)).trans
    (mul_le_of_le_one_left ht C.budget.le)
  constructor <;> linarith

/-- This is an equality of actual open vertical intersections, not merely
an almost-everywhere length identity. Empty/contact fibres stay empty. -/
theorem mem_overlap_fibre (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space) (t : ℝ) :
    ((t, x) ∈ pilot3Region h f ∧ (t, x) + z ∈ pilot3Region h f) ↔
      t ∈ Ioo (f x - max 0 (h x)) (f (x + z.2) - z.1) := by
  rw [pilot3Region_eq_envelopes]
  have he := C.causal_endpoint_order z hz x
  change ((f x - max 0 (h x) < t ∧ t < f x) ∧
    (f (x + z.2) - max 0 (h (x + z.2)) < t + z.1 ∧ t + z.1 < f (x + z.2))) ↔
    (f x - max 0 (h x) < t ∧ t < f (x + z.2) - z.1)
  constructor
  · intro ht
    exact ⟨ht.1.1, by have := ht.2.2; linarith⟩
  · intro ht
    exact ⟨⟨ht.1, ht.2.trans_le he.1⟩,
      ⟨by have := ht.1; have := he.2; linarith, by have := ht.2; linarith⟩⟩

/-- Contact gives an EMPTY open fibre, not an extra endpoint mass. -/
theorem overlap_fibre_empty_of_nonpos_gap (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1)
    (x : Pilot3Space) (hg : pilot3OverlapGap h f z x ≤ 0) (t : ℝ) :
    ¬ ((t, x) ∈ pilot3Region h f ∧ (t, x) + z ∈ pilot3Region h f) := by
  rw [C.mem_overlap_fibre z hz x t]
  intro ht
  dsimp [pilot3OverlapGap] at hg
  have := ht.1
  have := ht.2
  linarith

theorem shortGap_bounds (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space) :
    (1 - η) * z.1 ≤ pilot3ShortGap f z x ∧ pilot3ShortGap f z x ≤ (1 + η) * z.1 := by
  have hb := abs_le.mp (C.future_increment x z.2)
  have hm := mul_le_mul_of_nonneg_left hz C.future_nonneg
  dsimp [pilot3ShortGap]
  constructor <;> nlinarith

/-- Quantitative margins at BOTH endpoints. The lower-envelope constant is
the original combined budget; raw height is not differentiated. -/
theorem gap_le_heights (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space) :
    pilot3OverlapGap h f z x ≤ max 0 (h x) - (1 - η) * z.1 ∧
    pilot3OverlapGap h f z x ≤ max 0 (h (x + z.2)) - (1 - κ - η) * z.1 := by
  have hu := (abs_le.mp (C.future_increment x z.2)).2
  have hl := (abs_le.mp (C.lower_lipschitz (x + z.2) x)).2
  rw [norm_sub_rev, add_sub_cancel_left] at hl
  have h1 := mul_le_mul_of_nonneg_left hz C.future_nonneg
  have h2 := mul_le_mul_of_nonneg_left hz (add_nonneg C.height_nonneg C.future_nonneg)
  unfold pilot3OverlapGap
  constructor <;> nlinarith

theorem gap_height_margins (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space)
    (hg : 0 ≤ pilot3OverlapGap h f z x) :
    (1 - κ - η) * z.1 ≤ max 0 (h x) ∧
      (1 - κ - η) * z.1 ≤ max 0 (h (x + z.2)) := by
  have hb := C.gap_le_heights z hz x
  have ht := (norm_nonneg z.2).trans hz
  constructor <;> nlinarith [mul_nonneg C.height_nonneg ht]

theorem positive_endpoints (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space)
    (hg : 0 < pilot3OverlapGap h f z x) : 0 < h x ∧ 0 < h (x + z.2) := by
  have hb := C.gap_le_heights z hz x
  have ht := (norm_nonneg z.2).trans hz
  have hm : 0 ≤ (1 - κ - η) * z.1 := mul_nonneg (by linarith [C.budget]) ht
  have hu : 0 ≤ (1 - η) * z.1 := mul_nonneg (by linarith [C.budget, C.height_nonneg]) ht
  have h0 : 0 < max 0 (h x) := by linarith
  have h1 : 0 < max 0 (h (x + z.2)) := by linarith
  exact ⟨by simpa using h0, by simpa using h1⟩

theorem gap_nonpos_of_source_nonpos (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1)
    (x : Pilot3Space) (hx : h x ≤ 0) : pilot3OverlapGap h f z x ≤ 0 :=
  le_of_not_gt (fun hg => not_lt_of_ge hx (C.positive_endpoints z hz x hg).1)

end Pilot3SlopeControl

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem continuous_overlapGap (z : Pilot3Spacetime) : Continuous (pilot3OverlapGap h f z) :=
  ((hf.continuous_positivePart.add
    (hf.continuous_future.comp (continuous_id.add continuous_const))).sub hf.continuous_future).sub continuous_const

theorem continuous_shortGap (z : Pilot3Spacetime) : Continuous (pilot3ShortGap f z) :=
  (continuous_const.sub (hf.continuous_future.comp
    (continuous_id.add continuous_const))).add hf.continuous_future

/-- The weight need only be continuous on the closed positive region; its
irrelevant exterior values need not even be measurable. -/
theorem integrable_overlap_fibre (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) :
    IntegrableOn (fun p : Pilot3Spacetime =>
      w p.2 * (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p + z)) (pilot3Region h f) := by
  have hc : ContinuousOn (fun p : Pilot3Spacetime => w p.2) (closure (pilot3Region h f)) :=
    hw.comp continuous_snd.continuousOn (fun p hp => ((hf.mem_closure_region p).mp hp).1)
  have hi := (hc.integrableOn_compact (μ := volume) hf.isCompact_closure_region).mono_set subset_closure
  have hm : MeasurableSet ((fun p : Pilot3Spacetime => p + z) ⁻¹' pilot3Region h f) :=
    hf.measurableSet_region.preimage (continuous_id.add continuous_const).measurable
  have he : (fun p : Pilot3Spacetime => w p.2 *
      (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p + z)) =
      ((fun p : Pilot3Spacetime => p + z) ⁻¹' pilot3Region h f).indicator (fun p => w p.2) := by
    ext p
    by_cases hp : p + z ∈ pilot3Region h f <;> simp [indicator, hp]
  rw [he]
  exact hi.indicator hm

/-- Absolute spatial integrability, including signed weights with arbitrary
exterior values. Causality makes the positive-part integrand vanish there. -/
theorem integrable_weighted_overlapGap (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
    Integrable (fun x => w x * max 0 (pilot3OverlapGap h f z x)) := by
  have hc : Continuous (fun x => max 0 (pilot3OverlapGap h f z x)) :=
    continuous_const.max (hf.continuous_overlapGap z)
  have hi := (hw.mul hc.continuousOn).integrableOn_compact
    (μ := volume) hf.toPilot3RegularHeight.isCompact_closedPositive
  have hind := (integrable_indicator_iff
    hf.toPilot3RegularHeight.isCompact_closedPositive.isClosed.measurableSet).mpr hi
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  apply hind.congr
  filter_upwards with x
  by_cases hx : x ∈ pilot3ClosedPositive h
  · exact indicator_of_mem hx _
  · rw [indicator_of_not_mem hx, max_eq_left (C.gap_nonpos_of_source_nonpos z hz x
      (le_of_not_gt (fun hp => hx (subset_closure hp)))), mul_zero]

/-- L3/T5 at EVERY causal displacement, including null directions and zero.
The source weight is signed and all partner components remain in the indicator. -/
theorem weightedOverlap_eq_gap (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
    pilot3WeightedOverlap h f w z = ∫ x, w x * max 0 (pilot3OverlapGap h f z x) := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  have hi := (integrable_indicator_iff hf.measurableSet_region).mpr (hf.integrable_overlap_fibre w hw z)
  rw [Measure.volume_eq_prod] at hi
  rw [pilot3WeightedOverlap, ← integral_indicator hf.measurableSet_region,
    Measure.volume_eq_prod, integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have he (t : ℝ) : (pilot3Region h f).indicator
        (fun p => w p.2 * (pilot3Region h f).indicator (fun _ => (1 : ℝ)) (p + z)) (t, x) =
        (Ioo (f x - max 0 (h x)) (f (x + z.2) - z.1)).indicator (fun _ => w x) t := by
      have ht := C.mem_overlap_fibre z hz x t
      by_cases hp : (t, x) ∈ pilot3Region h f
      · by_cases hq : (t, x) + z ∈ pilot3Region h f
        · simp [indicator_of_mem hp, indicator_of_mem hq, indicator_of_mem (ht.mp ⟨hp, hq⟩)]
        · rw [indicator_of_mem hp, indicator_of_not_mem hq,
            indicator_of_not_mem (fun hmem => hq (ht.mpr hmem).2), mul_zero]
      · rw [indicator_of_not_mem hp,
          indicator_of_not_mem (fun hmem => hp (ht.mpr hmem).1)]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
      smul_eq_mul, Real.volume_real_Ioo]
    rw [show (f (x + z.2) - z.1) - (f x - max 0 (h x)) = pilot3OverlapGap h f z x by
      unfold pilot3OverlapGap; ring, max_comm]
    ring

/-- The raw short gap is used only on the positive source set. No assumption
is made on raw height outside its closed positive region. -/
theorem weightedOverlap_eq_shortGap (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
    pilot3WeightedOverlap h f w z =
      ∫ x in {x | 0 < h x}, w x * max 0 (h x - pilot3ShortGap f z x) := by
  rw [hf.weightedOverlap_eq_gap w hw z hz,
    ← integral_indicator hf.toPilot3RegularHeight.isOpen_positive.measurableSet]
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : 0 < h x
    · rw [indicator_of_mem (show x ∈ {x | 0 < h x} from hx)]
      congr 2
      unfold pilot3OverlapGap pilot3ShortGap
      rw [max_eq_right hx.le]
      ring
    · rw [indicator_of_not_mem (show x ∉ {x | 0 < h x} from hx),
        max_eq_left (C.gap_nonpos_of_source_nonpos z hz x (le_of_not_gt hx)), mul_zero]

theorem overlap_eq_gap (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
    pilot3Overlap h f z = ∫ x, max 0 (pilot3OverlapGap h f z x) := by
  simpa only [pilot3Overlap, one_mul] using hf.weightedOverlap_eq_gap (fun _ => 1) continuousOn_const z hz

/-- Signed source partitions act linearly. This does NOT assert additivity
under a componentwise splitting of the partner region. -/
theorem weightedOverlap_add (w₁ w₂ : Pilot3Space → ℝ)
    (hw₁ : ContinuousOn w₁ (pilot3ClosedPositive h)) (hw₂ : ContinuousOn w₂ (pilot3ClosedPositive h))
    (z : Pilot3Spacetime) :
    pilot3WeightedOverlap h f (fun x => w₁ x + w₂ x) z =
      pilot3WeightedOverlap h f w₁ z + pilot3WeightedOverlap h f w₂ z := by
  unfold pilot3WeightedOverlap
  simp_rw [add_mul]
  exact integral_add (hf.integrable_overlap_fibre w₁ hw₁ z) (hf.integrable_overlap_fibre w₂ hw₂ z)

theorem weightedOverlap_zero (w : Pilot3Space → ℝ) (hw : ContinuousOn w (pilot3ClosedPositive h)) :
    pilot3WeightedOverlap h f w 0 = ∫ x in {x | 0 < h x}, w x * h x := by
  rw [hf.weightedOverlap_eq_shortGap w hw 0 (by simp)]
  apply setIntegral_congr_fun hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  intro x hx
  change 0 < h x at hx
  simp [pilot3ShortGap, max_eq_right hx.le]

/-- Absolute integrability of the raw spatial expression, before a signed
bulk/correction decomposition. No noncriticality is assumed in the interior. -/
theorem integrableOn_weighted_shortGap (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) :
    IntegrableOn (fun x => w x * pilot3ShortGap f z x) {x | 0 < h x} :=
  ((hw.mul (hf.continuous_shortGap z).continuousOn).integrableOn_compact
    hf.toPilot3RegularHeight.isCompact_closedPositive).mono_set subset_closure

theorem weightedOverlap_eq_bulk_add_correction (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
    pilot3WeightedOverlap h f w z =
      (∫ x in {x | 0 < h x}, w x * h x) -
      (∫ x in {x | 0 < h x}, w x * pilot3ShortGap f z x) +
      ∫ x in {x | 0 < h x}, w x * max 0 (pilot3ShortGap f z x - h x) := by
  have hh := ((hw.mul hf.toPilot3RegularHeight.continuousOn_closedPositive).integrableOn_compact
    (μ := volume) hf.toPilot3RegularHeight.isCompact_closedPositive).mono_set subset_closure
  have hq := hf.integrableOn_weighted_shortGap w hw z
  have hc : ContinuousOn (fun x => max 0 (pilot3ShortGap f z x - h x)) (pilot3ClosedPositive h) :=
    fun x hx => continuousWithinAt_const.max
      (((hf.continuous_shortGap z).continuousOn x hx).sub
        (hf.toPilot3RegularHeight.continuousOn_closedPositive x hx))
  have hi := ((hw.mul hc).integrableOn_compact
    (μ := volume) hf.toPilot3RegularHeight.isCompact_closedPositive).mono_set subset_closure
  have hsum := integral_add (hh.sub hq) hi
  simp only [Pi.add_apply, Pi.sub_apply] at hsum
  rw [hf.weightedOverlap_eq_shortGap w hw z hz, ← integral_sub hh hq, ← hsum]
  apply setIntegral_congr_fun hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  intro x _
  dsimp only
  rcases le_total (h x) (pilot3ShortGap f z x) with hl | hl
  · rw [max_eq_left (sub_nonpos.mpr hl), max_eq_right (sub_nonneg.mpr hl)]
    ring
  · rw [max_eq_right (sub_nonneg.mpr hl), max_eq_left (sub_nonpos.mpr hl)]
    ring

/-- The correction is supported on the actual moving collar, with exact
contacts contributing zero. This is a set-integral identity, NOT coarea. -/
theorem weighted_correction_eq_collar (w : Pilot3Space → ℝ) (z : Pilot3Spacetime) :
    (∫ x in {x | 0 < h x}, w x * max 0 (pilot3ShortGap f z x - h x)) =
      ∫ x in {x | 0 < h x ∧ h x < pilot3ShortGap f z x}, w x * (pilot3ShortGap f z x - h x) := by
  let A := {x | max 0 (h x) < pilot3ShortGap f z x}
  have hA : MeasurableSet A := (isOpen_lt hf.continuous_positivePart (hf.continuous_shortGap z)).measurableSet
  have he : {x | 0 < h x ∧ h x < pilot3ShortGap f z x} = A ∩ {x | 0 < h x} := by
    ext x
    by_cases hx : 0 < h x
    · simp only [A, mem_setOf_eq, mem_inter_iff, max_eq_right hx.le, hx, true_and, and_true]
    · simp [hx]
  rw [he, ← Measure.restrict_restrict hA, ← integral_indicator hA]
  apply setIntegral_congr_fun hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  intro x hx
  change 0 < h x at hx
  dsimp only
  by_cases hq : h x < pilot3ShortGap f z x
  · have ha : x ∈ A := by simpa only [A, mem_setOf_eq, max_eq_right hx.le] using hq
    rw [indicator_of_mem ha, max_eq_right (sub_nonneg.mpr hq.le)]
  · have ha : x ∉ A := by simpa only [A, mem_setOf_eq, max_eq_right hx.le] using hq
    rw [indicator_of_not_mem ha, max_eq_left (sub_nonpos.mpr (le_of_not_gt hq)), mul_zero]

/-- T5 with its original point-volume term and actual moving-collar domain.
No regular-height substitution, collar atlas or divergence identity is asserted. -/
theorem weightedOverlap_eq_bulk_add_collar (w : Pilot3Space → ℝ)
    (hw : ContinuousOn w (pilot3ClosedPositive h)) (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) :
    pilot3WeightedOverlap h f w z = pilot3WeightedOverlap h f w 0 -
      (∫ x in {x | 0 < h x}, w x * pilot3ShortGap f z x) +
      ∫ x in {x | 0 < h x ∧ h x < pilot3ShortGap f z x}, w x * (pilot3ShortGap f z x - h x) := by
  rw [hf.weightedOverlap_zero w hw, ← hf.weighted_correction_eq_collar w z]
  exact hf.weightedOverlap_eq_bulk_add_correction w hw z hz

end SmoothPilot3
end BoundaryDraft
