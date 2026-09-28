import BoundaryDraft.TwoFaceOverlap
import BoundaryDraft.WeightedGraphAction

/-!
# Exact short/long and source partitions

Finite-density identities only. The conventional curved-face stability proof
in `notes/curved-face-stability.md` is NOT an end-to-end Lean theorem here.
In particular no overlap Taylor expansion or geometric limit is assumed.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace BoundaryDraft

/-- The exact complement of the existing long domain inside the causal cone.
The cutoff equality belongs to the long part, including null displacements. -/
def shortFuture (δ : ℝ) : Set Spacetime := causalFuture 0 \ longFuture δ

theorem shortFuture_eq (δ : ℝ) : shortFuture δ =
    {z | z ∈ causalFuture 0 ∧ z 0 + spatialDistance 0 (spatialPart z) < δ} := by
  ext z
  simp only [shortFuture, longFuture, mem_diff, mem_setOf_eq]
  constructor
  · rintro ⟨hz, hn⟩
    exact ⟨hz, lt_of_not_ge (fun h => hn ⟨hz, h⟩)⟩
  · rintro ⟨hz, hl⟩
    exact ⟨hz, fun h => (not_le_of_gt hl) h.2⟩

theorem measurableSet_shortFuture (δ : ℝ) : MeasurableSet (shortFuture δ) :=
  (isClosed_causalFuture 0).measurableSet.diff (measurableSet_longFuture δ)

theorem shortFuture_disjoint_longFuture (δ : ℝ) :
    Disjoint (shortFuture δ) (longFuture δ) := disjoint_sdiff_self_left

theorem shortFuture_union_longFuture (δ : ℝ) :
    shortFuture δ ∪ longFuture δ = causalFuture 0 :=
  diff_union_of_subset (fun _ hz => hz.1)

/-- Absolute integrability is inherited BEFORE splitting the signed kernel. -/
theorem integrableOn_short_overlap {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) (w : Spacetime → ℝ) (hw : Continuous w) :
    IntegrableOn (fun z => w z * translatedOverlap M z) (shortFuture δ) :=
  (integrableOn_overlap_weight hm hb w hw).mono_set diff_subset

theorem integral_overlap_short_add_long {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (δ : ℝ) (w : Spacetime → ℝ) (hw : Continuous w) :
    (∫ z in shortFuture δ, w z * translatedOverlap M z) +
      (∫ z in longFuture δ, w z * translatedOverlap M z) =
        ∫ z in causalFuture 0, w z * translatedOverlap M z := by
  rw [shortFuture, integral_diff (measurableSet_longFuture δ)
    (integrableOn_overlap_weight hm hb w hw) (fun _ hz => hz.1)]
  ring

/-- Allocate the point term once to the short domain. This is a piece of the
unchanged action, not a new proposed action or a vanishing-long-term premise. -/
def shortContinuumMean (ρ δ : ℝ) (M : Set Spacetime) : ℝ :=
  (4 / Real.sqrt 6) * Real.sqrt ρ * (volume.real M - ρ * ∫ z in shortFuture δ,
    bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) * translatedOverlap M z)

theorem continuumMean_eq_short_sub_long {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ δ : ℝ) :
    continuumMean ρ M = shortContinuumMean ρ δ M -
      (4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ z in longFuture δ,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) * translatedOverlap M z := by
  have hw : Continuous (fun z : Spacetime => bdgKernel ((Real.pi / 24) * ρ *
      intervalSq 0 z ^ 2)) := by
    unfold bdgKernel bdgPolynomial intervalSq spatialSeparationSq
    fun_prop
  rw [continuumMean_eq_translatedOverlap hm hb ρ,
    ← integral_overlap_short_add_long hm hb δ _ hw, shortContinuumMean]
  ring

/-- The long term is precisely #61's ACTUAL density, with every density factor.
No right-hand jet or cancellation of this term is claimed. -/
theorem AdmissibleTwoFace.continuumMean_eq_short_sub_density
    {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    continuumMean ρ (twoFaceRegion h f) = shortContinuumMean ρ δ (twoFaceRegion h f) -
      (4 / Real.sqrt 6) * Real.sqrt ρ * ρ * ∫ σ : ℝ,
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) *
          longOverlapDensity (twoFaceRegion h f) δ σ := by
  rw [continuumMean_eq_short_sub_long hf.measurableSet_region hf.isBounded_region,
    hf.integral_longOverlap_bdg hδ]

/-- Source weights need agree only on the actual region, not on exterior points. -/
theorem weightedContinuumMean_congr {M : Set Spacetime} (hm : MeasurableSet M)
    (ρ : ℝ) {w v : Spacetime → ℝ} (h : EqOn w v M) :
    weightedContinuumMean ρ M w = weightedContinuumMean ρ M v := by
  unfold weightedContinuumMean
  rw [setIntegral_congr_fun hm h]
  congr 3
  exact setIntegral_congr_fun hm (fun x hx => by rw [h hx])

/-- Finite source sums preserve all second endpoints; no disjointness premise. -/
theorem weightedContinuumMean_finset_sum {ι : Type*} (s : Finset ι)
    {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (ρ : ℝ) (w : ι → Spacetime → ℝ) (hw : ∀ i, Continuous (w i)) :
    weightedContinuumMean ρ M (fun x => ∑ i ∈ s, w i x) =
      ∑ i ∈ s, weightedContinuumMean ρ M (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedContinuumMean]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [show (fun x => w i x + ∑ j ∈ s, w j x) =
      w i + (fun x => ∑ j ∈ s, w j x) from rfl,
      weightedContinuumMean_add hm hb ρ (hw i) (continuous_finset_sum s (fun j _ => hw j)), ih]

/-- Overlap-aware partition of the original bilocal action at every density. -/
theorem continuumMean_eq_sum_source_weights {ι : Type*} (s : Finset ι)
    {M : Set Spacetime} (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (ρ : ℝ) (w : ι → Spacetime → ℝ) (hw : ∀ i, Continuous (w i))
    (hs : ∀ x ∈ M, ∑ i ∈ s, w i x = 1) :
    continuumMean ρ M = ∑ i ∈ s, weightedContinuumMean ρ M (w i) := by
  rw [← weightedContinuumMean_finset_sum s hm hb ρ w hw]
  exact (weightedContinuumMean_one ρ M).symm.trans
    (weightedContinuumMean_congr hm ρ (fun x hx => (hs x hx).symm))

end BoundaryDraft
