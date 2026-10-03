import BoundaryDraft.IndependentFaceGeometry
import BoundaryDraft.TwoFaceNullGap

/-!
# Geometric envelope data for the fixed-cutoff long proof

This derived package is NOT a new admissibility contract. Both the original
class and class E supply it. Its upper face is a global causal envelope, smooth
only inside the positive region; no smoothness at the clipped joint is used.
There is no combined slope budget or analytic conclusion among its fields.
-/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Geometric inputs shared by the two long-proof callers. -/
structure LongEnvelopeData (h u : Spatial → ℝ) : Prop extends RegularHeight h where
  strictGraphLipschitz_upper : StrictGraphLipschitz u
  strictGraphLipschitz_lower : StrictGraphLipschitz (fun x => u x - max 0 (h x))
  smooth_positive : ∀ x : JointSpace, 0 < h x → ContDiffAt ℝ 3 (fun y : JointSpace => u y) x
  isBounded_region : Bornology.IsBounded (twoFaceRegion h u)

theorem AdmissibleTwoFace.toLongEnvelopeData {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) : LongEnvelopeData h f where
  toRegularHeight := hf.toAdmissibleGraphCap.toRegularHeight
  strictGraphLipschitz_upper := hf.strictGraphLipschitz_upper
  strictGraphLipschitz_lower := hf.strictGraphLipschitz_lower
  smooth_positive := fun x hx => hf.smooth_future x (subset_closure hx)
  isBounded_region := hf.isBounded_region

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)

/-- Replacing the raw future by its causal envelope changes no region point. -/
theorem region_eq_upperEnvelope : twoFaceRegion h f = twoFaceRegion h hf.upperEnvelope := by
  have hl : hf.lowerEnvelope = fun x => hf.upperEnvelope x - max 0 (h x) := by
    funext x
    linarith [hf.envelope_gap x]
  rw [hf.region_eq_twoGraphRegion, twoFaceRegion_eq_twoGraphRegion, hl]

/-- On an open positive neighborhood the envelope equals the raw C³ germ.
This does not differentiate the clipped envelope at a joint point. -/
theorem smooth_upper_positive (x : JointSpace) (hx : 0 < h x) :
    ContDiffAt ℝ 3 (fun y : JointSpace => hf.upperEnvelope y) x := by
  apply (hf.smooth_future x (subset_closure hx)).congr_of_eventuallyEq
  have hopen : IsOpen {y : JointSpace | 0 < h y} :=
    hf.toRegularHeight.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact hf.upper_eq y (subset_closure hy)

theorem toLongEnvelopeData : LongEnvelopeData h hf.upperEnvelope where
  toRegularHeight := hf.toRegularHeight
  strictGraphLipschitz_upper := hf.strictGraphLipschitz_upper
  strictGraphLipschitz_lower := by
    have he : (fun x => hf.upperEnvelope x - max 0 (h x)) = hf.lowerEnvelope := by
      funext x
      linarith [hf.envelope_gap x]
    rw [he]
    exact hf.strictGraphLipschitz_lower
  smooth_positive := hf.smooth_upper_positive
  isBounded_region := by rw [← hf.region_eq_upperEnvelope]; exact hf.isBounded_region

end AdmissibleIndependentTwoFace

namespace LongEnvelopeData
variable {h f : Spatial → ℝ} (hf : LongEnvelopeData h f)
include hf

/-- Independent constants, their SUM as the thickness bound, and their MINIMUM
causal margin. The thickness constant may exceed one. -/
theorem envelope_bounds : ∃ κ η : ℝ, 0 ≤ κ ∧ 0 ≤ η ∧ κ < 1 ∧ η < 1 ∧
    (∀ x y, |(f x - max 0 (h x)) - (f y - max 0 (h y))| ≤ κ * spatialDistance x y) ∧
    (∀ x y, |f x - f y| ≤ η * spatialDistance x y) ∧
    (∀ x y, |max 0 (h x) - max 0 (h y)| ≤ (κ + η) * spatialDistance x y) := by
  obtain ⟨κ, hκ, hk, hl⟩ := hf.strictGraphLipschitz_lower
  obtain ⟨η, hη, he, hu⟩ := hf.strictGraphLipschitz_upper
  refine ⟨κ, η, hκ, hη, hk, he, hl, hu, fun x y => ?_⟩
  calc
    _ = |(f x - f y) - ((f x - max 0 (h x)) - (f y - max 0 (h y)))| := by congr 1; ring
    _ ≤ |f x - f y| + |(f x - max 0 (h x)) - (f y - max 0 (h y))| := abs_sub _ _
    _ ≤ η * spatialDistance x y + κ * spatialDistance x y := add_le_add (hu x y) (hl x y)
    _ = _ := by ring

omit hf in
/-- E21, including exact contact: each endpoint uses the other face's causal
margin, not one minus a combined thickness/future budget. -/
theorem gap_height_margins {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hl : ∀ x y, |(f x - max 0 (h x)) - (f y - max 0 (h y))| ≤ κ * spatialDistance x y)
    (hu : ∀ x y, |f x - f y| ≤ η * spatialDistance x y)
    (x y : Spatial) (s : ℝ) (hds : spatialDistance x y ≤ s)
    (hg : 0 ≤ twoFaceGap h f x y s) :
    (1 - η) * s ≤ max 0 (h x) ∧ (1 - κ) * s ≤ max 0 (h y) := by
  have hfut := (abs_le.mp (hu y x)).2
  have hpast := (abs_le.mp (hl y x)).2
  rw [spatialDistance_symm y x] at hfut hpast
  have hηd := mul_le_mul_of_nonneg_left hds hη
  have hκd := mul_le_mul_of_nonneg_left hds hκ
  unfold twoFaceGap at hg
  constructor <;> nlinarith

theorem exists_gap_height_margin : ∃ m : ℝ, 0 < m ∧
    ∀ (x y : Spatial) (s : ℝ), spatialDistance x y ≤ s →
      0 ≤ twoFaceGap h f x y s →
      m * s ≤ max 0 (h x) ∧ m * s ≤ max 0 (h y) := by
  obtain ⟨κ, η, hκ, hη, hk, he, hl, hu, _⟩ := hf.envelope_bounds
  refine ⟨min (1 - η) (1 - κ), lt_min (by linarith) (by linarith), ?_⟩
  intro x y s hds hg
  have hs := (spatialDistance_nonneg x y).trans hds
  have hb := gap_height_margins hκ hη hl hu x y s hds hg
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hs).trans hb.1,
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hs).trans hb.2⟩

theorem measurableSet_region : MeasurableSet (twoFaceRegion h f) := by
  rw [twoFaceRegion_eq_twoGraphRegion]
  exact measurableSet_twoGraphRegion hf.strictGraphLipschitz_lower.continuous
    hf.strictGraphLipschitz_upper.continuous

theorem translatedOverlap_eq_gap {s : ℝ} {a : Spatial}
    (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoFaceRegion h f) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (twoFaceGap h f x (x + a) s) := by
  rw [twoFaceRegion_eq_twoGraphRegion]
  rw [translatedOverlap_twoGraph_causal hf.strictGraphLipschitz_lower
    hf.strictGraphLipschitz_upper (by rw [← twoFaceRegion_eq_twoGraphRegion]; exact hf.isBounded_region) hz]
  congr 1
  funext x
  congr 1
  unfold twoFaceGap
  ring

theorem integrableOn_overlap_weight (w : Spacetime → ℝ) (hw : Continuous w) :
    IntegrableOn (fun z => w z * translatedOverlap (twoFaceRegion h f) z) (causalFuture 0) :=
  BoundaryDraft.integrableOn_overlap_weight hf.measurableSet_region hf.isBounded_region w hw

theorem measurable_longOverlapDensity (δ : ℝ) :
    Measurable (longOverlapDensity (twoFaceRegion h f) δ) :=
  BoundaryDraft.measurable_longOverlapDensity hf.measurableSet_region δ

theorem longOverlapDensityENN_lt_top {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) :
    longOverlapDensityENN (twoFaceRegion h f) δ σ < ⊤ :=
  BoundaryDraft.longOverlapDensityENN_lt_top hf.measurableSet_region hf.isBounded_region hδ σ

theorem bounded_longOverlapDensity {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ, |longOverlapDensity (twoFaceRegion h f) δ σ| ≤ C :=
  BoundaryDraft.bounded_longOverlapDensity hf.measurableSet_region hf.isBounded_region hδ

theorem integrable_longOverlapDensity_weight {δ : ℝ} (hδ : 0 < δ)
    (w : ℝ → ℝ) (hw : Continuous w) :
    Integrable (fun σ => w σ * longOverlapDensity (twoFaceRegion h f) δ σ) :=
  BoundaryDraft.integrable_longOverlapDensity_weight hf.measurableSet_region hf.isBounded_region hδ w hw

theorem integral_longOverlap_bdg {δ : ℝ} (hδ : 0 < δ) (ρ : ℝ) :
    (∫ z in longFuture δ, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 z ^ 2) *
      translatedOverlap (twoFaceRegion h f) z) =
      ∫ σ : ℝ, bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) *
        longOverlapDensity (twoFaceRegion h f) δ σ :=
  BoundaryDraft.integral_longOverlap_bdg hf.measurableSet_region hf.isBounded_region hδ ρ

end LongEnvelopeData
end BoundaryDraft
