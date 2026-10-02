import BoundaryDraft.TwoFaceGeometry

/-!
# Independent causal envelopes (class E)

Only geometric data are admissibility fields. Raw germs are C³ near the compact
closed positive region; the globally strict envelopes need not be smooth at the
joint. There is no combined slope budget, jet, cancellation or limit premise.
The old contracts, region, faces, action and induced-area target are unchanged.
-/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Exactly the independent-envelope class E of `notes/independent-face-extension.md`.
Positive-height critical points and irrelevant exterior raw values are allowed. -/
structure AdmissibleIndependentTwoFace (h f : Spatial → ℝ) : Prop extends RegularHeight h where
  smooth_future : ∀ x ∈ graphClosedPositive h,
    ContDiffAt ℝ 3 (fun y : JointSpace => f y) x
  envelopes : ∃ lower upper : Spatial → ℝ,
    StrictGraphLipschitz lower ∧ StrictGraphLipschitz upper ∧
    (∀ x, upper x - lower x = max 0 (h x)) ∧
    (∀ x : JointSpace, x ∈ graphClosedPositive h → upper x = f x)

/-- Every original member is included, with no stronger hypothesis. -/
theorem AdmissibleTwoFace.toIndependentTwoFace {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) : AdmissibleIndependentTwoFace h f where
  toRegularHeight := hf.toAdmissibleGraphCap.toRegularHeight
  smooth_future := hf.smooth_future
  envelopes := ⟨fun x => f x - max 0 (h x), f,
    hf.strictGraphLipschitz_lower, hf.strictGraphLipschitz_upper,
    fun _ => by ring, fun _ _ => rfl⟩

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- A chosen lower causal envelope, not the raw past germ. -/
def lowerEnvelope : Spatial → ℝ := hf.envelopes.choose

/-- A chosen upper causal envelope, not a globally smooth future germ. -/
def upperEnvelope : Spatial → ℝ := hf.envelopes.choose_spec.choose

theorem strictGraphLipschitz_lower : StrictGraphLipschitz hf.lowerEnvelope :=
  hf.envelopes.choose_spec.choose_spec.1

theorem strictGraphLipschitz_upper : StrictGraphLipschitz hf.upperEnvelope :=
  hf.envelopes.choose_spec.choose_spec.2.1

theorem envelope_gap (x : Spatial) :
    hf.upperEnvelope x - hf.lowerEnvelope x = max 0 (h x) :=
  hf.envelopes.choose_spec.choose_spec.2.2.1 x

theorem upper_eq (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    hf.upperEnvelope x = f x := hf.envelopes.choose_spec.choose_spec.2.2.2 x hx

theorem lower_eq (x : JointSpace) (hx : x ∈ graphClosedPositive h) :
    hf.lowerEnvelope x = f x - h x := by
  have he := hf.envelope_gap x
  rw [hf.upper_eq x hx, max_eq_right (hf.toRegularHeight.nonneg_on_closedPositive x hx)] at he
  linarith

/-- The envelopes coincide off the positive region, even at irrelevant zeros. -/
theorem envelopes_eq_of_nonpos (x : Spatial) (hx : h x ≤ 0) :
    hf.upperEnvelope x = hf.lowerEnvelope x := by
  have he := hf.envelope_gap x
  rw [max_eq_left hx] at he
  exact sub_eq_zero.mp he

/-- Exact equality with the existing independent global-graph region. -/
theorem region_eq_twoGraphRegion :
    twoFaceRegion h f = twoGraphRegion hf.lowerEnvelope hf.upperEnvelope := by
  ext p
  by_cases hx : 0 < h (spatialPart p)
  · have hc : (WithLp.equiv 2 _).symm (spatialPart p) ∈ graphClosedPositive h :=
      subset_closure hx
    have hl : hf.lowerEnvelope (spatialPart p) = f (spatialPart p) - h (spatialPart p) :=
      hf.lower_eq _ hc
    have hu : hf.upperEnvelope (spatialPart p) = f (spatialPart p) := hf.upper_eq _ hc
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hl, hu]
  · have he := hf.envelopes_eq_of_nonpos (spatialPart p) (le_of_not_gt hx)
    constructor
    · intro hp
      exact (hx (by have := hp.1; have := hp.2; linarith)).elim
    · intro hp
      exact (not_lt_of_ge (le_of_eq he) (hp.1.trans hp.2)).elim

/-- Thickness is Lipschitz with the SUM of the two independent constants.
Only a bound below two follows; a bound below one is deliberately not asserted. -/
theorem exists_thickness_bound : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 2 ∧
    ∀ x y, |max 0 (h x) - max 0 (h y)| ≤ κ * spatialDistance x y := by
  obtain ⟨a, ha, ha1, hl⟩ := hf.strictGraphLipschitz_lower
  obtain ⟨b, hb, hb1, hu⟩ := hf.strictGraphLipschitz_upper
  refine ⟨a + b, add_nonneg ha hb, by linarith, fun x y => ?_⟩
  rw [← hf.envelope_gap x, ← hf.envelope_gap y]
  calc
    _ = |(hf.upperEnvelope x - hf.upperEnvelope y) -
        (hf.lowerEnvelope x - hf.lowerEnvelope y)| := by congr 1; ring
    _ ≤ |hf.upperEnvelope x - hf.upperEnvelope y| +
        |hf.lowerEnvelope x - hf.lowerEnvelope y| := abs_sub _ _
    _ ≤ b * spatialDistance x y + a * spatialDistance x y := add_le_add (hu x y) (hl x y)
    _ = (a + b) * spatialDistance x y := by ring

end AdmissibleIndependentTwoFace
end BoundaryDraft
