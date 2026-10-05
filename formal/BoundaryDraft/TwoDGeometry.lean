import BoundaryDraft.TwoDContract

/-!
# Whole-region 2D geometry and the existing finite-density expectation bridge

These are finite-geometry/finite-density results, not either global limit.
Closed ambient intervals, null partners, all spatial components, and all
regular endpoints are retained. No componentwise action additivity is used.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

theorem twoDRegion_eq_envelopes (h f : TwoDSpace → ℝ) :
    twoDRegion h f = {p | f p.2 - max 0 (h p.2) < p.1 ∧ p.1 < f p.2} := by
  ext p
  by_cases hp : 0 < h p.2
  · simp [twoDRegion, max_eq_right hp.le]
  · have hn := le_of_not_gt hp
    simp only [twoDRegion, mem_setOf_eq, max_eq_left hn, sub_zero]
    constructor <;> intro hc <;> have := hc.1 <;> have := hc.2 <;> linarith

@[simp] theorem twoDRegion_planar (h : TwoDSpace → ℝ) :
    twoDRegion h (fun _ => 0) = dimensionGraphCap h := by
  ext p
  simp [twoDRegion, dimensionGraphCap]

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem height_smoothAt (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    ContDiffAt ℝ ∞ h x := by
  obtain ⟨U, hU, hxU, hs⟩ := hf.smooth_height x hx
  exact hs.contDiffAt (hU.mem_nhds hxU)

theorem future_smoothAt (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨U, hU, hxU, hs⟩ := hf.smooth_future x hx
  exact hs.contDiffAt (hU.mem_nhds hxU)

theorem graphCapData : DimensionGraphCapData h := by
  obtain ⟨κ, η, hκ, hη, hb, hl, _⟩ := hf.slope_budget
  exact ⟨hf.bounded_positive, κ, hκ, by linarith, hl⟩

theorem continuous_positivePart : Continuous (fun x => max 0 (h x)) :=
  hf.graphCapData.continuous_positivePart

theorem continuous_future : Continuous f := by
  obtain ⟨_, η, _, hη, _, _, hl⟩ := hf.slope_budget
  have hL : LipschitzWith ⟨η, hη⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, dist_eq_norm, norm_sub_rev] using hl x y
  exact hL.continuous

theorem isOpen_positive : IsOpen {x | 0 < h x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact (hf.height_smoothAt x (subset_closure hx)).continuousAt.preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hx)

theorem isCompact_closedPositive : IsCompact (twoDClosedPositive h) :=
  hf.bounded_positive.isCompact_closure

theorem joint_eq_frontier : dimensionTwoSpatialJoint h = frontier {x | 0 < h x} := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    change h x = 0 at hz
    exact ⟨hx, fun hi => by have := interior_subset hi; change 0 < h x at this; linarith⟩
  · intro hx
    exact ⟨frontier_subset_closure hx, hf.zero_frontier x hx⟩

/-- All regular endpoints, including inner boundaries of disconnected members. -/
theorem joint_finite : (dimensionTwoSpatialJoint h).Finite :=
  dimensionTwo_joint_finite hf.bounded_positive hf.height_smoothAt
    (fun x hx => hf.regular_zero x hx.1 hx.2)

theorem endpoint_integral (w : TwoDSpace → ℝ) :
    Integrable w (dimensionTwoJointMeasure h) ∧
      (∫ x, w x ∂dimensionTwoJointMeasure h) = ∑ x ∈ hf.joint_finite.toFinset, w x :=
  dimensionTwo_joint_integral hf.bounded_positive hf.height_smoothAt
    (fun x hx => hf.regular_zero x hx.1 hx.2) w

theorem jointMeasure_eq_count :
    dimensionTwoJointMeasure h = Measure.count.restrict (dimensionTwoSpatialJoint h) := by
  have he : dimensionTwoJointMeasure h = dimensionTwoEndpointMeasure hf.joint_finite.toFinset := by
    simp [dimensionTwoJointMeasure, dimensionTwoEndpointMeasure]
  rw [he, dimensionTwoEndpointMeasure_eq_count, Set.Finite.coe_toFinset]

theorem boundaryIntegral_eq_sum :
    twoDBoundaryIntegral h f = ∑ x ∈ hf.joint_finite.toFinset, twoDWeight h f x :=
  (hf.endpoint_integral (twoDWeight h f)).2

theorem isOpen_region : IsOpen (twoDRegion h f) := by
  rw [twoDRegion_eq_envelopes]
  exact (isOpen_lt ((hf.continuous_future.sub hf.continuous_positivePart).comp continuous_snd)
    continuous_fst).inter (isOpen_lt continuous_fst (hf.continuous_future.comp continuous_snd))

theorem measurableSet_region : MeasurableSet (twoDRegion h f) := hf.isOpen_region.measurableSet

/-- The whole CLOSED ambient interval, not just timelike interior points. -/
theorem causallyConvex_region : DimensionCausallyConvex (twoDRegion h f) := by
  obtain ⟨κ, η, hκ, hη, hb, hl, hu⟩ := hf.slope_budget
  rw [twoDRegion_eq_envelopes]
  intro p hp q hq z hz
  have hlow : |(f z.2 - max 0 (h z.2)) - (f p.2 - max 0 (h p.2))| ≤
      (κ + η) * ‖z.2 - p.2‖ := by
    calc
      _ = |(f z.2 - f p.2) - (max 0 (h z.2) - max 0 (h p.2))| := by congr 1; ring
      _ ≤ |f z.2 - f p.2| + |max 0 (h z.2) - max 0 (h p.2)| := abs_sub _ _
      _ ≤ η * ‖z.2 - p.2‖ + κ * ‖z.2 - p.2‖ := by
        simpa only [norm_sub_rev] using add_le_add (hu z.2 p.2) (hl z.2 p.2)
      _ = _ := by ring
  have hzp : ‖z.2 - p.2‖ ≤ z.1 - p.1 := hz.1
  have hqz : ‖q.2 - z.2‖ ≤ q.1 - z.1 := hz.2
  have ht1 : 0 ≤ z.1 - p.1 := (norm_nonneg _).trans hzp
  have ht2 : 0 ≤ q.1 - z.1 := (norm_nonneg _).trans hqz
  have h1 := mul_le_mul_of_nonneg_left hzp (add_nonneg hκ hη)
  have h2 := mul_le_of_le_one_left ht1 hb.le
  have h3 := mul_le_mul_of_nonneg_left hqz hη
  have h4 := mul_le_of_le_one_left ht2 (show η ≤ 1 by linarith)
  have h5 := (abs_le.mp hlow).2
  have h6 := (abs_le.mp (hu z.2 q.2)).1
  exact ⟨by have := hp.1; linarith, by have := hq.2; linarith⟩

/-- A compact filling contains the whole region; no component enumeration. -/
theorem isBounded_region : Bornology.IsBounded (twoDRegion h f) := by
  let F : TwoDSpace × ℝ → TwoDSpacetime :=
    fun q => (f q.1 - (1 - q.2) * max 0 (h q.1), q.1)
  have hc : Continuous F :=
    ((hf.continuous_future.comp continuous_fst).sub
      ((continuous_const.sub continuous_snd).mul
        (hf.continuous_positivePart.comp continuous_fst))).prodMk continuous_fst
  apply ((hf.isCompact_closedPositive.prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).image hc).isBounded.subset
  intro p hp
  have hh : 0 < h p.2 := by have := hp.1; have := hp.2; linarith
  refine ⟨⟨p.2, 1 - (f p.2 - p.1) / h p.2⟩, ⟨subset_closure hh, ?_⟩, ?_⟩
  · constructor
    · have := (div_lt_one hh).mpr (show f p.2 - p.1 < h p.2 by have := hp.1; linarith)
      linarith
    · have := div_pos (sub_pos.mpr hp.2) hh
      linarith
  · refine Prod.ext ?_ rfl
    dsimp only [F]
    rw [max_eq_right hh.le]
    field_simp

/-- Actual hypotheses for #91 and #77 have now been derived. -/
theorem boundedCausalRegion : DimensionBoundedCausalRegion (twoDRegion h f) :=
  ⟨hf.measurableSet_region, hf.isBounded_region, hf.causallyConvex_region⟩

/-- #91's interval volume specialized only AFTER closed interval containment. -/
theorem restricted_interval {x y : TwoDSpacetime} (hx : x ∈ twoDRegion h f)
    (hy : y ∈ twoDRegion h f) (hxy : y ∈ dimensionCausalFuture x) :
    (dimensionRestrictedIntervalVolume (twoDRegion h f) x y).toReal =
      dimensionIntervalSq x y / 2 := by
  have he := (hf.boundedCausalRegion.sprinkling 1 (by norm_num)).restricted_rate
    (by norm_num) hf.causallyConvex_region hx hy hxy
  simpa [dimensionIntervalCoefficient_two, div_eq_mul_inv, mul_comm] using he

/-- Entire signed causal-pair integral is absolutely integrable at fixed density. -/
theorem integrable_bilocal (ρ : ℝ) :
    IntegrableOn (fun p : TwoDSpacetime × TwoDSpacetime =>
      dimensionBilocalKernel 1 (dimensionIntervalCoefficient 2) ρ p.1 p.2)
      {p | p.1 ∈ twoDRegion h f ∧ p.2 ∈ twoDRegion h f ∧
        p.2 ∈ dimensionCausalFuture p.1} := by
  simpa only [one_mul] using integrableOn_dimensionWeighted_bilocal hf.isBounded_region
    (dimensionIntervalCoefficient 2) ρ (fun _ => 1) continuous_const

/-- Only finite density; no deterministic limit is inferred. -/
theorem expectedAction_eq {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionExpectedAction 1 ρ (twoDRegion h f) = twoDAction ρ h f :=
  hf.boundedCausalRegion.expectedAction_eq (by norm_num) hρ

end SmoothTwoD

/-- Conditional transfer, not a proof of either open proposition. -/
theorem twoDExpectedGoal_iff : TwoDExpectedGoal ↔ TwoDDeterministicGoal := by
  constructor
  · intro hg h f hf
    apply (hg h f hf).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact hf.expectedAction_eq hρ
  · intro hg h f hf
    apply (hg h f hf).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact (hf.expectedAction_eq hρ).symm

end BoundaryDraft
