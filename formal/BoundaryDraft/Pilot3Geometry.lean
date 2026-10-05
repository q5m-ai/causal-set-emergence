import BoundaryDraft.Pilot3RegularHeight

/-!
# The entire smooth 3D region and its closed strata

All components, null/diagonal causal intervals, and interior critical points
are retained. The finite-density expectation theorem is a specialization of
#77's existing law and action, not a new probability definition.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

@[simp] theorem pilot3Lift_snd (f : Pilot3Space → ℝ) (x : Pilot3Space) :
    (pilot3Lift f x).2 = x := rfl

theorem mem_pilot3Lift_image (f : Pilot3Space → ℝ) (s : Set Pilot3Space) (p : Pilot3Spacetime) :
    p ∈ pilot3Lift f '' s ↔ p.2 ∈ s ∧ f p.2 = p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, he⟩
    exact ⟨p.2, hx, Prod.ext he rfl⟩

theorem pilot3Region_eq_envelopes (h f : Pilot3Space → ℝ) :
    pilot3Region h f = {p | f p.2 - max 0 (h p.2) < p.1 ∧ p.1 < f p.2} := by
  ext p
  by_cases hp : 0 < h p.2
  · simp [pilot3Region, max_eq_right hp.le]
  · have hn := le_of_not_gt hp
    simp only [pilot3Region, mem_setOf_eq, max_eq_left hn, sub_zero]
    constructor <;> intro hc <;> have := hc.1 <;> have := hc.2 <;> linarith

@[simp] theorem pilot3Region_planar (h : Pilot3Space → ℝ) :
    pilot3Region h (fun _ => 0) = dimensionGraphCap h := by
  ext p
  simp [pilot3Region, dimensionGraphCap]

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem future_smoothAt (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
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

theorem isOpen_region : IsOpen (pilot3Region h f) := by
  rw [pilot3Region_eq_envelopes]
  exact (isOpen_lt ((hf.continuous_future.sub hf.continuous_positivePart).comp continuous_snd)
    continuous_fst).inter (isOpen_lt continuous_fst (hf.continuous_future.comp continuous_snd))

theorem measurableSet_region : MeasurableSet (pilot3Region h f) := hf.isOpen_region.measurableSet

/-- Complete ambient closed interval containment, including all components. -/
theorem causallyConvex_region : DimensionCausallyConvex (pilot3Region h f) := by
  obtain ⟨κ, η, hκ, hη, hb, hl, hu⟩ := hf.slope_budget
  rw [pilot3Region_eq_envelopes]
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

private def fill (_hf : SmoothPilot3 h f) (q : Pilot3Space × ℝ) : Pilot3Spacetime :=
  (f q.1 - (1 - q.2) * max 0 (h q.1), q.1)

private theorem continuous_fill : Continuous (hf.fill) :=
  ((hf.continuous_future.comp continuous_fst).sub
    ((continuous_const.sub continuous_snd).mul
      (hf.continuous_positivePart.comp continuous_fst))).prodMk continuous_fst

private theorem fill_on_closed (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) (u : ℝ) :
    hf.fill (x, u) = (f x - (1 - u) * h x, x) := by
  simp only [fill, max_eq_right (hf.toPilot3RegularHeight.nonneg_on_closedPositive x hx)]

private theorem image_fill_open :
    hf.fill '' ({x | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) = pilot3Region h f := by
  ext p
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    rw [hf.fill_on_closed x (subset_closure hx)]
    change 0 < h x at hx
    change 0 < u ∧ u < 1 at hu
    change f x - h x < f x - (1 - u) * h x ∧ f x - (1 - u) * h x < f x
    constructor <;> nlinarith [mul_pos hx hu.1, mul_pos hx (sub_pos.mpr hu.2)]
  · intro hp
    have hh : 0 < h p.2 := by have := hp.1; have := hp.2; linarith
    refine ⟨⟨p.2, 1 - (f p.2 - p.1) / h p.2⟩, ⟨hh, ?_⟩, ?_⟩
    · constructor
      · have := (div_lt_one hh).mpr (show f p.2 - p.1 < h p.2 by have := hp.1; linarith)
        linarith
      · have := div_pos (sub_pos.mpr hp.2) hh
        linarith
    · rw [hf.fill_on_closed p.2 (subset_closure hh)]
      refine Prod.ext ?_ rfl
      dsimp only
      field_simp

private theorem closure_eq_image_fill :
    closure (pilot3Region h f) = hf.fill '' (pilot3ClosedPositive h ×ˢ Icc (0 : ℝ) 1) := by
  have hk := (hf.toPilot3RegularHeight.isCompact_closedPositive.prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).image hf.continuous_fill
  have he : closure ({x | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) =
      pilot3ClosedPositive h ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rfl
  apply subset_antisymm
  · apply closure_minimal _ hk.isClosed
    rw [← hf.image_fill_open]
    exact image_mono (by rw [← he]; exact subset_closure)
  · rw [← he, ← hf.image_fill_open]
    exact image_closure_subset_closure_image hf.continuous_fill

/-- Closed fibres only over the closed positive region; no exterior zero sheet. -/
theorem mem_closure_region (p : Pilot3Spacetime) :
    p ∈ closure (pilot3Region h f) ↔ p.2 ∈ pilot3ClosedPositive h ∧
      f p.2 - h p.2 ≤ p.1 ∧ p.1 ≤ f p.2 := by
  rw [hf.closure_eq_image_fill]
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    rw [hf.fill_on_closed x hx]
    have hh := hf.toPilot3RegularHeight.nonneg_on_closedPositive x hx
    refine ⟨hx, ?_, ?_⟩ <;> dsimp only <;>
      nlinarith [mul_nonneg hh hu.1, mul_nonneg hh (sub_nonneg.mpr hu.2)]
  · rintro ⟨hx, hl, hu⟩
    have hh := hf.toPilot3RegularHeight.nonneg_on_closedPositive _ hx
    by_cases hh0 : h p.2 = 0
    · refine ⟨⟨p.2, 0⟩, ⟨hx, by norm_num⟩, ?_⟩
      rw [hf.fill_on_closed _ hx]
      have ht : f p.2 = p.1 := by rw [hh0, sub_zero] at hl; exact le_antisymm hl hu
      exact Prod.ext (by simp [hh0, ht]) rfl
    · have hp : 0 < h p.2 := lt_of_le_of_ne hh (Ne.symm hh0)
      refine ⟨⟨p.2, 1 - (f p.2 - p.1) / h p.2⟩, ⟨hx, ?_⟩, ?_⟩
      · constructor
        · have := (div_le_one hp).mpr (show f p.2 - p.1 ≤ h p.2 by linarith)
          linarith
        · have := div_nonneg (sub_nonneg.mpr hu) hp.le
          linarith
      · rw [hf.fill_on_closed _ hx]
        refine Prod.ext ?_ rfl
        dsimp only
        field_simp

theorem isCompact_closure_region : IsCompact (closure (pilot3Region h f)) := by
  rw [hf.closure_eq_image_fill]
  exact (hf.toPilot3RegularHeight.isCompact_closedPositive.prod isCompact_Icc).image hf.continuous_fill

theorem isBounded_region : Bornology.IsBounded (pilot3Region h f) :=
  hf.isCompact_closure_region.isBounded.subset subset_closure

/-- Constructor for #77's existing finite-density region interface. -/
theorem boundedCausalRegion : DimensionBoundedCausalRegion (pilot3Region h f) :=
  ⟨hf.measurableSet_region, hf.isBounded_region, hf.causallyConvex_region⟩

theorem isCompact_past : IsCompact (pilot3Past h f) :=
  hf.toPilot3RegularHeight.isCompact_closedPositive.image_of_continuousOn
    ((hf.continuous_future.continuousOn.sub
      hf.toPilot3RegularHeight.continuousOn_closedPositive).prodMk continuousOn_id)

theorem isCompact_future : IsCompact (pilot3Future h f) :=
  hf.toPilot3RegularHeight.isCompact_closedPositive.image
    (hf.continuous_future.prodMk continuous_id)

theorem isCompact_joint : IsCompact (pilot3Joint h f) :=
  hf.toPilot3RegularHeight.isCompact_joint.image (hf.continuous_future.prodMk continuous_id)

theorem frontier_region : frontier (pilot3Region h f) = pilot3Past h f ∪ pilot3Future h f := by
  rw [hf.isOpen_region.frontier_eq]
  ext p
  simp only [mem_diff, hf.mem_closure_region, mem_union, pilot3Past, pilot3Future,
    mem_pilot3Lift_image]
  constructor
  · rintro ⟨⟨hx, hl, hu⟩, hn⟩
    by_cases he : f p.2 - h p.2 = p.1
    · exact Or.inl ⟨hx, he⟩
    · right
      refine ⟨hx, le_antisymm ?_ hu⟩
      by_contra ht
      exact hn ⟨lt_of_le_of_ne hl he, lt_of_not_ge ht⟩
  · rintro (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · have hh := hf.toPilot3RegularHeight.nonneg_on_closedPositive _ hx
      exact ⟨⟨hx, ht.le, by linarith⟩, fun hp => (ne_of_lt hp.1) ht⟩
    · have hh := hf.toPilot3RegularHeight.nonneg_on_closedPositive _ hx
      exact ⟨⟨hx, by linarith, ht.ge⟩, fun hp => (ne_of_lt hp.2) ht.symm⟩

omit hf in
theorem past_inter_future : pilot3Past h f ∩ pilot3Future h f = pilot3Joint h f := by
  ext p
  simp only [mem_inter_iff, pilot3Past, pilot3Future, pilot3Joint, mem_pilot3Lift_image,
    pilot3SpatialJoint, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx, hl⟩, ⟨_, hu⟩⟩
    exact ⟨⟨hx, by linarith⟩, hu⟩
  · rintro ⟨⟨hx, hz⟩, ht⟩
    exact ⟨⟨hx, by simpa [hz] using ht⟩, ⟨hx, ht⟩⟩

/-- Specialize the independently proved bridge; the actual law and action
are unchanged, and no asymptotic theorem is used. -/
theorem expectedAction_eq {ρ : ℝ} (hρ : 0 < ρ) :
    dimensionExpectedAction 2 ρ (pilot3Region h f) = pilot3Action ρ h f :=
  hf.boundedCausalRegion.expectedAction_eq (by norm_num) hρ

/-- The full signed pair integrand is absolutely integrable at every fixed
density; partners are the entire causal relation, not one component or chart. -/
theorem integrable_bilocal (ρ : ℝ) :
    IntegrableOn (fun p : Pilot3Spacetime × Pilot3Spacetime =>
      dimensionBilocalKernel 2 (dimensionIntervalCoefficient 3) ρ p.1 p.2)
      {p | p.1 ∈ pilot3Region h f ∧ p.2 ∈ pilot3Region h f ∧
        p.2 ∈ dimensionCausalFuture p.1} := by
  simpa only [one_mul] using integrableOn_dimensionWeighted_bilocal hf.isBounded_region
    (dimensionIntervalCoefficient 3) ρ (fun _ => 1) continuous_const

/-- Product Lebesgue normalization and vertical Fubini on the whole region.
The time endpoints are the original open fibre; no boundary mass is added. -/
theorem integral_region (F : Pilot3Spacetime → ℝ) (hF : Continuous F) :
    (∫ p in pilot3Region h f, F p) =
      ∫ x in {x | 0 < h x}, ∫ t in Ioo (f x - h x) (f x), F (t, x) := by
  have hi := (integrable_indicator_iff hf.measurableSet_region).mpr
    ((hF.continuousOn.integrableOn_compact (μ := volume)
      hf.isCompact_closure_region).mono_set subset_closure)
  rw [Measure.volume_eq_prod] at hi
  rw [← integral_indicator hf.measurableSet_region, Measure.volume_eq_prod,
    integral_prod_symm _ hi,
    ← integral_indicator hf.toPilot3RegularHeight.isOpen_positive.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have he (t : ℝ) : (pilot3Region h f).indicator F (t, x) =
        (Ioo (f x - h x) (f x)).indicator (fun t => F (t, x)) t := by
      simp [indicator, pilot3Region]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    by_cases hx : 0 < h x
    · rw [indicator_of_mem (show x ∈ {x | 0 < h x} from hx)]
    · rw [indicator_of_not_mem (show x ∉ {x | 0 < h x} from hx),
        Ioo_eq_empty_of_le (by linarith : f x ≤ f x - h x), setIntegral_empty]

theorem volume_region : (volume (pilot3Region h f)).toReal = ∫ x in {x | 0 < h x}, h x := by
  have he := hf.integral_region (fun _ => 1) continuous_const
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul,
    mul_one, Real.volume_Ioo] at he
  rw [he]
  apply setIntegral_congr_fun hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  intro x hx
  simp only [sub_sub_cancel, ENNReal.toReal_ofReal hx.le]

end SmoothPilot3

/-- Conditional transfer only: this equivalence does not by itself establish
either limit. It is derived from the positive-density bridge; the unconditional
proofs are separate in `Pilot3Limit`. -/
theorem pilot3ExpectedGoal_iff : Pilot3ExpectedGoal ↔ Pilot3DeterministicGoal := by
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
