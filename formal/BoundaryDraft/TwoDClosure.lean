import BoundaryDraft.TwoDGeometry

/-! # Complete closed fibres and vertical integration of the 2D region -/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

def twoDPast (h f : TwoDSpace → ℝ) : Set TwoDSpacetime :=
  twoDLift (fun x => f x - h x) '' twoDClosedPositive h

def twoDFuture (h f : TwoDSpace → ℝ) : Set TwoDSpacetime :=
  twoDLift f '' twoDClosedPositive h

theorem mem_twoDLift_image (f : TwoDSpace → ℝ) (s : Set TwoDSpace) (p : TwoDSpacetime) :
    p ∈ twoDLift f '' s ↔ p.2 ∈ s ∧ f p.2 = p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, he⟩
    exact ⟨p.2, hx, Prod.ext he rfl⟩

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

theorem continuousOn_closedPositive : ContinuousOn h (twoDClosedPositive h) :=
  fun x hx => (hf.height_smoothAt x hx).continuousAt.continuousWithinAt

theorem nonneg_on_closedPositive (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) :
    0 ≤ h x := by
  by_cases hp : 0 < h x
  · exact hp.le
  · exact (hf.zero_frontier x ⟨hx, fun hi => hp (show x ∈ {x | 0 < h x} from interior_subset hi)⟩).ge

private def fill (_hf : SmoothTwoD h f) (q : TwoDSpace × ℝ) : TwoDSpacetime :=
  (f q.1 - (1 - q.2) * max 0 (h q.1), q.1)

private theorem continuous_fill : Continuous (hf.fill) :=
  ((hf.continuous_future.comp continuous_fst).sub
    ((continuous_const.sub continuous_snd).mul
      (hf.continuous_positivePart.comp continuous_fst))).prodMk continuous_fst

private theorem fill_on_closed (x : TwoDSpace) (hx : x ∈ twoDClosedPositive h) (u : ℝ) :
    hf.fill (x, u) = (f x - (1 - u) * h x, x) := by
  simp only [fill, max_eq_right (hf.nonneg_on_closedPositive x hx)]

private theorem image_fill_open :
    hf.fill '' ({x | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) = twoDRegion h f := by
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
    closure (twoDRegion h f) = hf.fill '' (twoDClosedPositive h ×ˢ Icc (0 : ℝ) 1) := by
  have hk := (hf.isCompact_closedPositive.prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).image hf.continuous_fill
  have he : closure ({x | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) =
      twoDClosedPositive h ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rfl
  apply subset_antisymm
  · apply closure_minimal _ hk.isClosed
    rw [← hf.image_fill_open]
    exact image_mono (by rw [← he]; exact subset_closure)
  · rw [← he, ← hf.image_fill_open]
    exact image_closure_subset_closure_image hf.continuous_fill

/-- Every closed fibre, including all joint points and no exterior zero sheets. -/
theorem mem_closure_region (p : TwoDSpacetime) :
    p ∈ closure (twoDRegion h f) ↔ p.2 ∈ twoDClosedPositive h ∧
      f p.2 - h p.2 ≤ p.1 ∧ p.1 ≤ f p.2 := by
  rw [hf.closure_eq_image_fill]
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    rw [hf.fill_on_closed x hx]
    have hh := hf.nonneg_on_closedPositive x hx
    refine ⟨hx, ?_, ?_⟩ <;> dsimp only <;>
      nlinarith [mul_nonneg hh hu.1, mul_nonneg hh (sub_nonneg.mpr hu.2)]
  · rintro ⟨hx, hl, hu⟩
    have hh := hf.nonneg_on_closedPositive _ hx
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

theorem isCompact_closure_region : IsCompact (closure (twoDRegion h f)) :=
  hf.isBounded_region.isCompact_closure

theorem isCompact_joint : IsCompact (dimensionTwoSpatialJoint h) := hf.joint_finite.isCompact

theorem frontier_region : frontier (twoDRegion h f) = twoDPast h f ∪ twoDFuture h f := by
  rw [hf.isOpen_region.frontier_eq]
  ext p
  simp only [mem_diff, hf.mem_closure_region, mem_union, twoDPast, twoDFuture,
    mem_twoDLift_image]
  constructor
  · rintro ⟨⟨hx, hl, hu⟩, hn⟩
    by_cases he : f p.2 - h p.2 = p.1
    · exact Or.inl ⟨hx, he⟩
    · right
      refine ⟨hx, le_antisymm ?_ hu⟩
      by_contra ht
      exact hn ⟨lt_of_le_of_ne hl he, lt_of_not_ge ht⟩
  · rintro (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · have hh := hf.nonneg_on_closedPositive _ hx
      exact ⟨⟨hx, ht.le, by linarith⟩, fun hp => (ne_of_lt hp.1) ht⟩
    · have hh := hf.nonneg_on_closedPositive _ hx
      exact ⟨⟨hx, by linarith, ht.ge⟩, fun hp => (ne_of_lt hp.2) ht.symm⟩

omit hf in
theorem past_inter_future : twoDPast h f ∩ twoDFuture h f = twoDJoint h f := by
  ext p
  simp only [mem_inter_iff, twoDPast, twoDFuture, twoDJoint, mem_twoDLift_image,
    dimensionTwoSpatialJoint, twoDClosedPositive, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx, hl⟩, ⟨_, hu⟩⟩
    exact ⟨⟨hx, by linarith⟩, hu⟩
  · rintro ⟨⟨hx, hz⟩, ht⟩
    exact ⟨⟨hx, by simpa [hz] using ht⟩, ⟨hx, ht⟩⟩

/-- Product-volume Fubini over the whole region. -/
theorem integral_region (F : TwoDSpacetime → ℝ) (hF : Continuous F) :
    (∫ p in twoDRegion h f, F p) =
      ∫ x in {x | 0 < h x}, ∫ t in Ioo (f x - h x) (f x), F (t, x) := by
  have hi := (integrable_indicator_iff hf.measurableSet_region).mpr
    ((hF.continuousOn.integrableOn_compact (μ := volume)
      hf.isCompact_closure_region).mono_set subset_closure)
  rw [Measure.volume_eq_prod] at hi
  rw [← integral_indicator hf.measurableSet_region, Measure.volume_eq_prod,
    integral_prod_symm _ hi,
    ← integral_indicator hf.isOpen_positive.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have he (t : ℝ) : (twoDRegion h f).indicator F (t, x) =
        (Ioo (f x - h x) (f x)).indicator (fun t => F (t, x)) t := by
      simp [indicator, twoDRegion]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    by_cases hx : 0 < h x
    · rw [indicator_of_mem (show x ∈ {x | 0 < h x} from hx)]
    · rw [indicator_of_not_mem (show x ∉ {x | 0 < h x} from hx),
        Ioo_eq_empty_of_le (by linarith : f x ≤ f x - h x), setIntegral_empty]

theorem volume_region : (volume (twoDRegion h f)).toReal = ∫ x in {x | 0 < h x}, h x := by
  have he := hf.integral_region (fun _ => 1) continuous_const
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul,
    mul_one, Real.volume_Ioo] at he
  rw [he]
  apply setIntegral_congr_fun hf.isOpen_positive.measurableSet
  intro x hx
  simp only [sub_sub_cancel, ENNReal.toReal_ofReal hx.le]

end SmoothTwoD
end BoundaryDraft
