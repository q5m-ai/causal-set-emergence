import BoundaryDraft.TwoFaceContract
import BoundaryDraft.GraphOverlap

/-!
# Geometry of the unchanged two-face region

The causal envelopes, not the raw past germ, supply ambient causal convexity.
A continuous filling of the compact closed positive region proves the closure
and its complete frontier, including zero-height fibres. No regularity outside
that closed positive region is required of the raw height.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- The lower envelope uses the combined Euclidean slope budget. -/
theorem AdmissibleTwoFace.strictGraphLipschitz_lower {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) : StrictGraphLipschitz (fun x => f x - max 0 (h x)) := by
  obtain ⟨κ, η, hκ, hη, hk, hh, hfl⟩ := hf.slope_budget
  refine ⟨η + κ, add_nonneg hη hκ, by linarith, fun x y => ?_⟩
  calc
    _ = |(f x - f y) - (max 0 (h x) - max 0 (h y))| := by congr 1; ring
    _ ≤ |f x - f y| + |max 0 (h x) - max 0 (h y)| := abs_sub _ _
    _ ≤ η * spatialDistance x y + κ * spatialDistance x y := add_le_add (hfl x y) (hh x y)
    _ = (η + κ) * spatialDistance x y := by ring

theorem AdmissibleTwoFace.strictGraphLipschitz_upper {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) : StrictGraphLipschitz f := by
  obtain ⟨κ, η, hκ, hη, hk, _, hfl⟩ := hf.slope_budget
  exact ⟨η, hη, by linarith, hfl⟩

/-- Exact compatibility with the independent two-global-graph API. -/
theorem twoFaceRegion_eq_twoGraphRegion (h f : Spatial → ℝ) :
    twoFaceRegion h f = twoGraphRegion (fun x => f x - max 0 (h x)) f :=
  twoFaceRegion_eq_envelopes h f

/-- A strict graph epigraph is a future set in ambient Minkowski space,
including null relations and the vertex. -/
theorem StrictGraphLipschitz.epigraph_future {f : Spatial → ℝ}
    (hf : StrictGraphLipschitz f) {x y : Spacetime}
    (hx : f (spatialPart x) < x 0) (hxy : y ∈ causalFuture x) :
    f (spatialPart y) < y 0 := by
  obtain ⟨κ, hκ, hk, hl⟩ := hf
  have hd := spatialDistance_le_of_causalFuture x y hxy
  have he := (abs_le.mp (hl (spatialPart x) (spatialPart y))).1
  have hb := (mul_le_mul_of_nonneg_left hd hκ).trans
    (mul_le_of_le_one_left (sub_nonneg.mpr hxy.1) hk.le)
  linarith

/-- Dually, the strict hypograph is a past set. -/
theorem StrictGraphLipschitz.hypograph_past {f : Spatial → ℝ}
    (hf : StrictGraphLipschitz f) {x y : Spacetime}
    (hy : y 0 < f (spatialPart y)) (hxy : y ∈ causalFuture x) :
    x 0 < f (spatialPart x) := by
  obtain ⟨κ, hκ, hk, hl⟩ := hf
  have hd := spatialDistance_le_of_causalFuture x y hxy
  have he := (abs_le.mp (hl (spatialPart x) (spatialPart y))).1
  have hb := (mul_le_mul_of_nonneg_left hd hκ).trans
    (mul_le_of_le_one_left (sub_nonneg.mpr hxy.1) hk.le)
  linarith

theorem causallyConvex_twoGraphRegion {lower upper : Spatial → ℝ}
    (hl : StrictGraphLipschitz lower) (hu : StrictGraphLipschitz upper) :
    CausallyConvex (twoGraphRegion lower upper) := by
  intro x hx z hz y hy
  exact ⟨hl.epigraph_future hx.1 hy.1, hu.hypograph_past hz.2 hy.2⟩

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem isOpen_region : IsOpen (twoFaceRegion h f) := by
  rw [twoFaceRegion_eq_envelopes]
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  exact (isOpen_lt (hf.strictGraphLipschitz_lower.continuous.comp hs) (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) (hf.strictGraphLipschitz_upper.continuous.comp hs))

theorem measurableSet_region : MeasurableSet (twoFaceRegion h f) :=
  hf.isOpen_region.measurableSet

theorem causallyConvex_region : CausallyConvex (twoFaceRegion h f) := by
  rw [twoFaceRegion_eq_twoGraphRegion]
  exact causallyConvex_twoGraphRegion hf.strictGraphLipschitz_lower hf.strictGraphLipschitz_upper

private def fill (h f : Spatial → ℝ) (q : JointSpace × ℝ) : Spacetime :=
  Fin.cons (f q.1 - (1 - q.2) * max 0 (h q.1)) q.1

private theorem continuous_fill : Continuous (fill h f) := by
  have he : Continuous (fun x : JointSpace => (x : Spatial)) := PiLp.continuous_equiv 2 _
  have hh := hf.toGraphCapData.continuous_positivePart.comp he
  have hfc := hf.strictGraphLipschitz_upper.continuous.comp he
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hfc.comp continuous_fst).sub
      ((continuous_const.sub continuous_snd).mul (hh.comp continuous_fst))
  · exact (continuous_apply j).comp (he.comp continuous_fst)

omit hf in
private theorem image_fill_open :
    fill h f '' ({x : JointSpace | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) = twoFaceRegion h f := by
  ext p
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    change 0 < h x at hx
    change 0 < u ∧ u < 1 at hu
    simp only [twoFaceRegion, mem_setOf_eq, fill, spatialPart_cons, Fin.cons_zero,
      max_eq_right hx.le]
    constructor <;> nlinarith [mul_pos hx hu.1, mul_pos hx (sub_pos.mpr hu.2)]
  · intro hp
    have hh : 0 < h (spatialPart p) := by have := hp.1; have := hp.2; linarith
    refine ⟨⟨(WithLp.equiv 2 _).symm (spatialPart p),
      1 - (f (spatialPart p) - p 0) / h (spatialPart p)⟩, ⟨hh, ?_⟩, ?_⟩
    · constructor
      · have := (div_lt_one hh).mpr (show f (spatialPart p) - p 0 < h (spatialPart p) by
          have := hp.1; linarith)
        linarith
      · have := div_pos (sub_pos.mpr hp.2) hh
        linarith
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change f (spatialPart p) -
          (1 - (1 - (f (spatialPart p) - p 0) / h (spatialPart p))) *
            max 0 (h (spatialPart p)) = p 0
        rw [max_eq_right hh.le]
        field_simp
      · rfl

private theorem closure_eq_image_fill :
    closure (twoFaceRegion h f) = fill h f '' (graphClosedPositive h ×ˢ Icc (0 : ℝ) 1) := by
  have hk := (hf.toGraphCapData.isCompact_closedPositive.prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).image hf.continuous_fill
  have he : closure ({x : JointSpace | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) =
      graphClosedPositive h ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rfl
  apply subset_antisymm
  · apply closure_minimal _ hk.isClosed
    rw [← image_fill_open]
    exact image_mono (by rw [← he]; exact subset_closure)
  · rw [← he, ← image_fill_open]
    exact image_closure_subset_closure_image hf.continuous_fill

/-- The actual closure has no lateral wall or exterior zero fibre. -/
theorem mem_closure_region (p : Spacetime) :
    p ∈ closure (twoFaceRegion h f) ↔
      (WithLp.equiv 2 _).symm (spatialPart p) ∈ graphClosedPositive h ∧
      f (spatialPart p) - h (spatialPart p) ≤ p 0 ∧ p 0 ≤ f (spatialPart p) := by
  rw [hf.closure_eq_image_fill]
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    have hh := hf.toAdmissibleGraphCap.nonneg_on_closedPositive x hx
    simp only [fill, spatialPart_cons, Fin.cons_zero, max_eq_right hh]
    refine ⟨hx, ?_, ?_⟩ <;> nlinarith [mul_nonneg hh hu.1, mul_nonneg hh (sub_nonneg.mpr hu.2)]
  · rintro ⟨hx, hl, hu⟩
    have hh := hf.toAdmissibleGraphCap.nonneg_on_closedPositive _ hx
    by_cases hh0 : h (spatialPart p) = 0
    · refine ⟨⟨(WithLp.equiv 2 _).symm (spatialPart p), 0⟩, ⟨hx, by norm_num⟩, ?_⟩
      have ht : f (spatialPart p) = p 0 := by rw [hh0, sub_zero] at hl; exact le_antisymm hl hu
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change f (spatialPart p) - (1 - 0) * max 0 (h (spatialPart p)) = p 0
        simp [hh0, ht]
      · rfl
    · have hp : 0 < h (spatialPart p) := lt_of_le_of_ne hh (Ne.symm hh0)
      refine ⟨⟨(WithLp.equiv 2 _).symm (spatialPart p),
        1 - (f (spatialPart p) - p 0) / h (spatialPart p)⟩, ⟨hx, ?_⟩, ?_⟩
      · constructor
        · have := (div_le_one hp).mpr (show f (spatialPart p) - p 0 ≤ h (spatialPart p) by linarith)
          linarith
        · have := div_nonneg (sub_nonneg.mpr hu) hp.le
          linarith
      · ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · change f (spatialPart p) -
            (1 - (1 - (f (spatialPart p) - p 0) / h (spatialPart p))) *
              max 0 (h (spatialPart p)) = p 0
          rw [max_eq_right hp.le]
          field_simp
        · rfl

theorem isCompact_closure_region : IsCompact (closure (twoFaceRegion h f)) := by
  rw [hf.closure_eq_image_fill]
  exact (hf.toGraphCapData.isCompact_closedPositive.prod isCompact_Icc).image hf.continuous_fill

theorem isBounded_region : Bornology.IsBounded (twoFaceRegion h f) :=
  hf.isCompact_closure_region.isBounded.subset subset_closure

/-- All inputs of the existing expectation bridge are now derived geometry. -/
theorem boundedCausalRegion : BoundedCausalRegion (twoFaceRegion h f) :=
  ⟨hf.measurableSet_region, hf.isBounded_region, hf.causallyConvex_region⟩

end AdmissibleTwoFace

/-- Membership of a graph image retains its actual spatial base set. -/
theorem mem_twoFaceLift_image (g : Spatial → ℝ) (s : Set JointSpace) (p : Spacetime) :
    p ∈ twoFaceLift g '' s ↔
      (WithLp.equiv 2 _).symm (spatialPart p) ∈ s ∧ g (spatialPart p) = p 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, ht⟩
    refine ⟨(WithLp.equiv 2 _).symm (spatialPart p), hx, ?_⟩
    ext i
    exact Fin.cases ht (fun _ => rfl) i

theorem continuousOn_twoFaceLift {g : Spatial → ℝ} {s : Set JointSpace}
    (hg : ContinuousOn (fun x : JointSpace => g x) s) : ContinuousOn (twoFaceLift g) s := by
  apply continuousOn_pi.mpr
  intro i
  refine Fin.cases hg (fun j => ?_) i
  exact ((continuous_apply j).comp (PiLp.continuous_equiv 2 _)).continuousOn

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

theorem continuousOn_future : ContinuousOn (fun x : JointSpace => f x) (graphClosedPositive h) :=
  fun x hx => (hf.smooth_future x hx).continuousAt.continuousWithinAt

theorem isCompact_past : IsCompact (twoFacePast h f) :=
  hf.toGraphCapData.isCompact_closedPositive.image_of_continuousOn
    (continuousOn_twoFaceLift (hf.continuousOn_future.sub
      hf.toAdmissibleGraphCap.continuousOn_closedPositive))

theorem isCompact_future : IsCompact (twoFaceFuture h f) :=
  hf.toGraphCapData.isCompact_closedPositive.image_of_continuousOn
    (continuousOn_twoFaceLift hf.continuousOn_future)

theorem isCompact_joint : IsCompact (twoFaceJoint h f) :=
  hf.toAdmissibleGraphCap.isCompact_joint.image_of_continuousOn
    (continuousOn_twoFaceLift (hf.continuousOn_future.mono inter_subset_left))

/-- Both closed faces exhaust the topological frontier; no lateral boundary
or graph above an irrelevant exterior zero is inserted. -/
theorem frontier_region :
    frontier (twoFaceRegion h f) = twoFacePast h f ∪ twoFaceFuture h f := by
  rw [hf.isOpen_region.frontier_eq]
  ext p
  simp only [mem_diff, hf.mem_closure_region, mem_union, twoFacePast, twoFaceFuture,
    mem_twoFaceLift_image]
  constructor
  · rintro ⟨⟨hx, hl, hu⟩, hn⟩
    by_cases he : f (spatialPart p) - h (spatialPart p) = p 0
    · exact Or.inl ⟨hx, he⟩
    · right
      refine ⟨hx, le_antisymm ?_ hu⟩
      by_contra ht
      exact hn ⟨lt_of_le_of_ne hl he, lt_of_not_ge ht⟩
  · rintro (⟨hx, ht⟩ | ⟨hx, ht⟩)
    · have hh := hf.toAdmissibleGraphCap.nonneg_on_closedPositive _ hx
      change 0 ≤ h (spatialPart p) at hh
      refine ⟨⟨hx, ht.le, by linarith⟩, ?_⟩
      intro hp
      exact (ne_of_lt hp.1) ht
    · have hh := hf.toAdmissibleGraphCap.nonneg_on_closedPositive _ hx
      change 0 ≤ h (spatialPart p) at hh
      refine ⟨⟨hx, by linarith, ht.ge⟩, ?_⟩
      intro hp
      exact (ne_of_lt hp.2) ht.symm

omit hf in
/-- The face intersection is the declared joint, not the full raw zero set. -/
theorem past_inter_future : twoFacePast h f ∩ twoFaceFuture h f = twoFaceJoint h f := by
  ext p
  simp only [mem_inter_iff, twoFacePast, twoFaceFuture, twoFaceJoint, mem_twoFaceLift_image,
    graphJoint, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx, hl⟩, ⟨_, hu⟩⟩
    refine ⟨⟨hx, ?_⟩, hu⟩
    change h (spatialPart p) = 0
    linarith
  · rintro ⟨⟨hx, hh⟩, ht⟩
    change h (spatialPart p) = 0 at hh
    exact ⟨⟨hx, by simpa only [hh, sub_zero] using ht⟩, hx, ht⟩

end AdmissibleTwoFace

/-- Proof term for the original, unchanged region/stratum contract. -/
theorem twoFaceRegionGoal : TwoFaceRegionGoal := by
  intro h f hf
  exact ⟨hf.isOpen_region, hf.boundedCausalRegion, hf.isCompact_past, hf.isCompact_future,
    hf.isCompact_joint, hf.frontier_region, AdmissibleTwoFace.past_inter_future⟩

end BoundaryDraft
