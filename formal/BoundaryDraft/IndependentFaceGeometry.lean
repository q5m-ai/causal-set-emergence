import BoundaryDraft.IndependentFaceContract

/-!
# Region and strata for independent causal envelopes

The actual raw-germ region is filled using the continuous upper envelope.
Causal convexity uses each independent bound separately, including null pairs.
This supplies the existing finite-density Poisson bridge, not a limit theorem.
-/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

theorem isOpen_region : IsOpen (twoFaceRegion h f) := by
  rw [hf.region_eq_twoGraphRegion]
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  exact (isOpen_lt (hf.strictGraphLipschitz_lower.continuous.comp hs) (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) (hf.strictGraphLipschitz_upper.continuous.comp hs))

theorem measurableSet_region : MeasurableSet (twoFaceRegion h f) :=
  hf.isOpen_region.measurableSet

/-- Every closed ambient causal interval between region points is retained. -/
theorem causallyConvex_region : CausallyConvex (twoFaceRegion h f) := by
  rw [hf.region_eq_twoGraphRegion]
  exact causallyConvex_twoGraphRegion hf.strictGraphLipschitz_lower hf.strictGraphLipschitz_upper

private def fill (q : JointSpace × ℝ) : Spacetime :=
  Fin.cons (hf.upperEnvelope q.1 - (1 - q.2) * max 0 (h q.1)) q.1

private theorem continuous_fill : Continuous hf.fill := by
  have he : Continuous (fun x : JointSpace => (x : Spatial)) := PiLp.continuous_equiv 2 _
  have hh := hf.toRegularHeight.continuous_positivePart.comp he
  have hfc := hf.strictGraphLipschitz_upper.continuous.comp he
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hfc.comp continuous_fst).sub
      ((continuous_const.sub continuous_snd).mul (hh.comp continuous_fst))
  · exact (continuous_apply j).comp (he.comp continuous_fst)

private theorem fill_on_closed (x : JointSpace) (hx : x ∈ graphClosedPositive h) (u : ℝ) :
    hf.fill (x, u) = Fin.cons (f x - (1 - u) * h x) x := by
  simp only [fill, hf.upper_eq x hx,
    max_eq_right (hf.toRegularHeight.nonneg_on_closedPositive x hx)]

private theorem image_fill_open :
    hf.fill '' ({x : JointSpace | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) = twoFaceRegion h f := by
  ext p
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    rw [hf.fill_on_closed x (subset_closure hx)]
    change 0 < h x at hx
    change 0 < u ∧ u < 1 at hu
    simp only [twoFaceRegion, mem_setOf_eq, spatialPart_cons, Fin.cons_zero]
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
    · rw [hf.fill_on_closed ((WithLp.equiv 2 _).symm (spatialPart p))
        (subset_closure (show 0 < h ((WithLp.equiv 2 _).symm (spatialPart p)) from hh))]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change f (spatialPart p) -
          (1 - (1 - (f (spatialPart p) - p 0) / h (spatialPart p))) *
            h (spatialPart p) = p 0
        field_simp
      · rfl

private theorem closure_eq_image_fill :
    closure (twoFaceRegion h f) = hf.fill '' (graphClosedPositive h ×ˢ Icc (0 : ℝ) 1) := by
  have hk := (hf.toRegularHeight.isCompact_closedPositive.prod
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).image hf.continuous_fill
  have he : closure ({x : JointSpace | 0 < h x} ×ˢ Ioo (0 : ℝ) 1) =
      graphClosedPositive h ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rfl
  apply subset_antisymm
  · apply closure_minimal _ hk.isClosed
    rw [← hf.image_fill_open]
    exact image_mono (by rw [← he]; exact subset_closure)
  · rw [← he, ← hf.image_fill_open]
    exact image_closure_subset_closure_image hf.continuous_fill

/-- Closed fibres only over the closed positive region; no exterior zeros are added. -/
theorem mem_closure_region (p : Spacetime) :
    p ∈ closure (twoFaceRegion h f) ↔
      (WithLp.equiv 2 _).symm (spatialPart p) ∈ graphClosedPositive h ∧
      f (spatialPart p) - h (spatialPart p) ≤ p 0 ∧ p 0 ≤ f (spatialPart p) := by
  rw [hf.closure_eq_image_fill]
  constructor
  · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    rw [hf.fill_on_closed x hx]
    have hh := hf.toRegularHeight.nonneg_on_closedPositive x hx
    simp only [spatialPart_cons, Fin.cons_zero]
    refine ⟨hx, ?_, ?_⟩ <;> nlinarith [mul_nonneg hh hu.1, mul_nonneg hh (sub_nonneg.mpr hu.2)]
  · rintro ⟨hx, hl, hu⟩
    have hh := hf.toRegularHeight.nonneg_on_closedPositive _ hx
    by_cases hh0 : h (spatialPart p) = 0
    · refine ⟨⟨(WithLp.equiv 2 _).symm (spatialPart p), 0⟩, ⟨hx, by norm_num⟩, ?_⟩
      rw [hf.fill_on_closed _ hx]
      have ht : f (spatialPart p) = p 0 := by rw [hh0, sub_zero] at hl; exact le_antisymm hl hu
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change f (spatialPart p) - (1 - 0) * h (spatialPart p) = p 0
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
      · rw [hf.fill_on_closed _ hx]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · change f (spatialPart p) -
            (1 - (1 - (f (spatialPart p) - p 0) / h (spatialPart p))) *
              h (spatialPart p) = p 0
          field_simp
        · rfl

theorem isCompact_closure_region : IsCompact (closure (twoFaceRegion h f)) := by
  rw [hf.closure_eq_image_fill]
  exact (hf.toRegularHeight.isCompact_closedPositive.prod isCompact_Icc).image hf.continuous_fill

theorem isBounded_region : Bornology.IsBounded (twoFaceRegion h f) :=
  hf.isCompact_closure_region.isBounded.subset subset_closure

theorem boundedCausalRegion : BoundedCausalRegion (twoFaceRegion h f) :=
  ⟨hf.measurableSet_region, hf.isBounded_region, hf.causallyConvex_region⟩

theorem continuousOn_future : ContinuousOn (fun x : JointSpace => f x) (graphClosedPositive h) :=
  fun x hx => (hf.smooth_future x hx).continuousAt.continuousWithinAt

theorem isCompact_past : IsCompact (twoFacePast h f) :=
  hf.toRegularHeight.isCompact_closedPositive.image_of_continuousOn
    (continuousOn_twoFaceLift (hf.continuousOn_future.sub
      hf.toRegularHeight.continuousOn_closedPositive))

theorem isCompact_future : IsCompact (twoFaceFuture h f) :=
  hf.toRegularHeight.isCompact_closedPositive.image_of_continuousOn
    (continuousOn_twoFaceLift hf.continuousOn_future)

theorem isCompact_joint : IsCompact (twoFaceJoint h f) :=
  hf.toRegularHeight.isCompact_joint.image_of_continuousOn
    (continuousOn_twoFaceLift (hf.continuousOn_future.mono inter_subset_left))

/-- Both closed faces exhaust the frontier, without a lateral wall or hidden seam. -/
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
    · have hh := hf.toRegularHeight.nonneg_on_closedPositive _ hx
      change 0 ≤ h (spatialPart p) at hh
      refine ⟨⟨hx, ht.le, by linarith⟩, ?_⟩
      intro hp
      exact (ne_of_lt hp.1) ht
    · have hh := hf.toRegularHeight.nonneg_on_closedPositive _ hx
      change 0 ≤ h (spatialPart p) at hh
      refine ⟨⟨hx, by linarith, ht.ge⟩, ?_⟩
      intro hp
      exact (ne_of_lt hp.2) ht.symm

omit hf in
/-- Exact stratum intersection reuses the hypothesis-free set identity. -/
theorem past_inter_future : twoFacePast h f ∩ twoFaceFuture h f = twoFaceJoint h f :=
  AdmissibleTwoFace.past_inter_future

/-- Finite-density equality for the existing restricted Poisson law and action.
This is NOT an expected-action convergence theorem. -/
theorem expectedBDGAction_eq {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (twoFaceRegion h f) = continuumMean ρ (twoFaceRegion h f) :=
  hf.boundedCausalRegion.expectedBDGAction_eq hρ

end AdmissibleIndependentTwoFace
end BoundaryDraft
