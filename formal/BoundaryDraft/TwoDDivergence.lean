import BoundaryDraft.TwoDFundamentalTheorem

/-! # Whole-positive-region 1D divergence and the independent 2D endpoint target -/

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 800000

namespace TwoDIntervalFamily
variable {h : TwoDSpace → ℝ} (A : TwoDIntervalFamily h)

private theorem left_injOn : Set.InjOn (fun p : ℝ × ℝ => twoDLine.symm p.1) (A.intervals : Set (ℝ × ℝ)) := by
  intro p hp q hq he
  have hl : p.1 = q.1 := twoDLine.symm.injective he
  by_contra hne
  obtain ⟨s, hs, hs'⟩ := exists_between (lt_min (A.ordered p hp)
    (show p.1 < q.2 by rw [hl]; exact A.ordered q hq))
  exact disjoint_left.mp (A.disjoint hp hq hne)
    ⟨hs, (lt_min_iff.mp hs').1⟩ ⟨by rwa [← hl], (lt_min_iff.mp hs').2⟩

private theorem right_injOn : Set.InjOn (fun p : ℝ × ℝ => twoDLine.symm p.2) (A.intervals : Set (ℝ × ℝ)) := by
  intro p hp q hq he
  have hr : p.2 = q.2 := twoDLine.symm.injective he
  by_contra hne
  obtain ⟨s, hs, hs'⟩ := exists_between (max_lt (A.ordered p hp)
    (show q.1 < p.2 by rw [hr]; exact A.ordered q hq))
  exact disjoint_left.mp (A.disjoint hp hq hne)
    ⟨(max_lt_iff.mp hs).1, hs'⟩ ⟨(max_lt_iff.mp hs).2, by rwa [← hr]⟩

end TwoDIntervalFamily
namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- No endpoint is duplicated or omitted. Regularity rules out a common right
and left endpoint, while interval disjointness rules out duplicate left/right ends. -/
theorem endpoint_sum_eq_intervals (A : TwoDIntervalFamily h) (G : TwoDSpace → ℝ) :
    (∑ x ∈ hf.joint_finite.toFinset, G x) =
      ∑ p ∈ A.intervals, (G (twoDLine.symm p.1) + G (twoDLine.symm p.2)) := by
  classical
  let L := A.intervals.image (fun p => twoDLine.symm p.1)
  let R := A.intervals.image (fun p => twoDLine.symm p.2)
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxR
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hxL
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hxR
    have hl := hf.interval_left_gradient_pos A p hp
    have hr := hf.interval_right_gradient_neg A q hq
    rw [hpx] at hl
    rw [hqx] at hr
    linarith
  have he : L ∪ R = hf.joint_finite.toFinset := by
    ext x
    rw [hf.joint_finite.mem_toFinset, Finset.mem_union]
    constructor
    · rintro (hx | hx)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        exact A.left_mem_joint p hp
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        exact A.right_mem_joint p hp
    · intro hx
      have hi : twoDLine x ∈ twoDLine '' dimensionTwoSpatialJoint h := mem_image_of_mem _ hx
      rw [A.all_endpoints] at hi
      obtain ⟨p, hp, hi⟩ := mem_iUnion₂.mp hi
      rcases hi with hi | hi
      · exact Or.inl (Finset.mem_image.mpr ⟨p, hp, twoDLine.injective
          (by rw [twoDLine.apply_symm_apply]; exact hi.symm)⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨p, hp, twoDLine.injective
          (by rw [twoDLine.apply_symm_apply]; exact (show twoDLine x = p.2 from hi).symm)⟩)
  rw [← he, Finset.sum_union hd]
  dsimp only [L, R]
  rw [Finset.sum_image (fun p hp q hq he => A.left_injOn hp hq he),
    Finset.sum_image (fun p hp q hq he => A.right_injOn hp hq he), Finset.sum_add_distrib]

/-- The complete bulk Hessian integral is an oriented sum over every endpoint.
This is ordinary geometric integration, not bilocal/action additivity. -/
theorem integral_futureHessian_eq_endpoints :
    (∫ x in {x | 0 < h x}, twoDFutureHessian f x) =
      -(∑ x ∈ hf.joint_finite.toFinset,
        twoDGradient h x 0 * twoDGradient f x 0 / |twoDGradient h x 0|) := by
  classical
  obtain ⟨A⟩ := hf.exists_intervalFamily
  have hpre : twoDLine.symm ⁻¹' {x | 0 < h x} = twoDPositiveLine h := by
    ext s
    exact (mem_twoDPositiveLine h s).symm
  have htransport := twoDLine.symm.measurePreserving.setIntegral_preimage_emb
    twoDLine.symm.toHomeomorph.measurableEmbedding (twoDFutureHessian f) {x | 0 < h x}
  rw [hpre, A.positive] at htransport
  have hcont (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
      ContinuousOn (fun s => twoDFutureHessian f (twoDLine.symm s)) (Icc p.1 p.2) := by
    intro s hs
    exact ((hf.continuousAt_futureHessian (A.interval_mem_closedPositive p hp hs)).comp
      twoDLine.symm.continuous.continuousAt).continuousWithinAt
  rw [← htransport, integral_finset_biUnion A.intervals (fun _ _ => measurableSet_Ioo)
    A.disjoint (fun p hp => ((hcont p hp).integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self)]
  have hinterval (p : ℝ × ℝ) (hp : p ∈ A.intervals) :
      (∫ s in Ioo p.1 p.2, twoDFutureHessian f (twoDLine.symm s)) =
        twoDGradient f (twoDLine.symm p.2) 0 - twoDGradient f (twoDLine.symm p.1) 0 := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le (A.ordered p hp).le]
    exact hf.integral_futureHessian_interval A p hp
  rw [hf.endpoint_sum_eq_intervals A, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hinterval p hp, abs_of_pos (hf.interval_left_gradient_pos A p hp),
    abs_of_neg (hf.interval_right_gradient_neg A p hp)]
  field_simp [(hf.interval_left_gradient_pos A p hp).ne', (hf.interval_right_gradient_neg A p hp).ne]
  ring

end SmoothTwoD

/-- Actual time and space coefficients of the TWO-direction absolute polynomial. -/
def twoDShortTimeCoefficient (h : TwoDSpace → ℝ) : ℝ :=
  ∫ x, 1 / ‖twoDGradient h x‖ ∂dimensionTwoJointMeasure h

def twoDShortSpaceCoefficient (h f : TwoDSpace → ℝ) : ℝ :=
  (∫ x in {x | 0 < h x}, twoDFutureHessian f x) +
    ∫ x, (twoDGradient f x 0) ^ 2 / ‖twoDGradient h x‖ ∂dimensionTwoJointMeasure h

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

/-- The difference is the independently normal-defined target. Its definition
has not been replaced by a fitted asymptotic coefficient. -/
theorem short_coefficients_eq_boundaryIntegral :
    twoDShortTimeCoefficient h - twoDShortSpaceCoefficient h f = twoDBoundaryIntegral h f := by
  classical
  rw [twoDShortTimeCoefficient, twoDShortSpaceCoefficient,
    (hf.endpoint_integral _).2, (hf.endpoint_integral _).2,
    hf.integral_futureHessian_eq_endpoints, hf.boundaryIntegral_eq_scalar_sum]
  simp only [twoD_norm_eq]
  rw [sub_add_eq_sub_sub, sub_neg_eq_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end SmoothTwoD
end BoundaryDraft
