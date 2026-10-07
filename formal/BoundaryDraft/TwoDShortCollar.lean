import BoundaryDraft.TwoDCollarMeasure

/-!
# Complete actual endpoint-collar extension in physical dimension two

Every canonical endpoint is included. Disjoint physical collars localize only
the correction; the original bulk and its causal partners are not split into
componentwise actions. The complement has a proved positive height margin.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft
set_option maxHeartbeats 1000000

private theorem finite_separation {ι : Type} [Fintype ι] (x : ι → TwoDSpace)
    (hi : Function.Injective x) : ∃ R : ℝ, 0 < R ∧ ∀ i j, i ≠ j → 2 * R < dist (x i) (x j) := by
  have ht : ∀ᶠ R : ℝ in 𝓝 (0 : ℝ), ∀ i j, i ≠ j → 2 * R < dist (x i) (x j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ hn => False.elim (hn hij)
    · have hd : 0 < dist (x i) (x j) := dist_pos.mpr (hi.ne hij)
      filter_upwards [gt_mem_nhds (div_pos hd (by norm_num : (0 : ℝ) < 2))] with R hR _
      linarith
  exact ((show ∀ᶠ R : ℝ in 𝓝[>] 0, 0 < R from self_mem_nhdsWithin).and
    (nhdsWithin_le_nhds ht)).exists

namespace SmoothTwoD
variable {h f : TwoDSpace → ℝ} (hf : SmoothTwoD h f)
include hf

private theorem endpoint_integral_subtype [Fintype (dimensionTwoSpatialJoint h)] (G : TwoDSpace → ℝ) :
    (∫ x, G x ∂dimensionTwoJointMeasure h) = ∑ x : dimensionTwoSpatialJoint h, G x := by
  rw [(hf.endpoint_integral G).2]
  exact Finset.sum_subtype _ (fun x => hf.joint_finite.mem_toFinset) G

/-- The complete C³ correction and canonical endpoint Hessian are PRODUCED
from `SmoothTwoD`. None of these analytic conclusions is an admissibility field. -/
theorem exists_shortCollar_twoJet :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : TwoDSpacetime → ℝ,
      ContDiffAt ℝ 3 V 0 ∧ V 0 = 0 ∧ fderiv ℝ V 0 = 0 ∧
      (∀ v w : TwoDSpacetime, fderiv ℝ (fderiv ℝ V) 0 v w =
        ∫ x, (twoDShortGapLinear f x v * twoDShortGapLinear f x w) / ‖twoDGradient h x‖
          ∂dimensionTwoJointMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : TwoDSpacetime) δ, ‖z.2‖ ≤ z.1 →
        V z = twoDShortCollarCorrection h f z := by
  classical
  let J := dimensionTwoSpatialJoint h
  letI : Fintype J := hf.joint_finite.fintype
  obtain ⟨R, hR, hsep⟩ := finite_separation (fun x : J => x.val) Subtype.val_injective
  choose η hη₀ hη hr hu hC hC₀ hC₁ hC₂ using
    (fun x : J => hf.exists_movingEndpoint_twoJet x.val x.property)
  choose B d hB hBR hd hsign hcorr using
    (fun x : J => hf.exists_endpointCollar x.val x.property R hR (η x) (hη₀ x)
      (hη x).continuousAt (hr x) (hu x))
  let S : Set TwoDSpace := ⋃ x : J, Metric.ball x.val (B x)
  have hS : IsOpen S := isOpen_iUnion fun _ => Metric.isOpen_ball
  have hdis : Pairwise (fun x y : J => Disjoint (twoDPositiveCollar h x.val (B x))
      (twoDPositiveCollar h y.val (B y))) := by
    intro x y hxy
    apply disjoint_left.mpr
    intro p hpx hpy
    have hpX : dist p x.val < B x := hpx.1
    have hpY : dist p y.val < B y := hpy.1
    have ht := dist_triangle x.val p y.val
    rw [dist_comm x.val p] at ht
    have hs := hsep x y hxy
    linarith [hBR x, hBR y]
  let K := twoDClosedPositive h \ S
  have hK : IsCompact K := hf.isCompact_closedPositive.diff hS
  have hpos (y : TwoDSpace) (hy : y ∈ K) : 0 < h y := by
    have hn := hf.nonneg_on_closedPositive y hy.1
    by_cases hz : h y = 0
    · have hj : y ∈ J := ⟨hy.1, hz⟩
      exact False.elim (hy.2 (mem_iUnion.mpr ⟨⟨y, hj⟩, Metric.mem_ball_self (hB ⟨y, hj⟩)⟩))
    · exact lt_of_le_of_ne hn (Ne.symm hz)
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ y ∈ K, m ≤ h y := by
    by_cases hne : K.Nonempty
    · obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hne (hf.continuousOn_closedPositive.mono diff_subset)
      exact ⟨h y, hpos y hy, fun t ht => hmin ht⟩
    · exact ⟨1, zero_lt_one, fun y hy => False.elim (hne ⟨y, hy⟩)⟩
  obtain ⟨m, hm, hmin⟩ := hm
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < m / 4 ∧ ∀ x : J, δ < d x :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds ((gt_mem_nhds (div_pos hm (by norm_num))).and
        (eventually_all.mpr fun x => gt_mem_nhds (hd x))))
  obtain ⟨δ, hδ, hδm, hδd⟩ := hsmall.exists
  let C : J → TwoDSpacetime → ℝ := fun x => twoDEndpointCorrection h f x.val (η x)
  let V : TwoDSpacetime → ℝ := fun z => ∑ x : J, C x z
  have hV : ContDiffAt ℝ 3 V 0 := ContDiffAt.sum (fun x _ => hC x)
  have hVeq (z : TwoDSpacetime) (hz : z ∈ Metric.ball (0 : TwoDSpacetime) δ)
      (hc : ‖z.2‖ ≤ z.1) : V z = twoDShortCollarCorrection h f z := by
    let F : TwoDSpace → ℝ := fun y => max 0 (twoDShortGap f z y - h y)
    have hFi : IntegrableOn F {y | 0 < h y} :=
      ((continuousOn_const.sup ((hf.continuous_shortGap z).continuousOn.sub
        hf.continuousOn_closedPositive)).integrableOn_compact hf.isCompact_closedPositive).mono_set subset_closure
    have hzero : (∫ y in {y | 0 < h y} \ S, F y) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      have hyK : y ∈ K := ⟨subset_closure hy.1, hy.2⟩
      have hb := hmin y hyK
      have hzn : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      exact hf.shortCollar_integrand_eq_zero z y (by linarith)
    have hUS : {y | 0 < h y} ∩ S = ⋃ x : J, twoDPositiveCollar h x.val (B x) := by
      ext y
      simp only [S, twoDPositiveCollar, mem_inter_iff, mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨hy, x, hx⟩
        exact ⟨x, hx, hy⟩
      · rintro ⟨x, hx, hy⟩
        exact ⟨hy, x, hx⟩
    have hsum : (∫ y in ⋃ x : J, twoDPositiveCollar h x.val (B x), F y) =
        ∑ x : J, ∫ y in twoDPositiveCollar h x.val (B x), F y :=
      integral_fintype_iUnion (f := F) (μ := volume)
        (fun x : J => hf.measurableSet_positiveCollar x.val (B x)) hdis
        (fun x : J => hFi.mono_set (show twoDPositiveCollar h x.val (B x) ⊆ {y | 0 < h y} from inter_subset_right))
    have hp := integral_inter_add_diff hS.measurableSet hFi
    rw [hzero, add_zero, hUS, hsum] at hp
    change V z = ∫ y in {y | 0 < h y}, F y
    rw [← hp]
    apply Finset.sum_congr rfl
    intro x _
    rw [hf.integral_positiveCollar x.val x.property (hB x) (hsign x) F]
    exact (hcorr x z ((Metric.ball_subset_ball (hδd x).le) hz) hc).symm
  refine ⟨δ, hδ, V, hV, ?_, ?_, ?_, hVeq⟩
  · exact Finset.sum_eq_zero (fun x _ => hC₀ x)
  · rw [show V = (fun z => ∑ x : J, C x z) from rfl,
      fderiv_sum (fun x _ => (hC x).differentiableAt (by norm_num))]
    exact Finset.sum_eq_zero (fun x _ => hC₁ x)
  · intro v w
    have he : fderiv ℝ V =ᶠ[𝓝 (0 : TwoDSpacetime)] (fun z => ∑ x : J, fderiv ℝ (C x) z) := by
      filter_upwards [eventually_all.mpr (fun x => (hC x).eventually (by simp))] with z hz
      exact fderiv_sum (fun x _ => (hz x).differentiableAt (by norm_num))
    rw [he.fderiv_eq, fderiv_sum (fun x _ =>
      ((hC x).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.sum_apply]
    rw [hf.endpoint_integral_subtype]
    exact Finset.sum_congr rfl (fun x _ => hC₂ x v w)

end SmoothTwoD
end BoundaryDraft
