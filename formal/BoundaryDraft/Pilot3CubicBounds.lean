import BoundaryDraft.Pilot3Contract
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Primitive cubic Taylor bounds in the three-dimensional pilot spacetime

The analytic hypothesis consists of actual value and derivative bounds on a
fixed ball. A C³ germ produces a globally measurable representative of its
absolute Taylor remainder. No overlap jet or action limit is assumed here.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace Pilot3ShortRemainder

abbrev Space := Pilot3Spacetime

/-- Primitive C² bounds, with the same fields as the four-dimensional analytic
interface but in the genuinely three-dimensional pilot spacetime. -/
structure CubicBounds (R : Space → ℝ) (δ T : ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 R (Metric.ball 0 δ)
  nonneg : 0 ≤ T
  value : ∀ z ∈ Metric.ball 0 δ, ‖R z‖ ≤ T * ‖z‖ ^ 3
  first : ∀ z ∈ Metric.ball 0 δ, ‖fderiv ℝ R z‖ ≤ T * ‖z‖ ^ 2
  second : ∀ z ∈ Metric.ball 0 δ, ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ T * ‖z‖

/-- Three mean-value bounds from the actual third derivative on a compact ball. -/
theorem exists_cubicBounds_of_vanishing_jet {R : Space → ℝ}
    (hR : ContDiffAt ℝ 3 R 0) (h₀ : R 0 = 0)
    (h₁ : fderiv ℝ R 0 = 0) (h₂ : fderiv ℝ (fderiv ℝ R) 0 = 0) :
    ∃ δ T : ℝ, 0 < δ ∧ CubicBounds R δ T := by
  letI : NormedAddCommGroup (Space →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] ℝ) := inferInstance
  obtain ⟨ε, hε, hεR⟩ := Metric.mem_nhds_iff.mp (hR.eventually (by norm_num))
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsub : Metric.closedBall (0 : Space) δ ⊆ Metric.ball 0 ε :=
    Metric.closedBall_subset_ball (by dsimp only [δ]; linarith)
  have hs (z : Space) (hz : z ∈ Metric.closedBall 0 δ) : ContDiffAt ℝ 3 R z := hεR (hsub hz)
  have hs' (z : Space) (hz : z ∈ Metric.ball 0 δ) : ContDiffAt ℝ 3 R z :=
    hs z (Metric.ball_subset_closedBall hz)
  have hc : ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ R))) (Metric.closedBall 0 δ) := by
    intro z hz
    exact ((((hs z hz).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Space) δ).exists_bound_of_continuousOn hc
  let T := max 0 K
  have hT : 0 ≤ T := le_max_left _ _
  have hthird (z : Space) (hz : z ∈ Metric.ball 0 δ) :
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ R)) z‖ ≤ T :=
    (hK z (Metric.ball_subset_closedBall hz)).trans (le_max_right _ _)
  have hd₂ (z : Space) (hz : z ∈ Metric.ball 0 δ) :
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ R)) z :=
    (((hs' z hz).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₁ (z : Space) (hz : z ∈ Metric.ball 0 δ) : DifferentiableAt ℝ (fderiv ℝ R) z :=
    ((hs' z hz).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hzero : (0 : Space) ∈ Metric.ball 0 δ := by simpa using hδ
  have hb₂ (z : Space) (hz : z ∈ Metric.ball 0 δ) :
      ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ T * ‖z‖ := by
    simpa only [h₂, sub_zero] using Convex.norm_image_sub_le_of_norm_fderiv_le
      hd₂ hthird (convex_ball (0 : Space) δ) hzero hz
  have hsmall {z y : Space} (hz : z ∈ Metric.ball 0 δ) (hy : y ∈ Metric.closedBall 0 ‖z‖) :
      y ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    exact hy.trans_lt hz
  have hpoint (z : Space) : z ∈ Metric.closedBall (0 : Space) ‖z‖ := by simp
  have hbase (z : Space) : (0 : Space) ∈ Metric.closedBall 0 ‖z‖ := by simp
  have hb₁ (z : Space) (hz : z ∈ Metric.ball 0 δ) : ‖fderiv ℝ R z‖ ≤ T * ‖z‖ ^ 2 := by
    have hb (y : Space) (hy : y ∈ Metric.closedBall 0 ‖z‖) :
        ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ T * ‖z‖ := by
      apply (hb₂ y (hsmall hz hy)).trans
      apply mul_le_mul_of_nonneg_left _ hT
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => hd₁ y (hsmall hz hy)) hb (convex_closedBall (0 : Space) ‖z‖) (hbase z) (hpoint z)
    simpa only [h₁, sub_zero, mul_assoc, ← pow_two] using he
  have hb₀ (z : Space) (hz : z ∈ Metric.ball 0 δ) : ‖R z‖ ≤ T * ‖z‖ ^ 3 := by
    have hb (y : Space) (hy : y ∈ Metric.closedBall 0 ‖z‖) :
        ‖fderiv ℝ R y‖ ≤ T * ‖z‖ ^ 2 := by
      apply (hb₁ y (hsmall hz hy)).trans
      have hn : ‖y‖ ≤ ‖z‖ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      gcongr
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hs' y (hsmall hz hy)).differentiableAt (by norm_num)) hb
        (convex_closedBall (0 : Space) ‖z‖) (hbase z) (hpoint z)
    simpa only [h₀, sub_zero, mul_assoc, ← pow_succ] using he
  refine ⟨δ, T, hδ, ?_⟩
  exact ⟨fun z hz => ((hs' z hz).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).contDiffWithinAt,
    hT, hb₀, hb₁, hb₂⟩

/-- A smaller fixed cutoff preserves all three primitive bounds. -/
theorem CubicBounds.mono {R : Space → ℝ} {δ ε T : ℝ} (h : CubicBounds R δ T) (he : ε ≤ δ) :
    CubicBounds R ε T :=
  ⟨h.smooth.mono (Metric.ball_subset_ball he), h.nonneg,
    fun z hz => h.value z (Metric.ball_subset_ball he hz),
    fun z hz => h.first z (Metric.ball_subset_ball he hz),
    fun z hz => h.second z (Metric.ball_subset_ball he hz)⟩

/-- The measurable representative agrees near zero. No regularity of the
uncontrolled exterior values of the original germ is assumed. -/
theorem exists_measurable_cubicRemainder {R : Space → ℝ}
    (hR : ContDiffAt ℝ 3 R 0) (h₀ : R 0 = 0)
    (h₁ : fderiv ℝ R 0 = 0) (h₂ : fderiv ℝ (fderiv ℝ R) 0 = 0) :
    ∃ (G : Space → ℝ) (δ T : ℝ), Measurable G ∧ 0 < δ ∧ CubicBounds G δ T ∧
      EqOn G R (Metric.ball 0 δ) := by
  obtain ⟨ε, hε, hεR⟩ := Metric.mem_nhds_iff.mp (hR.eventually (by norm_num))
  let b : ContDiffBump (0 : Space) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let G : Space → ℝ := fun z => b z * R z
  have hsupp : tsupport b ⊆ Metric.ball (0 : Space) ε := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp only [b]; linarith)
  have hG : ContDiff ℝ 3 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport b
    · exact b.contDiffAt.mul (hεR (hsupp hz))
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [not_mem_tsupport_iff_eventuallyEq.mp hz] with y hy
      change b y * R y = 0
      simp [hy]
  have hEq : EqOn G R (Metric.ball (0 : Space) (ε / 4)) := by
    intro z hz
    change b z * R z = R z
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_mul]
  have he : G =ᶠ[𝓝 (0 : Space)] R := by
    filter_upwards [Metric.ball_mem_nhds (0 : Space) (by positivity : 0 < ε / 4)] with z hz
    exact hEq hz
  obtain ⟨δ, T, hδ, hB⟩ := exists_cubicBounds_of_vanishing_jet hG.contDiffAt
    (he.eq_of_nhds.trans h₀) (he.fderiv_eq.trans h₁) ((he.fderiv.fderiv_eq).trans h₂)
  refine ⟨G, min δ (ε / 4), T, hG.continuous.measurable, lt_min hδ (by positivity),
    hB.mono (min_le_left _ _), ?_⟩
  exact hEq.mono (Metric.ball_subset_ball (min_le_right _ _))

/-- Equality of actual two-jets produces the required measurable remainder. -/
theorem exists_remainder_of_same_jet {F P : Space → ℝ}
    (hF : ContDiffAt ℝ 3 F 0) (hP : ContDiffAt ℝ 3 P 0)
    (h₀ : F 0 = P 0) (h₁ : fderiv ℝ F 0 = fderiv ℝ P 0)
    (h₂ : fderiv ℝ (fderiv ℝ F) 0 = fderiv ℝ (fderiv ℝ P) 0) :
    ∃ (R : Space → ℝ) (δ T : ℝ), Measurable R ∧ 0 < δ ∧ CubicBounds R δ T ∧
      ∀ z ∈ Metric.ball 0 δ, F z = P z + R z := by
  have hdF := hF.differentiableAt (by norm_num)
  have hdP := hP.differentiableAt (by norm_num)
  have hD₀ : (fun z => F z - P z) 0 = 0 := sub_eq_zero.mpr h₀
  have hD₁ : fderiv ℝ (fun z => F z - P z) 0 = 0 := by
    rw [fderiv_sub hdF hdP, h₁, sub_self]
  have he : fderiv ℝ (fun z => F z - P z) =ᶠ[𝓝 (0 : Space)]
      (fun z => fderiv ℝ F z - fderiv ℝ P z) := by
    filter_upwards [hF.eventually (by norm_num), hP.eventually (by norm_num)] with z hzF hzP
    exact fderiv_sub (hzF.differentiableAt (by norm_num)) (hzP.differentiableAt (by norm_num))
  have hD₂ : fderiv ℝ (fderiv ℝ (fun z => F z - P z)) 0 = 0 := by
    rw [he.fderiv_eq, fderiv_sub
      ((hF.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
      ((hP.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)), h₂, sub_self]
  obtain ⟨R, δ, T, hR, hδ, hB, hEq⟩ := exists_measurable_cubicRemainder (hF.sub hP) hD₀ hD₁ hD₂
  refine ⟨R, δ, T, hR, hδ, hB, ?_⟩
  intro z hz
  have hval := hEq hz
  change R z = F z - P z at hval
  linarith

private theorem hasFDerivAt_half_quadratic
    (B : Space →L[ℝ] Space →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) (z : Space) :
    HasFDerivAt (fun x => (1 / 2 : ℝ) * B x x) (B z) z := by
  have hd := ((B.hasFDerivAt).clm_apply (hasFDerivAt_id z)).const_mul (1 / 2 : ℝ)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, id_eq, smul_eq_mul]
  rw [hB v z]
  ring

/-- Schwarz symmetry follows from regularity, rather than being a premise
about the proposed Taylor polynomial. -/
theorem same_jet_of_taylor_form {F P : Space → ℝ}
    (hF : ContDiffAt ℝ 3 F 0) (h₀ : F 0 = 0)
    (hP : ∀ z, P z = fderiv ℝ F 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ F) 0 z z) :
    F 0 = P 0 ∧ fderiv ℝ F 0 = fderiv ℝ P 0 ∧
      fderiv ℝ (fderiv ℝ F) 0 = fderiv ℝ (fderiv ℝ P) 0 := by
  let L := fderiv ℝ F 0
  let B := fderiv ℝ (fderiv ℝ F) 0
  have hsym : ∀ v w, B v w = B w v :=
    (hF.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)).isSymmSndFDerivAt (by simp [minSmoothness])
  have he : P = fun z => L z + (1 / 2 : ℝ) * B z z := funext hP
  have hd (z : Space) : HasFDerivAt P (L + B z) z := by
    rw [he]
    exact L.hasFDerivAt.add (hasFDerivAt_half_quadratic B hsym z)
  have hD : fderiv ℝ P = fun z => L + B z := funext fun z => (hd z).fderiv
  refine ⟨?_, ?_, ?_⟩
  · simp [he, h₀]
  · rw [hD]
    simp [L]
  · rw [hD]
    have hh := ((hasFDerivAt_const L (0 : Space)).add B.hasFDerivAt).fderiv
    simpa only [zero_add] using hh.symm

/-- Absolute Taylor remainder, retaining the nonzero constant term. -/
theorem exists_absolute_taylor_remainder {F : Space → ℝ} (hF : ContDiffAt ℝ 3 F 0) :
    ∃ (R : Space → ℝ) (δ T : ℝ), Measurable R ∧ 0 < δ ∧ CubicBounds R δ T ∧
      ∀ z ∈ Metric.ball 0 δ,
        F z = F 0 + fderiv ℝ F 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ F) 0 z z + R z := by
  let G : Space → ℝ := fun z => F z - F 0
  have hG : ContDiffAt ℝ 3 G 0 := hF.sub contDiffAt_const
  have hG₀ : G 0 = 0 := sub_self _
  let P : Space → ℝ := fun z => fderiv ℝ G 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ G) 0 z z
  have hP : ContDiff ℝ 3 P :=
    (fderiv ℝ G 0).contDiff.add (contDiff_const.mul
      ((fderiv ℝ (fderiv ℝ G) 0).contDiff.clm_apply contDiff_id))
  obtain ⟨h₀, h₁, h₂⟩ := same_jet_of_taylor_form hG hG₀ (fun _ => rfl : ∀ z, P z = _)
  obtain ⟨R, δ, T, hR, hδ, hB, he⟩ := exists_remainder_of_same_jet hG hP.contDiffAt h₀ h₁ h₂
  have hD : fderiv ℝ G =ᶠ[𝓝 (0 : Space)] fderiv ℝ F :=
    Eventually.of_forall (fun _ => fderiv_sub_const (F 0))
  refine ⟨R, δ, T, hR, hδ, hB, ?_⟩
  intro z hz
  have heq := he z hz
  dsimp only [G, P] at heq
  change F z - F 0 = fderiv ℝ G 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ G) 0 z z + R z at heq
  rw [hD.eq_of_nhds, hD.fderiv_eq] at heq
  linarith

end Pilot3ShortRemainder
end BoundaryDraft
