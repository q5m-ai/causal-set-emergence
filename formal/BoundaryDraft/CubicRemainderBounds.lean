import BoundaryDraft.ShortNullRemainder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Cubic displacement bounds from a vanishing two-jet

Three applications of the mean value inequality give the value, first- and
second-derivative bounds needed by short null cancellation. The constant is a
compact bound on the actual third derivative, not an assumed asymptotic limit.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ShortNullRemainder

/-- A C³ germ with a vanishing two-jet supplies all the required null estimates
on one fixed positive displacement ball. Global measurability is separate. -/
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

/-- Shrinking the fixed displacement neighborhood preserves every primitive
bound. No cutoff depending on density is introduced. -/
theorem CubicBounds.mono {R : Space → ℝ} {δ ε T : ℝ} (h : CubicBounds R δ T) (he : ε ≤ δ) :
    CubicBounds R ε T :=
  ⟨h.smooth.mono (Metric.ball_subset_ball he), h.nonneg,
    fun z hz => h.value z (Metric.ball_subset_ball he hz),
    fun z hz => h.first z (Metric.ball_subset_ball he hz),
    fun z hz => h.second z (Metric.ball_subset_ball he hz)⟩

/-- A local C³ remainder has a measurable representative agreeing on a smaller
fixed neighborhood. Uncontrolled exterior values are never differentiated. -/
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

end ShortNullRemainder
end BoundaryDraft
