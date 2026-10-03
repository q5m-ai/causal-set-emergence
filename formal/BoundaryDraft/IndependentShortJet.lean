import BoundaryDraft.IndependentShortCollar
import BoundaryDraft.ShortTaylorRemainder
import BoundaryDraft.TwoFaceShortReduction

/-!
# Absolute class-E overlap jet and derivative-controlled remainder

The actual future-cone overlap is extended near zero using the unweighted
fixed interior and the complete regular-height collar. Its volume and linear
slice terms are retained. This file produces primitive remainder bounds; it
does not identify the sphere-averaged density or assert an action limit.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- The constant term of the absolute overlap is the original spacetime
point volume, not a polynomial model parameter. -/
theorem volume_region_eq_height : volume.real (twoFaceRegion h f) =
    ∫ x : JointSpace in {x : JointSpace | 0 < h x}, h x := by
  obtain ⟨ε, κ, N⟩ := hf.exists_rawFaceNeighborhood
  have he := hf.translatedOverlap_eq_shortGap N
    (z := 0) (by simpa using N.radius_pos.le) (by simp)
  have hz : displacementSpacetime 0 = (0 : Spacetime) := by ext i; fin_cases i <;> rfl
  rw [hz, translatedOverlap_at_zero hf.measurableSet_region] at he
  rw [he]
  apply setIntegral_congr_fun
    (hf.toRegularHeight.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  intro x hx
  simp only [shortOverlapGap_zero, sub_zero, max_eq_right (show 0 ≤ h x from hx.le)]

/-- The time-linear moving slice is explicit before Taylor expansion. -/
theorem translatedOverlap_eq_absolute_bulk {ε κ : ℝ} (N : RawFaceNeighborhood h f ε κ)
    {z : Displacement} (hz : ‖z.2‖ ≤ ε) (hc : ‖z.2‖ ≤ z.1) :
    translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) =
      volume.real (twoFaceRegion h f) - z.1 * volume.real {x : JointSpace | 0 < h x} +
        shortOverlapBulk h f z + shortOverlapCollarCorrection h f z := by
  have hi : IntegrableOn (fun _ : JointSpace => z.1) {x : JointSpace | 0 < h x} :=
    (continuous_const.continuousOn.integrableOn_compact hf.toRegularHeight.isCompact_closedPositive).mono_set
      subset_closure
  have hq := hf.integrableOn_shortOverlapGap N hz
  have he : shortOverlapBulk h f z = z.1 * volume.real {x : JointSpace | 0 < h x} -
      ∫ x : JointSpace in {x : JointSpace | 0 < h x}, shortOverlapGap f z x := by
    calc
      _ = ∫ x : JointSpace in {x : JointSpace | 0 < h x}, z.1 - shortOverlapGap f z x := by
        apply integral_congr_ae
        filter_upwards with x
        unfold shortOverlapGap
        ring
      _ = _ := by rw [integral_sub hi hq]; simp [mul_comm]
  rw [hf.translatedOverlap_eq_fixed_sub_gap_add_collar N hz hc, ← hf.volume_region_eq_height, he]
  ring

set_option maxHeartbeats 800000 in
/-- The COMPLETE absolute two-jet: point volume, moving interior slice, true
future Hessian and canonical joint square. It is derived from geometry alone. -/
theorem exists_absoluteOverlap_twoJet :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Displacement → ℝ,
      ContDiffAt ℝ 3 F 0 ∧ F 0 = volume.real (twoFaceRegion h f) ∧
      (∀ v : Displacement, fderiv ℝ F 0 v =
        -v.1 * volume.real {x : JointSpace | 0 < h x} +
          ∫ x in {x : JointSpace | 0 < h x}, inner (𝕜 := ℝ) (graphGradient f x) v.2) ∧
      (∀ v w : Displacement, fderiv ℝ (fderiv ℝ F) 0 v w =
        (∫ x in {x : JointSpace | 0 < h x},
          fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x v.2 w.2) +
        ∫ x, (shortGapLinear f x v * shortGapLinear f x w) / ‖graphGradient h x‖
          ∂graphSurfaceMeasure h) ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        F z = translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) := by
  obtain ⟨ε, κ, N⟩ := hf.exists_rawFaceNeighborhood
  obtain ⟨A⟩ := hf.toRegularHeight.exists_controlledCollarAtlas
  obtain ⟨d, hd, V, hV, hV₀, hV₁, hV₂, heV⟩ := A.exists_collarCorrection_twoJet_independent hf
  obtain ⟨hB, hB₀, hB₁, hB₂⟩ := hf.toRegularHeightPair.shortOverlapBulk_twoJet
  let L : Displacement →L[ℝ] ℝ :=
    (-volume.real {x : JointSpace | 0 < h x}) • ContinuousLinearMap.fst ℝ ℝ JointSpace
  let U : Displacement → ℝ := fun z => volume.real (twoFaceRegion h f) + L z
  have hU : ContDiff ℝ 3 U := contDiff_const.add L.contDiff
  have hUD (z : Displacement) : fderiv ℝ U z = L := by
    simpa only [zero_add] using ((hasFDerivAt_const (volume.real (twoFaceRegion h f)) z).add L.hasFDerivAt).fderiv
  let F : Displacement → ℝ := fun z => U z + shortOverlapBulk h f z + V z
  have hF : ContDiffAt ℝ 3 F 0 := (hU.contDiffAt.add hB).add hV
  refine ⟨min ε d, lt_min N.radius_pos hd, F, hF, by simp [F, U, hB₀, hV₀], ?_, ?_, ?_⟩
  · intro v
    dsimp only [F]
    rw [fderiv_add ((hU.differentiable (by norm_num) 0).add (hB.differentiableAt (by norm_num)))
      (hV.differentiableAt (by norm_num)), fderiv_add (hU.differentiable (by norm_num) 0)
        (hB.differentiableAt (by norm_num)), hV₁, hUD]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, add_zero, hB₁]
    have he : (∫ x in {x : JointSpace | 0 < h x}, fderiv ℝ (fun y : JointSpace => f y) x v.2) =
        ∫ x in {x : JointSpace | 0 < h x}, inner (𝕜 := ℝ) (graphGradient f x) v.2 := by
      apply integral_congr_ae
      filter_upwards with x
      exact graph_differential_eq_inner f x v.2
    rw [he]
    dsimp [L]
    ring
  · intro v w
    have heD : fderiv ℝ F =ᶠ[𝓝 (0 : Displacement)]
        (fun z => L + fderiv ℝ (shortOverlapBulk h f) z + fderiv ℝ V z) := by
      filter_upwards [hB.eventually (by simp), hV.eventually (by simp)] with z hzB hzV
      dsimp only [F]
      rw [fderiv_add ((hU.differentiable (by norm_num) z).add (hzB.differentiableAt (by norm_num)))
        (hzV.differentiableAt (by norm_num)), fderiv_add (hU.differentiable (by norm_num) z)
          (hzB.differentiableAt (by norm_num)), hUD]
    have hDB := (hB.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    have hDV := (hV.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
    rw [heD.fderiv_eq, fderiv_add (differentiableAt_const L |>.add hDB) hDV,
      fderiv_const_add L]
    simp only [ContinuousLinearMap.add_apply, hB₂, hV₂]
  · intro z hz hc
    have hzε : ‖z.2‖ ≤ ε := (norm_snd_le z).trans
      ((show ‖z‖ < min ε d by simpa using hz).le.trans (min_le_left _ _))
    rw [hf.translatedOverlap_eq_absolute_bulk N hzε hc]
    dsimp only [F, U]
    rw [heV z (Metric.ball_subset_ball (min_le_right _ _) hz) hc]
    dsimp [L]
    ring

end AdmissibleIndependentTwoFace

namespace ShortNullRemainder

/-- The usual Taylor remainder for a nonzero constant term, produced as a
measurable representative with value AND first/second derivative bounds. -/
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

end ShortNullRemainder

namespace AdmissibleIndependentTwoFace
variable {h f : Spatial → ℝ} (hf : AdmissibleIndependentTwoFace h f)
include hf

/-- Actual class-E overlap expansion on one density-independent future-cone
ball. All geometric and primitive derivative bounds are produced here, not
assumed as extra class-E fields. The future Hessian is not discarded. -/
theorem exists_absoluteOverlap_remainder :
    ∃ (R : Displacement → ℝ) (δ T : ℝ), Measurable R ∧ 0 < δ ∧
      ShortNullRemainder.CubicBounds R δ T ∧
      ∀ z ∈ Metric.ball 0 δ, ‖z.2‖ ≤ z.1 →
        translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) =
          volume.real (twoFaceRegion h f) - z.1 * volume.real {x : JointSpace | 0 < h x} +
          (∫ x in {x : JointSpace | 0 < h x}, inner (𝕜 := ℝ) (graphGradient f x) z.2) +
          (1 / 2 : ℝ) * (∫ x in {x : JointSpace | 0 < h x},
            fderiv ℝ (fderiv ℝ (fun y : JointSpace => f y)) x z.2 z.2) +
          (1 / 2 : ℝ) * (∫ x, (z.1 - inner (𝕜 := ℝ) (graphGradient f x) z.2) ^ 2 /
            ‖graphGradient h x‖ ∂graphSurfaceMeasure h) + R z := by
  obtain ⟨ε, hε, F, hF, hF₀, hF₁, hF₂, heF⟩ := hf.exists_absoluteOverlap_twoJet
  obtain ⟨R, d, T, hR, hd, hB, he⟩ := ShortNullRemainder.exists_absolute_taylor_remainder hF
  refine ⟨R, min ε d, T, hR, lt_min hε hd, hB.mono (min_le_right _ _), ?_⟩
  intro z hz hc
  rw [← heF z (Metric.ball_subset_ball (min_le_left _ _) hz) hc,
    he z (Metric.ball_subset_ball (min_le_right _ _) hz), hF₀, hF₁, hF₂]
  have hs : (∫ x, (shortGapLinear f x z * shortGapLinear f x z) / ‖graphGradient h x‖
      ∂graphSurfaceMeasure h) =
      ∫ x, (z.1 - inner (𝕜 := ℝ) (graphGradient f x) z.2) ^ 2 /
        ‖graphGradient h x‖ ∂graphSurfaceMeasure h := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [shortGapLinear_apply, graph_differential_eq_inner, pow_two]
  rw [hs]
  ring

end AdmissibleIndependentTwoFace
end BoundaryDraft
