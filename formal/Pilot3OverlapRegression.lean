import BoundaryDraft.Pilot3Examples
import BoundaryDraft.Pilot3Tubes

/-! Actual-overlap edge cases. In particular, a retained interior critical
point at an OLD exact contact remains covered when the NEW gap is negative.
No chart-measure theorem, jet or action limit is assumed by these checks. -/

open BoundaryDraft MeasureTheory Set
open scoped Topology
noncomputable section

-- Null displacements, including the vertex, are not discarded as measure-zero cases.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (θ : Pilot3Space) (hθ : ‖θ‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) :
    pilot3Overlap h f (r, r • θ) = ∫ x, max 0 (max 0 (h x) + f (x + r • θ) - f x - r) := by
  apply hf.overlap_eq_gap
  simp [norm_smul, hθ, abs_of_nonneg hr]

example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    pilot3Overlap h f 0 = (volume (pilot3Region h f)).toReal := by
  rw [hf.volume_region]
  simpa only [pilot3Overlap, one_mul] using hf.weightedOverlap_zero (fun _ => 1) continuousOn_const

-- A negative first-endpoint weight stays negative; no absolute-value replacement.
example : pilot3WeightedOverlap pilot3BallHeight pilot3SineFuture (fun _ => -1) 0 =
    -(volume (pilot3Region pilot3BallHeight pilot3SineFuture)).toReal := by
  rw [pilot3BallSine_admissible.weightedOverlap_zero (fun _ => -1) continuousOn_const,
    pilot3BallSine_admissible.volume_region]
  simp only [neg_one_mul, integral_neg]

-- At exact contact the vertical OPEN fibre is empty, even pointwise.
example {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) (z : Pilot3Spacetime) (hc : ‖z.2‖ ≤ z.1)
    (x : Pilot3Space) (hg : pilot3OverlapGap h f z x = 0) (t : ℝ) :
    ¬ ((t, x) ∈ pilot3Region h f ∧ (t, x) + z ∈ pilot3Region h f) := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  exact C.overlap_fibre_empty_of_nonpos_gap z hc x hg.le t

private theorem planarControl : Pilot3SlopeControl pilot3BallHeight (fun _ => 0) (1 / 2) 0 :=
  ⟨by norm_num, le_rfl, by norm_num, pilot3BallHeight_lipschitz, by simp⟩

-- Explicit width, and positive margin, for the critical-source contact below.
example : pilot3PerturbationWidth (1 / 2) (1 / 2) (1 / 2) = 1 / 24 := by
  norm_num [pilot3PerturbationWidth]

example (θ : Pilot3Space) (hθ : ‖θ‖ = 1) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 24) :
    fderiv ℝ pilot3BallHeight 0 = 0 ∧
    pilot3RayGap pilot3BallHeight (fun _ => 0) 0 θ 0 (1 / 2) = 0 ∧
    pilot3RayGap pilot3BallHeight (fun _ => 0) 0 θ σ (1 / 2) < 0 ∧
    ((1 / 2 - σ / (1 / 2)) / 2) • θ ∈ pilot3HeightTube pilot3BallHeight (1 / 16) := by
  have hg : 0 ≤ pilot3RayGap pilot3BallHeight (fun _ => 0) 0 θ 0 (1 / 2) := by
    norm_num [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, pilot3BallHeight]
  refine ⟨pilot3BallHeight_critical.2, ?_, ?_, ?_⟩
  · norm_num [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, pilot3BallHeight]
  · norm_num [pilot3RayGap, pilot3OverlapGap, pilot3RayDisplacement, pilot3BallHeight]
    linarith
  · have hb := planarControl.perturbed_endpoint_margin (δ := 1 / 2) (ε := 1 / 24)
      (σ := σ) (v := 1 / 2) (by norm_num) le_rfl ⟨hσ.le, hσ'⟩ (by norm_num) 0 θ hθ hg
    have ht := pilot3_mem_heightTube (by norm_num : 0 < (1 - (1 / 2 : ℝ) - 0) * (1 / 2) / 4) hb
    convert ht using 1 <;> norm_num

-- Empty admissible data give zero actual overlap for EVERY displacement, not only causal ones.
example (z : Pilot3Spacetime) (w : Pilot3Space → ℝ) :
    pilot3WeightedOverlap (fun _ => 0) (fun _ => 0) w z = 0 := by
  have he : pilot3Region (fun _ => 0) (fun _ => 0) = ∅ := by
    ext p
    simp only [pilot3Region, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hp
    linarith
  simp [pilot3WeightedOverlap, he]
