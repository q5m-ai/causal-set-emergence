import BoundaryDraft.NullTransverseCancellation
import BoundaryDraft.KernelHalfLine

/-!
Independent contracts for issue #53. The signed cubic-cutoff family has an
arbitrary quadratic jet and a genuine nonzero little-o remainder. No overlap
geometry or geometric admissibility assumption is used here.
-/

open BoundaryDraft MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section

-- Absolute integrability is independent of the signed integral's value.
example (j : ℕ) : IntegrableOn (fun z : ℝ => z ^ j * |bdgKernel (z ^ 2)|) (Ioi 0) :=
  integrableOn_abs_bdgKernel_transverse_moment j

example : (∫ z : ℝ in Ioi 0, bdgKernel (z ^ 2)) = 0 :=
  integral_bdgKernel_transverse_zero
example : (∫ z : ℝ in Ioi 0, z * bdgKernel (z ^ 2)) = 0 :=
  integral_bdgKernel_transverse_one
example : (∫ z : ℝ in Ioi 0, z ^ 2 * bdgKernel (z ^ 2)) = 0 :=
  integral_bdgKernel_transverse_two
example : (∫ z : ℝ in Ioi 0, z ^ 3 * bdgKernel (z ^ 2)) = -(1 / 2) :=
  integral_bdgKernel_transverse_three

-- These are different kernels, and neither the kernel nor the weight below
-- can be replaced by a nonnegative approximate identity.
example : (∫ z : ℝ in Ioi 0, planeKernel 1 z) = 1 := integral_planeKernel_Ioi
example : bdgKernel 1 < 0 := by
  have he : bdgKernel 1 = -(4 / 3) * Real.exp (-1) := by
    norm_num [bdgKernel, bdgPolynomial]
  rw [he]
  exact mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)

private def cutoffCubic (δ b₀ b₁ b₂ b₃ : ℝ) : ℝ → ℝ :=
  (Ioo 0 δ).indicator (fun s => b₀ + b₁ * s + b₂ * s ^ 2 + b₃ * s ^ 3)

private theorem measurable_cutoffCubic (δ b₀ b₁ b₂ b₃ : ℝ) :
    Measurable (cutoffCubic δ b₀ b₁ b₂ b₃) := by
  unfold cutoffCubic
  exact (by fun_prop : Measurable (fun s : ℝ => b₀ + b₁ * s + b₂ * s ^ 2 + b₃ * s ^ 3)).indicator
    measurableSet_Ioo

private theorem compactSupport_cutoffCubic (δ b₀ b₁ b₂ b₃ : ℝ) :
    HasCompactSupport (cutoffCubic δ b₀ b₁ b₂ b₃) := by
  apply HasCompactSupport.intro (K := Icc 0 δ) isCompact_Icc
  intro s hs
  exact indicator_of_not_mem (fun h => hs ⟨h.1.le, h.2.le⟩) _

private theorem bounded_cutoffCubic (δ b₀ b₁ b₂ b₃ : ℝ) :
    ∃ C : ℝ, ∀ s, ‖cutoffCubic δ b₀ b₁ b₂ b₃ s‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s : ℝ => b₀ + b₁ * s + b₂ * s ^ 2 + b₃ * s ^ 3)
    (s := Icc 0 δ) (by fun_prop)
  refine ⟨max C 0, fun s => ?_⟩
  by_cases hs : s ∈ Ioo 0 δ
  · rw [cutoffCubic, indicator_of_mem hs]
    exact (hC s ⟨hs.1.le, hs.2.le⟩).trans (le_max_left _ _)
  · rw [cutoffCubic, indicator_of_not_mem hs, norm_zero]
    exact le_max_right _ _

private theorem jet_cutoffCubic (δ b₀ b₁ b₂ b₃ : ℝ) (hδ : 0 < δ) :
    (fun s => cutoffCubic δ b₀ b₁ b₂ b₃ s - (b₀ + b₁ * s + b₂ * s ^ 2)) =o[𝓝[>] 0]
      (fun s => s ^ 2) := by
  have h : (fun s : ℝ => b₃ * s ^ 3) =o[𝓝[>] 0] (fun s => s ^ 2) :=
    ((isLittleO_pow_pow (𝕜 := ℝ) (by decide : 2 < 3)).const_mul_left b₃).mono
      nhdsWithin_le_nhds
  apply h.congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with s hs hsδ
  rw [cutoffCubic, indicator_of_mem (show s ∈ Ioo 0 δ from ⟨hs, hsδ⟩)]
  ring

-- Any positive cutoff, arbitrary signs, and arbitrary nonzero quadratic jet.
private theorem limit_cutoffCubic (δ b₀ b₁ b₂ b₃ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) * ∫ s : ℝ in Ioi 0,
      cutoffCubic δ b₀ b₁ b₂ b₃ s * bdgKernel (c * ρ * s ^ 2)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := bounded_cutoffCubic δ b₀ b₁ b₂ b₃
  exact bdgKernel_transverse_cancellation _ (measurable_cutoffCubic δ b₀ b₁ b₂ b₃)
    C (fun s _ => hC s) b₀ b₁ b₂ (jet_cutoffCubic δ b₀ b₁ b₂ b₃ hδ) c hc

-- A signed compactly supported example with jet (-2, 1, 3) and remainder -s^3.
private def signedCutoff := cutoffCubic 1 (-2) 1 3 (-1)

example : HasCompactSupport signedCutoff := compactSupport_cutoffCubic _ _ _ _ _
example : signedCutoff (1 / 2) < 0 ∧ 0 < signedCutoff (3 / 4) := by
  norm_num [signedCutoff, cutoffCubic, Set.indicator]
example : signedCutoff 0 = 0 ∧ signedCutoff 1 = 0 := by
  norm_num [signedCutoff, cutoffCubic, Set.indicator]

-- The support cutoff really is discontinuous, not secretly smoothed.
example : ¬ ContinuousAt signedCutoff 1 := by
  intro hc
  have hl : Tendsto signedCutoff (𝓝[<] 1) (𝓝 1) := by
    have hp : Tendsto (fun s : ℝ => -2 + s + 3 * s ^ 2 - s ^ 3) (𝓝[<] 1) (𝓝 1) := by
      have h : Continuous (fun s : ℝ => -2 + s + 3 * s ^ 2 - s ^ 3) := by fun_prop
      have h1 : Tendsto (fun s : ℝ => -2 + s + 3 * s ^ 2 - s ^ 3) (𝓝[<] 1)
          (𝓝 (-2 + 1 + 3 * 1 ^ 2 - 1 ^ 3)) :=
        (h.tendsto 1).mono_left nhdsWithin_le_nhds
      norm_num at h1
      exact h1
    apply hp.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with s hs hs0
    rw [signedCutoff, cutoffCubic, indicator_of_mem (show s ∈ Ioo 0 1 from ⟨hs0, hs⟩)]
    ring
  have he := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hl
  norm_num [signedCutoff, cutoffCubic, Set.indicator] at he

example : Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) * ∫ s : ℝ in Ioi 0,
    signedCutoff s * bdgKernel ((Real.pi / 24) * ρ * s ^ 2)) atTop (𝓝 0) :=
  limit_cutoffCubic _ _ _ _ _ _ (by norm_num) (by positivity)

example (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => signedCutoff s * bdgKernel ((Real.pi / 24) * ρ * s ^ 2))
      (Ioi 0) := by
  obtain ⟨C, hC⟩ := bounded_cutoffCubic 1 (-2) 1 3 (-1)
  exact integrableOn_bdgKernel_density_mul_bounded _ (measurable_cutoffCubic _ _ _ _ _)
    C (fun s _ => hC s) _ ρ (by positivity) hρ

-- A pure nonzero quadratic jet also cancels with a discontinuous cutoff.
example : Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) * ∫ s : ℝ in Ioi 0,
    cutoffCubic 2 0 0 5 0 s * bdgKernel (3 * ρ * s ^ 2)) atTop (𝓝 0) :=
  limit_cutoffCubic _ _ _ _ _ _ (by norm_num) (by norm_num)
