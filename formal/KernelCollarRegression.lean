import BoundaryDraft

/-!
Independent contracts for the analytic collar step. These tests do not assume
coarea or supply a proof of the general graph-cap boundary limit.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology
noncomputable section

-- The actual signed kernel, the physical density parameter, and only
-- right continuity at zero. No continuity at positive heights is requested.
example (B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hB : Measurable B)
    (hB0 : ContinuousWithinAt B (Ici 0) 0) (C : ℝ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) δ, ‖B s‖ ≤ C) :
    Tendsto (fun ρ : ℝ => ∫ s in (0 : ℝ)..δ, planeKernel ρ s * B s)
      atTop (𝓝 (B 0)) :=
  planeKernel_collar_limit B δ hδ hB hB0 C hbound

-- Absolute integrability is checked separately from Lean's total integral.
example (B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hB : Measurable B) (C : ℝ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) δ, ‖B s‖ ≤ C) (ρ : ℝ) :
    IntervalIntegrable (fun s => planeKernel ρ s * B s) volume 0 δ :=
  intervalIntegrable_planeKernel_mul_bounded B ρ δ hδ.le hB C hbound

-- A negative profile exercises the signed integral rather than a
-- nonnegative-measure approximate identity.
example (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => ∫ s in (0 : ℝ)..δ, planeKernel ρ s * (-2)) atTop (𝓝 (-2)) := by
  apply planeKernel_collar_limit (fun _ => -2) δ hδ measurable_const
    continuousWithinAt_const 2
  intro s hs
  norm_num

-- This profile jumps both at zero (from the left) and at a positive height.
-- Its interior jump and its cutoff value need not be continuous.
private def jumpWeight (s : ℝ) : ℝ := (Ico (0 : ℝ) (1 / 2)).indicator (fun _ => 7) s

private theorem measurable_jumpWeight : Measurable jumpWeight :=
  measurable_const.indicator measurableSet_Ico

private theorem rightContinuous_jumpWeight : ContinuousWithinAt jumpWeight (Ici 0) 0 := by
  apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (7 : ℝ)) (Ici 0) 0).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs hs'
    exact indicator_of_mem (show s ∈ Ico (0 : ℝ) (1 / 2) from ⟨hs, hs'⟩) _
  · norm_num [jumpWeight]

private theorem norm_jumpWeight_le (s : ℝ) : ‖jumpWeight s‖ ≤ 7 := by
  by_cases hs : s ∈ Ico (0 : ℝ) (1 / 2)
  · rw [jumpWeight, indicator_of_mem hs]
    norm_num
  · rw [jumpWeight, indicator_of_not_mem hs, norm_zero]
    norm_num

-- The one-sided distinction is genuine, not merely a weaker-looking contract.
example : ¬ ContinuousAt jumpWeight 0 := by
  intro hc
  have hl : Tendsto jumpWeight (𝓝[<] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : s ∉ Ico (0 : ℝ) (1 / 2) := fun h => not_le_of_gt hs h.1
    rw [jumpWeight, indicator_of_not_mem hn]
  have he := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hl
  norm_num [jumpWeight] at he

example : Tendsto (fun ρ : ℝ => ∫ s in (0 : ℝ)..1, planeKernel ρ s * jumpWeight s)
    atTop (𝓝 7) := by
  have hl := planeKernel_collar_limit jumpWeight 1 (by norm_num)
    measurable_jumpWeight rightContinuous_jumpWeight 7 (fun s _ => norm_jumpWeight_le s)
  simpa [jumpWeight] using hl

-- Reversing the signed kernel reverses its mass and the resulting limit.
-- There is no hidden nonnegativity hypothesis in the general analytic lemma.
example : Tendsto (fun ε : ℝ => ∫ u in Ioi (0 : ℝ), (-planeKernel 1 u) * jumpWeight (ε * u))
    (𝓝[>] 0) (𝓝 (-7)) := by
  have hμ : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hu.le
  have hl := signed_rescaling_limit_right _ (fun u => -planeKernel 1 u) jumpWeight
    hμ integrableOn_planeKernel.neg measurable_jumpWeight rightContinuous_jumpWeight 7
    (fun s _ => norm_jumpWeight_le s)
  simpa [integral_neg, integral_planeKernel_Ioi, jumpWeight] using hl

-- Extending a collar by zero preserves its exact one-dimensional integral,
-- with only a Lebesgue-null endpoint replacement.
example (B : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (ρ : ℝ) :
    (∫ s in (0 : ℝ)..δ, planeKernel ρ s * B s) =
      ∫ s in Ioi (0 : ℝ), planeKernel ρ s * (Iio δ).indicator B s :=
  integral_planeKernel_collar_eq_halfLine B ρ δ hδ
