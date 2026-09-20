import BoundaryDraft

/-!
# Ellipsoid contract regression checks

These specializations are checked by `check.sh`, independently of the library
build. They exercise the original target, both volume endpoints, the critical
height, and a negative integrand without any positivity premise.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped BigOperators Topology Interval

noncomputable section

-- Restate the original contract independently of the `Goal` alias.
example : ∀ (a : ℝ) (b : Fin 3 → ℝ), 0 < a → (∀ i, 2 * a < b i) →
    Tendsto (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile a b)))
      atTop (𝓝 (2 * Real.pi * (∏ i : Fin 3, b i) / a)) := ellipsoidLimitGoal

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 0 < b i) :
    volume {x | 0 < ellipsoidProfile a b x} =
      ENNReal.ofReal ((4 * Real.pi / 3) * (∏ i, b i)) := by
  simpa using volume_ellipsoid_superlevel a b ha hb 0 ⟨le_rfl, ha.le⟩

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 0 < b i) :
    volume {x | a < ellipsoidProfile a b x} = 0 := by
  simpa [ha.ne'] using volume_ellipsoid_superlevel a b ha hb a ⟨ha.le, le_rfl⟩

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) :
    {x | a < ellipsoidProfile a b x} = ∅ :=
  ellipsoid_superlevel_empty a b ha.le a le_rfl

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) : ellipsoidWeight a b a = 0 :=
  ellipsoidWeight_of_ge a b ha a le_rfl

example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 0 < b i) :
    (∫ x in {x | 0 < ellipsoidProfile a b x}, -ellipsoidProfile a b x) =
      (2 * Real.pi * (∏ i, b i) / a) *
        ∫ s in (0 : ℝ)..a, Real.sqrt (1 - s / a) * (-s) :=
  integral_ellipsoid_profile a b ha hb (fun s => -s) continuous_id.neg

-- The unequal-axis example in the numerical tables, now at the level of the
-- original deterministic four-dimensional integral rather than a proxy.
example : Tendsto
    (fun ρ => continuumMean ρ (graphCapRegion (ellipsoidProfile (1 / 4) ![1, 2, 3])))
    atTop (𝓝 (48 * Real.pi)) := by
  have hb : ∀ i : Fin 3, 2 * (1 / 4 : ℝ) < ![1, 2, 3] i := by
    intro i
    fin_cases i <;> norm_num
  have h := ellipsoidLimitGoal (1 / 4) ![1, 2, 3] (by norm_num) hb
  convert h using 1
  norm_num [Fin.prod_univ_succ]
  ring
