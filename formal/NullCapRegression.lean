import BoundaryDraft

/-!
# Null-cap contract regression checks

These checks restate the unchanged target, specialize the independently proved
four-dimensional moment formula at `n = 0,1`, exercise both weight endpoints,
and instantiate the full spacetime limit at concrete parameters.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

-- Restate the original contract independently of the `Goal` alias.
example : ∀ T a : ℝ, 0 < a → a < T →
    Tendsto (fun ρ => continuumMean ρ (nullCapRegion T a))
      atTop (𝓝 (nullJointArea T a)) := nullCapLimitGoal

-- The actual four-dimensional volume of a standard causal interval.
example (T : ℝ) (hT : 0 < T) :
    (∫ _y in causalInterval 0 (timeAxis T), (1 : ℝ)) =
      Real.pi * T ^ 4 / 24 := by
  have h := standard_causalInterval_moment T hT 0
  norm_num at h ⊢
  simpa using h

-- The first nonconstant even proper-time moment.
example (T : ℝ) (hT : 0 < T) :
    (∫ y in causalInterval 0 (timeAxis T), intervalSq 0 y ^ 2) =
      Real.pi * T ^ 8 / 480 := by
  have h := standard_causalInterval_moment T hT 1
  norm_num at h ⊢
  simpa using h

-- The continuous endpoint is one quarter of the predicted joint area.
example : nullCapWeight 2 1 0 = 3 * Real.pi / 4 := by
  rw [nullCapWeight_zero 2 1 (by norm_num)]
  ring

-- Both the geometric weight and its continuous extension vanish at cutoff.
example : nullCapWeight 2 1 2 = 0 :=
  nullCapWeight_of_ge 2 1 2 (by norm_num)

example : nullCapWeightExtension 2 1 2 = 0 :=
  nullCapWeightExtension_of_ge 2 1 2 (by norm_num) (by norm_num) (by norm_num)

-- A concrete exact finite-density reduction, before taking the limit.
example (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (nullCapRegion 2 1) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ σ in Ioi (0 : ℝ),
          Real.exp (-(Real.pi / 24) * ρ * σ ^ 2) *
            nullCapWeightExtension 2 1 σ :=
  nullCap_continuumMean_eq_weightExtension 2 1 ρ (by norm_num) (by norm_num) hρ

-- Concrete specialization of the unchanged four-dimensional target.
example : Tendsto (fun ρ => continuumMean ρ (nullCapRegion 2 1))
    atTop (𝓝 (3 * Real.pi)) := by
  have h := nullCapLimitGoal 2 1 (by norm_num) (by norm_num)
  have heq : nullJointArea 2 1 = 3 * Real.pi := by
    unfold nullJointArea
    ring
  rw [heq] at h
  exact h
