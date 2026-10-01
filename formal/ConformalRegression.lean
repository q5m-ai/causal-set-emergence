import BoundaryDraft.ConformalExamples

/-! Independent contracts for #93. No curvature/limit identity is an input. -/
open BoundaryDraft MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
noncomputable section
namespace ConformalRegression

-- The main contract expands the law, normalization, every signed layer,
-- both curved endpoint measures, and the actual restricted interval rate.
example (Ω : Spacetime → ℝ) (M : Set Spacetime)
    (hΩ : ControlledConformalFactor Ω M) (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime,
      (4 / (Real.sqrt 6 * Real.sqrt ρ)) *
        ((c.card : ℝ) - intervalLayer 0 c + 9 * intervalLayer 1 c -
          16 * intervalLayer 2 c + 8 * intervalLayer 3 c)
      ∂FinitePoisson.law (ENNReal.ofReal ρ •
        (volume.withDensity (fun p => ENNReal.ofReal (Ω p ^ 4))).restrict M)) =
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (((volume.withDensity (fun p => ENNReal.ofReal (Ω p ^ 4))) M).toReal -
        ρ * ∫ x in M, ∫ y in M ∩ causalFuture x,
          bdgKernel (ρ * (((volume.withDensity (fun p => ENNReal.ofReal (Ω p ^ 4))).restrict M)
            (causalInterval x y \ {x, y})).toReal)
          ∂volume.withDensity (fun p => ENNReal.ofReal (Ω p ^ 4))
          ∂volume.withDensity (fun p => ENNReal.ofReal (Ω p ^ 4))) := by
  change conformalExpectedAction Ω ρ M = _
  rw [hΩ.expectedAction_eq hm hb hρ]
  exact conformalAction_eq_integral Ω ρ M

-- The same law has total mass one, support and simplicity; no custom law field.
example (Ω : Spacetime → ℝ) (M : Set Spacetime)
    (hΩ : ControlledConformalFactor Ω M) (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) :
    IsProbabilityMeasure (conformalProbability Ω ρ M) ∧
      ∀ᵐ c ∂conformalProbability Ω ρ M, c.Nodup ∧ ∀ x ∈ c, x ∈ M := by
  refine ⟨hΩ.isProbabilityMeasure hm hb ρ, ?_⟩
  filter_upwards [hΩ.ae_nodup hm hb ρ, hΩ.ae_supported hm hb ρ] with c hn hs
  exact ⟨hn, hs⟩

-- Finite factorial moments suffice even before specifying conformal geometry.
example (μ : Measure Spacetime) [IsFiniteMeasure μ] (ρ : ℝ) :
    Integrable (discreteBDGAction ρ) (FinitePoisson.law μ) :=
  FiniteMeasureBDG.integrable_action μ ρ

example (μ : Measure Spacetime) [IsFiniteMeasure μ] (k : ℕ) :
    (∫ c, (intervalLayer k c : ℝ) ∂FinitePoisson.law μ) =
      ∫ x, ∫ y, if y ∈ causalFuture x ∧ x ≠ y then
        (poissonPMF (μ (causalIntervalInterior x y)).toNNReal k).toReal else 0 ∂μ ∂μ :=
  FiniteMeasureBDG.integral_layer μ k

example (μ : Measure Spacetime) [IsFiniteMeasure μ] (x : Spacetime) :
    FiniteMeasureBDG.pairMean μ x x = 0 := by simp [FiniteMeasureBDG.pairMean]

-- Exclusive endpoints, not removal of every null-related intermediate point.
example (Ω : Spacetime → ℝ) (x y : Spacetime) :
    conformalVolume Ω (causalInterval x y \ {x, y}) = conformalVolume Ω (causalInterval x y) :=
  conformalVolume_exclusive Ω x y

example (Ω : Spacetime → ℝ) (x : Spacetime) :
    conformalVolume Ω {y : Spacetime | intervalSq x y = 0} = 0 :=
  conformalVolume_absolutelyContinuous Ω (volume_nullCone_at x)

-- Ambient compatibility is a consequence, never part of the interval definition.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (Ω : Spacetime → ℝ)
    (hΩ : ControlledConformalFactor Ω (twoFaceRegion h f)) {x y : Spacetime}
    (hx : x ∈ twoFaceRegion h f) (hy : y ∈ twoFaceRegion h f) :
    conformalVolume Ω (causalInterval x y) < ∞ ∧
      conformalIntervalVolume Ω (twoFaceRegion h f) x y =
        (conformalVolume Ω (causalInterval x y)).toReal :=
  hΩ.intervalVolume_ambient hf.boundedCausalRegion.measurable hf.boundedCausalRegion.bounded
    hf.boundedCausalRegion.causallyConvex hx hy

-- Simultaneous density/endpoint measurability and signed product/outer integrability.
example (Ω : Spacetime → ℝ) (M : Set Spacetime)
    (hΩ : ControlledConformalFactor Ω M) (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (fun p : ℝ × (Spacetime × Spacetime) =>
      bdgKernel (p.1 * conformalIntervalVolume Ω M p.2.1 p.2.2)) ∧
    Integrable (fun p : Spacetime × Spacetime => bdgKernel (ρ * conformalIntervalVolume Ω M p.1 p.2))
      (((conformalVolume Ω).restrict M).prod ((conformalVolume Ω).restrict M)) ∧
    Integrable (fun x => ∫ y in M ∩ causalFuture x,
      bdgKernel (ρ * conformalIntervalVolume Ω M x y) ∂conformalVolume Ω)
      ((conformalVolume Ω).restrict M) :=
  ⟨hΩ.measurable_kernel hm hb, hΩ.integrable_kernel hm hb hρ, hΩ.integrable_outer_kernel hm hb hρ⟩

-- Original flat bridge and non-unit/reciprocal scaling, not a redefined flat action.
example {M : Set Spacetime} (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    conformalAction (fun _ => 1) ρ M = continuumMean ρ M := conformalAction_one hM hρ

example {M : Set Spacetime} (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    conformalAction (fun _ => 2) ρ M = 4 * continuumMean (16 * ρ) M := by
  convert conformalAction_const hM hρ (by norm_num : (0 : ℝ) < 2) using 1
  ring

example {M : Set Spacetime} (hM : BoundedCausalRegion M) {ρ : ℝ} (hρ : 0 < ρ) :
    conformalAction (fun _ => 1 / 2) ρ M = (1 / 4) * continuumMean (ρ / 16) M := by
  convert conformalAction_const hM hρ (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ring

-- Empty and nonempty zero-volume regions require no uniform-point choice.
example (ρ : ℝ) (x : Spacetime) :
    ∀ᵐ c ∂conformalProbability quadraticConformalFactor ρ {x}, c = 0 :=
  (quadraticConformalFactor_controlled Bornology.isBounded_singleton).ae_empty_of_volume_zero
    (measurableSet_singleton x) Bornology.isBounded_singleton ρ (by simp)

example (ρ : ℝ) (x : Spacetime) : conformalExpectedAction quadraticConformalFactor ρ {x} = 0 :=
  (quadraticConformalFactor_controlled Bornology.isBounded_singleton).expectedAction_zero_of_volume_zero
    (measurableSet_singleton x) Bornology.isBounded_singleton ρ (by simp)

example (ρ : ℝ) : conformalAction quadraticConformalFactor ρ ∅ = 0 := by
  simp [conformalAction, finiteMeasureAction]

-- Only geometric fields: the original region and all-order conformal regularity.
example {ρ : ℝ} (hρ : 0 < ρ) :
    conformalExpectedAction quadraticConformalFactor ρ
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0)) =
    conformalAction quadraticConformalFactor ρ
      (twoFaceRegion (ellipsoidProfile (1 / 4) (fun _ => 4)) (fun _ => 0)) :=
  conformalExample_expectation hρ

-- The extension is unobservable, not a new geometric constraint on remote points.
example {M : Set Spacetime} (hm : MeasurableSet M) {Ω Ψ : Spacetime → ℝ}
    (he : EqOn Ω Ψ M) (ρ : ℝ) :
    conformalAction Ω ρ M = conformalAction Ψ ρ M ∧
      conformalProbability Ω ρ M = conformalProbability Ψ ρ M :=
  ⟨conformalAction_congr hm he ρ, conformalProbability_congr hm he ρ⟩

end ConformalRegression
