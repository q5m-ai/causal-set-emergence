import BoundaryDraft.ConformalGeometry
import BoundaryDraft.FiniteMeasureBDG

/-!
# Canonical controlled conformal action and exact finite-density bridge

All definitions are independent of any continuum limit. The deterministic
observable uses the isolated curved interval volume. The probability law is
constructed from the curved restricted intensity. The discrete action, closed
causal order, exclusive intervals and signed layer conventions are unchanged.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- Actual isolated curved interval volume, with both selected endpoints removed. -/
def conformalIntervalVolume (Ω : Spacetime → ℝ) (M : Set Spacetime) (x y : Spacetime) : ℝ :=
  ((conformalVolume Ω).restrict M (causalIntervalInterior x y)).toReal

theorem conformalIntervalVolume_eq (Ω : Spacetime → ℝ) (M : Set Spacetime) (x y : Spacetime) :
    conformalIntervalVolume Ω M x y =
      (conformalVolume Ω (M ∩ causalIntervalInterior x y)).toReal := by
  rw [conformalIntervalVolume, Measure.restrict_apply (measurableSet_causalIntervalInterior x y),
    inter_comm]

/-- Canonical deterministic unweighted observable for #73--#76. -/
def conformalAction (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) : ℝ :=
  finiteMeasureAction ((conformalVolume Ω).restrict M) ρ

/-- Density times the actual restricted metric volume. -/
def conformalIntensity (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) : Measure Spacetime :=
  ENNReal.ofReal ρ • (conformalVolume Ω).restrict M

/-- The previously constructed finite Poisson law, not supplied as input. -/
def conformalProbability (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) :
    Measure (Multiset Spacetime) := FinitePoisson.law (conformalIntensity Ω ρ M)

/-- Expectation of the genuine original finite-order discrete action. -/
def conformalExpectedAction (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) : ℝ :=
  ∫ c, discreteBDGAction ρ c ∂conformalProbability Ω ρ M

/-- Explicit integral contract. Both endpoints use curved measure, and the
inner interval volume remains restricted even for a non-causally-convex set. -/
theorem conformalAction_eq_integral (Ω : Spacetime → ℝ) (ρ : ℝ) (M : Set Spacetime) :
    conformalAction Ω ρ M = (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((conformalVolume Ω M).toReal - ρ *
        ∫ x in M, ∫ y in M ∩ causalFuture x,
          bdgKernel (ρ * conformalIntervalVolume Ω M x y) ∂conformalVolume Ω ∂conformalVolume Ω) := by
  simp only [conformalAction, finiteMeasureAction, Measure.restrict_apply_univ,
    conformalIntervalVolume, Measure.restrict_restrict (isClosed_causalFuture _).measurableSet,
    inter_comm (causalFuture _) M]

/-- Changing only the ambient extension does not change the observable. -/
theorem conformalAction_congr {M : Set Spacetime} (hm : MeasurableSet M)
    {Ω Ψ : Spacetime → ℝ} (he : EqOn Ω Ψ M) (ρ : ℝ) :
    conformalAction Ω ρ M = conformalAction Ψ ρ M := by
  rw [conformalAction, conformalAction, conformalVolume_restrict_congr hm he]

theorem conformalProbability_congr {M : Set Spacetime} (hm : MeasurableSet M)
    {Ω Ψ : Spacetime → ℝ} (he : EqOn Ω Ψ M) (ρ : ℝ) :
    conformalProbability Ω ρ M = conformalProbability Ψ ρ M := by
  rw [conformalProbability, conformalProbability, conformalIntensity, conformalIntensity,
    conformalVolume_restrict_congr hm he]

namespace ControlledConformalFactor
variable {Ω : Spacetime → ℝ} {M : Set Spacetime} (hΩ : ControlledConformalFactor Ω M)
  (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
include hΩ hm hb

theorem isFiniteMeasure_intensity (ρ : ℝ) : IsFiniteMeasure (conformalIntensity Ω ρ M) := by
  constructor
  simp only [conformalIntensity, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hΩ.finite_volume hm hb)

theorem isProbabilityMeasure (ρ : ℝ) : IsProbabilityMeasure (conformalProbability Ω ρ M) := by
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  exact FinitePoisson.isProbabilityMeasure_law _

theorem measurable_intervalVolume :
    Measurable (fun p : Spacetime × Spacetime => conformalIntervalVolume Ω M p.1 p.2) := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  exact (measurable_measure_prodMk_left measurableSet_causalIntervalInterior_joint).ennreal_toReal

/-- Joint measurability includes the density parameter; geometry stays fixed. -/
theorem measurable_kernel :
    Measurable (fun p : ℝ × (Spacetime × Spacetime) =>
      bdgKernel (p.1 * conformalIntervalVolume Ω M p.2.1 p.2.2)) := by
  have hc : Continuous bdgKernel := by unfold bdgKernel bdgPolynomial; fun_prop
  exact hc.measurable.comp (measurable_fst.mul ((hΩ.measurable_intervalVolume hm hb).comp measurable_snd))

theorem intervalVolume_bounds (x y : Spacetime) :
    0 ≤ conformalIntervalVolume Ω M x y ∧
      conformalIntervalVolume Ω M x y ≤ (conformalVolume Ω M).toReal := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have ht := ENNReal.toReal_mono (measure_ne_top ((conformalVolume Ω).restrict M) univ)
    (measure_mono (subset_univ (causalIntervalInterior x y)))
  simpa [conformalIntervalVolume] using ht

/-- For region endpoints ambient interval volume is finite and agrees with
the isolated volume, if and only where causal convexity has been supplied. -/
theorem intervalVolume_ambient (hc : CausallyConvex M) {x y : Spacetime}
    (hx : x ∈ M) (hy : y ∈ M) :
    conformalVolume Ω (causalInterval x y) < ∞ ∧
      conformalIntervalVolume Ω M x y = (conformalVolume Ω (causalInterval x y)).toReal := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  rw [← conformalVolume_restrict_interval hc Ω hx hy]
  exact ⟨measure_lt_top _ _, rfl⟩

/-- Absolute integrability on the entire endpoint product, before the causal
mask. Derived from bounded Poisson probabilities, not an analytic premise. -/
theorem integrable_kernel {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun p : Spacetime × Spacetime => bdgKernel (ρ * conformalIntervalVolume Ω M p.1 p.2))
      (((conformalVolume Ω).restrict M).prod ((conformalVolume Ω).restrict M)) := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  have hi := FiniteMeasureBDG.integrable_kernel (conformalIntensity Ω ρ M)
    ((conformalVolume Ω).restrict M)
  simpa only [conformalIntensity, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ.le, conformalIntervalVolume] using hi

theorem integrable_kernel_section {ρ : ℝ} (hρ : 0 < ρ) (x : Spacetime) :
    Integrable (fun y => bdgKernel (ρ * conformalIntervalVolume Ω M x y))
      ((conformalVolume Ω).restrict M) := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  have hi := FiniteMeasureBDG.integrable_kernel_section (conformalIntensity Ω ρ M)
    ((conformalVolume Ω).restrict M) x
  simpa only [conformalIntensity, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ.le, conformalIntervalVolume] using hi

theorem integrable_causalKernel {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun p : Spacetime × Spacetime =>
      (causalFuture p.1).indicator (fun y => bdgKernel (ρ * conformalIntervalVolume Ω M p.1 y)) p.2)
      (((conformalVolume Ω).restrict M).prod ((conformalVolume Ω).restrict M)) :=
  (hΩ.integrable_kernel hm hb hρ).indicator measurableSet_causalRelation

/-- Fubini supplies an integrable outer endpoint function, including its sign. -/
theorem integrable_outer_kernel {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun x => ∫ y in M ∩ causalFuture x,
      bdgKernel (ρ * conformalIntervalVolume Ω M x y) ∂conformalVolume Ω)
      ((conformalVolume Ω).restrict M) := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  have hi := (hΩ.integrable_causalKernel hm hb hρ).integral_prod_left
  simpa only [integral_indicator (isClosed_causalFuture _).measurableSet,
    Measure.restrict_restrict (isClosed_causalFuture _).measurableSet,
    inter_comm (causalFuture _) M] using hi

/-- The original discrete action is integrable under the constructed law. -/
theorem integrable_discreteAction (ρ : ℝ) :
    Integrable (discreteBDGAction ρ) (conformalProbability Ω ρ M) := by
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  exact FiniteMeasureBDG.integrable_action _ _

/-- Exact normalized expectation at each positive density. Causal convexity
is unnecessary because the deterministic action uses restricted volume. -/
theorem expectedAction_eq {ρ : ℝ} (hρ : 0 < ρ) :
    conformalExpectedAction Ω ρ M = conformalAction Ω ρ M := by
  letI := hΩ.isFiniteMeasure_restrict hm hb
  exact finiteMeasureAction_expectation _ hρ

/-- Every sample is supported in the original region almost surely. -/
theorem ae_supported (ρ : ℝ) :
    ∀ᵐ c ∂conformalProbability Ω ρ M, ∀ x ∈ c, x ∈ M := by
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  apply FinitePoisson.ae_supported _ hm
  simp [conformalIntensity, Measure.restrict_apply hm.compl]

theorem ae_nodup (ρ : ℝ) : ∀ᵐ c ∂conformalProbability Ω ρ M, c.Nodup := by
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  letI : NoAtoms (conformalIntensity Ω ρ M) := by
    constructor
    intro x
    simp [conformalIntensity]
  exact FinitePoisson.ae_nodup _ (isClosed_eq continuous_fst continuous_snd).measurableSet

/-- Empty and nonempty curved-null regions both produce the empty sample. -/
theorem ae_empty_of_volume_zero (ρ : ℝ) (hz : conformalVolume Ω M = 0) :
    ∀ᵐ c ∂conformalProbability Ω ρ M, c = 0 := by
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  apply FinitePoisson.ae_empty _
  simp [conformalIntensity, Measure.restrict_eq_zero.mpr hz]

theorem expectedAction_zero_of_volume_zero (ρ : ℝ) (hz : conformalVolume Ω M = 0) :
    conformalExpectedAction Ω ρ M = 0 := by
  calc
    _ = ∫ _c, (0 : ℝ) ∂conformalProbability Ω ρ M := by
      apply integral_congr_ae
      filter_upwards [hΩ.ae_empty_of_volume_zero hm hb ρ hz] with c hc
      simp [hc, discreteBDGAction, intervalLayer, intervalPairSum,
        FiniteConfiguration.pairSum, FiniteConfiguration.pointSum]
    _ = 0 := integral_zero _ _

/-- On the actual probability space the observable is the finite-set action,
with ordered-pair layers and exactly the original coefficients. -/
theorem ae_finite_order (ρ : ℝ) :
    ∀ᵐ c ∂conformalProbability Ω ρ M, (∀ x ∈ c, x ∈ M) ∧
      discreteBDGAction ρ c = bdgNormalization ρ *
        ((Fintype.card (CausalPoint c) : ℝ) - (causalLayerPairs 0 c).card +
          9 * (causalLayerPairs 1 c).card - 16 * (causalLayerPairs 2 c).card +
          8 * (causalLayerPairs 3 c).card) := by
  filter_upwards [hΩ.ae_supported hm hb ρ, hΩ.ae_nodup hm hb ρ] with c hs hc
  exact ⟨hs, discreteBDGAction_eq_finite_order ρ hc⟩

/-- Subset counts have the Poisson law at the actual curved restricted rate. -/
theorem count_probability {ρ : ℝ} (hρ : 0 < ρ) {A : Set Spacetime}
    (hA : MeasurableSet A) (k : ℕ) :
    conformalProbability Ω ρ M {c | FiniteConfiguration.count A c = k} =
      ENNReal.ofReal (Real.exp (-(ρ * (conformalVolume Ω (A ∩ M)).toReal)) *
        (ρ * (conformalVolume Ω (A ∩ M)).toReal) ^ k / k.factorial) := by
  letI := hΩ.isFiniteMeasure_intensity hm hb ρ
  rw [conformalProbability, FinitePoisson.count_probability _ hA]
  change ENNReal.ofReal (poissonPMFReal _ k) = _
  simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal, conformalIntensity,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ.le,
    Measure.restrict_apply hA]

end ControlledConformalFactor

/-- Specialization to exactly the original admissible two-face class. -/
theorem AdmissibleTwoFace.conformal_expectedAction_eq {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) {Ω : Spacetime → ℝ}
    (hΩ : ControlledConformalFactor Ω (twoFaceRegion h f)) {ρ : ℝ} (hρ : 0 < ρ) :
    conformalExpectedAction Ω ρ (twoFaceRegion h f) = conformalAction Ω ρ (twoFaceRegion h f) :=
  hΩ.expectedAction_eq hf.boundedCausalRegion.measurable hf.boundedCausalRegion.bounded hρ

/-- Unit factor recovers the unchanged flat probability and observable. -/
@[simp] theorem conformalExpectedAction_one (ρ : ℝ) (M : Set Spacetime) :
    conformalExpectedAction (fun _ => 1) ρ M = expectedBDGAction ρ M := by
  simp [conformalExpectedAction, conformalProbability, conformalIntensity, expectedBDGAction]

theorem conformalAction_one {M : Set Spacetime} (hM : BoundedCausalRegion M)
    {ρ : ℝ} (hρ : 0 < ρ) : conformalAction (fun _ => 1) ρ M = continuumMean ρ M := by
  rw [← (controlledConformalFactor_const M (by norm_num : (0 : ℝ) < 1)).expectedAction_eq
    hM.measurable hM.bounded hρ, conformalExpectedAction_one, hM.expectedBDGAction_eq hρ]

/-- Constant conformal scaling changes the physical density by c^4 and the
normalized discrete action by c^2. This is not a curved example. -/
theorem discreteBDGAction_density_scaling {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (s : Multiset Spacetime) :
    discreteBDGAction ρ s = c ^ 2 * discreteBDGAction (ρ * c ^ 4) s := by
  have hn : bdgNormalization ρ = c ^ 2 * bdgNormalization (ρ * c ^ 4) := by
    rw [bdgNormalization, bdgNormalization, Real.sqrt_mul hρ.le,
      show c ^ 4 = (c ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg c)]
    have hcn : c ^ 2 ≠ 0 := pow_ne_zero _ hc.ne'
    field_simp
    ring
  simp only [discreteBDGAction, hn]
  ring

theorem conformalExpectedAction_const {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (M : Set Spacetime) :
    conformalExpectedAction (fun _ => c) ρ M = c ^ 2 * expectedBDGAction (ρ * c ^ 4) M := by
  simp only [conformalExpectedAction, conformalProbability, conformalIntensity,
    conformalVolume_const, Measure.restrict_smul, smul_smul,
    ← ENNReal.ofReal_mul hρ.le, expectedBDGAction]
  simp_rw [discreteBDGAction_density_scaling hρ hc, integral_const_mul]

theorem conformalAction_const {M : Set Spacetime} (hM : BoundedCausalRegion M)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) :
    conformalAction (fun _ => c) ρ M = c ^ 2 * continuumMean (ρ * c ^ 4) M := by
  rw [← (controlledConformalFactor_const M hc).expectedAction_eq hM.measurable hM.bounded hρ,
    conformalExpectedAction_const hρ hc, hM.expectedBDGAction_eq (mul_pos hρ (pow_pos hc _))]

end BoundaryDraft
