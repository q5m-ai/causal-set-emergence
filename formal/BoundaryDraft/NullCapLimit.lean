import BoundaryDraft.NullCapReduction
import BoundaryDraft.NullGaussian

/-!
# Null-cap Gaussian limit

This file turns the exact spacetime coarea formula into a fixed half-line
Gaussian integral.  The logarithmic weight is extended continuously to the
left by its endpoint value and to the right by zero; the extension is only an
analytic device and agrees with the geometric weight for every nonnegative
proper-time square.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section
namespace BoundaryDraft

/-- A globally continuous extension of the exact finite-support null weight.
It clamps the proper-time square to `[0,aT]`; the value at `aT` is proved to
vanish below. -/
def nullCapWeightExtension (T a σ : ℝ) : ℝ :=
  nullCapWeightCore T a (min (max σ 0) (a * T))

theorem continuous_nullCapWeightCore (T a : ℝ) :
    Continuous (nullCapWeightCore T a) := by
  unfold nullCapWeightCore
  have hpoly : Continuous (fun σ : ℝ =>
      a * (2 * T - a) - 2 * (1 - a / T) * σ - σ ^ 2 / T ^ 2) := by
    fun_prop
  have hmulLog : Continuous (fun σ : ℝ => 2 * (σ * Real.log σ)) :=
    continuous_const.mul Real.continuous_mul_log
  have hlast : Continuous (fun σ : ℝ => 2 * σ * Real.log (a * T)) := by
    fun_prop
  simpa only [mul_assoc] using
    continuous_const.mul ((hpoly.add hmulLog).sub hlast)

theorem continuous_nullCapWeightExtension (T a : ℝ) :
    Continuous (nullCapWeightExtension T a) := by
  unfold nullCapWeightExtension
  exact (continuous_nullCapWeightCore T a).comp
    ((continuous_id.max continuous_const).min continuous_const)

theorem nullCapWeightCore_cutoff (T a : ℝ) (ha : 0 < a) (haT : a < T) :
    nullCapWeightCore T a (a * T) = 0 := by
  have hT : 0 < T := ha.trans haT
  rw [nullCapWeightCore_eq_log_ratio T a (a * T) (mul_pos ha hT)
    (mul_pos ha hT)]
  rw [div_self (mul_ne_zero ha.ne' hT.ne'), Real.log_one]
  field_simp
  ring

@[simp] theorem nullCapWeightExtension_zero (T a : ℝ) (haT : 0 ≤ a * T) :
    nullCapWeightExtension T a 0 = Real.pi / 4 * (a * (2 * T - a)) := by
  simp [nullCapWeightExtension, nullCapWeightCore, haT]

theorem nullCapWeightExtension_of_mem_Icc (T a σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) (a * T)) :
    nullCapWeightExtension T a σ = nullCapWeightCore T a σ := by
  rw [nullCapWeightExtension, max_eq_left hσ.1, min_eq_left hσ.2]

theorem nullCapWeightExtension_of_ge (T a σ : ℝ)
    (ha : 0 < a) (haT : a < T) (hσ : a * T ≤ σ) :
    nullCapWeightExtension T a σ = 0 := by
  have hT : 0 < T := ha.trans haT
  rw [nullCapWeightExtension, max_eq_left (mul_nonneg ha.le hT.le |>.trans hσ),
    min_eq_right hσ, nullCapWeightCore_cutoff T a ha haT]

theorem nullCapWeight_eq_extension_of_nonneg (T a σ : ℝ)
    (ha : 0 < a) (haT : a < T) (hσ : 0 ≤ σ) :
    nullCapWeight T a σ = nullCapWeightExtension T a σ := by
  have hT : 0 < T := ha.trans haT
  by_cases hs : σ < a * T
  · rw [nullCapWeight, if_pos ⟨hσ, hs⟩,
      nullCapWeightExtension_of_mem_Icc T a σ ⟨hσ, hs.le⟩]
  · rw [nullCapWeight_of_ge T a σ (not_lt.mp hs),
      nullCapWeightExtension_of_ge T a σ ha haT (not_lt.mp hs)]

theorem measurable_nullCapWeight (T a : ℝ) :
    Measurable (nullCapWeight T a) := by
  unfold nullCapWeight
  exact Measurable.ite measurableSet_Ico
    (continuous_nullCapWeightCore T a).measurable measurable_const

@[simp] theorem nullCapWeight_of_neg (T a σ : ℝ) (hσ : σ < 0) :
    nullCapWeight T a σ = 0 := by
  simp [nullCapWeight, not_le.mpr hσ]

theorem continuousWithinAt_nullCapWeight_zero (T a : ℝ)
    (ha : 0 < a) (haT : a < T) :
    ContinuousWithinAt (nullCapWeight T a) (Ici (0 : ℝ)) 0 := by
  apply (continuous_nullCapWeightExtension T a).continuousAt.continuousWithinAt.congr
  · intro σ hσ
    exact nullCapWeight_eq_extension_of_nonneg T a σ ha haT hσ
  · exact nullCapWeight_eq_extension_of_nonneg T a 0 ha haT le_rfl

/-- The global extension is bounded because its argument always lies in the
compact support interval. -/
theorem exists_norm_nullCapWeightExtension_le (T a : ℝ)
    (ha : 0 < a) (haT : a < T) :
    ∃ C : ℝ, ∀ σ : ℝ, ‖nullCapWeightExtension T a σ‖ ≤ C := by
  have hT : 0 < T := ha.trans haT
  have haT0 : 0 ≤ a * T := mul_nonneg ha.le hT.le
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (continuous_nullCapWeightCore T a).norm.continuousOn
  refine ⟨C, fun σ => ?_⟩
  unfold nullCapWeightExtension
  apply hC
  apply mem_image_of_mem (fun x => ‖nullCapWeightCore T a x‖)
  exact ⟨le_min (le_max_right _ _) haT0,
    min_le_right (max σ 0) (a * T)⟩

/-- Absolute integrability on the positive half-line follows from continuity
on `[0,aT]` and exact vanishing beyond the finite support. -/
theorem integrableOn_nullCapWeightExtension_mul (T a : ℝ)
    (ha : 0 < a) (haT : a < T) (f : ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn (fun σ => f σ * nullCapWeightExtension T a σ) (Ioi (0 : ℝ)) := by
  have hT : 0 < T := ha.trans haT
  have haT0 : 0 ≤ a * T := mul_nonneg ha.le hT.le
  have hc : IntegrableOn (fun σ => f σ * nullCapWeightExtension T a σ)
      (Ioc (0 : ℝ) (a * T)) :=
    ((hf.mul (continuous_nullCapWeightExtension T a)).intervalIntegrable 0 (a * T)).1
  have ht : IntegrableOn (fun σ => f σ * nullCapWeightExtension T a σ)
      (Ioi (a * T)) := by
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro σ hσ
    change 0 = f σ * nullCapWeightExtension T a σ
    rw [nullCapWeightExtension_of_ge T a σ ha haT hσ.le, mul_zero]
  simpa only [Ioc_union_Ioi_eq_Ioi haT0] using hc.union ht

/-- The exact coarea formula on a fixed positive half-line.  The interval
extension introduces only zeros and preserves the actual spacetime measure. -/
theorem integral_nullCap_eq_weightExtension (T a : ℝ)
    (ha : 0 < a) (haT : a < T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in nullCapRegion T a, f (intervalSq x 0)) =
      ∫ σ in Ioi (0 : ℝ), f σ * nullCapWeightExtension T a σ := by
  have hT : 0 < T := ha.trans haT
  have haT0 : 0 ≤ a * T := mul_nonneg ha.le hT.le
  rw [integral_nullCap_eq_weightCore T a ha haT f hf]
  have hsupport : (∫ σ in Ioi (0 : ℝ), f σ * nullCapWeightExtension T a σ) =
      ∫ σ in (0 : ℝ)..a * T, f σ * nullCapWeightExtension T a σ := by
    rw [intervalIntegral.integral_of_le haT0]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro σ hσ
    have hge : a * T ≤ σ := by
      by_contra h
      exact hσ.2 ⟨hσ.1, le_of_not_ge h⟩
    rw [nullCapWeightExtension_of_ge T a σ ha haT hge, mul_zero]
  rw [hsupport]
  apply intervalIntegral.integral_congr
  intro σ hσ
  have hσcc : σ ∈ Icc (0 : ℝ) (a * T) := by
    simpa [uIcc_of_le haT0] using hσ
  change f σ * nullCapWeightCore T a σ =
    f σ * nullCapWeightExtension T a σ
  rw [nullCapWeightExtension_of_mem_Icc T a σ hσcc]

/-- The geometric finite-support weight itself is absolutely integrable on the
positive half-line; this is not inferred merely from the closed formula. -/
theorem integrableOn_nullCapWeight_mul (T a : ℝ)
    (ha : 0 < a) (haT : a < T) (f : ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn (fun σ => f σ * nullCapWeight T a σ) (Ioi (0 : ℝ)) := by
  apply (integrableOn_nullCapWeightExtension_mul T a ha haT f hf).congr_fun ?_
    measurableSet_Ioi
  intro σ hσ
  change f σ * nullCapWeightExtension T a σ = f σ * nullCapWeight T a σ
  rw [nullCapWeight_eq_extension_of_nonneg T a σ ha haT hσ.le]

/-- Exact complete-interval cancellation for every point of the concrete cap.
The strict future-tip boundary has first been removed by the proved null-set
lemma; no missing interval reduction is encoded as a premise. -/
theorem nullCap_future_kernel_identity (T a ρ : ℝ)
    (hρ : 0 < ρ) (x : Spacetime) (hx : x ∈ nullCapRegion T a) :
    ρ * (∫ y in nullCapRegion T a ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
      1 - Real.exp (-(Real.pi / 24) * ρ * intervalSq x 0 ^ 2) := by
  rw [nullCap_complete_future T a x hx,
    integral_future_chronologicalPast_eq_causalInterval]
  exact causalInterval_kernel_identity ρ x 0 hρ hx.2.1

/-- The signed bilocal BDG expression cancels exactly to a positive spacetime
Gaussian at every positive density. -/
theorem nullCap_continuumMean_eq_spacetimeGaussian (T a ρ : ℝ)
    (ha : 0 < a) (haT : a < T) (hρ : 0 < ρ) :
    continuumMean ρ (nullCapRegion T a) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ x in nullCapRegion T a,
          Real.exp (-(Real.pi / 24) * ρ * intervalSq x 0 ^ 2) := by
  let M := nullCapRegion T a
  let E := fun x : Spacetime =>
    Real.exp (-(Real.pi / 24) * ρ * intervalSq x 0 ^ 2)
  let Q := fun x : Spacetime => ∫ y in M ∩ causalFuture x,
    bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)
  have hT : 0 < T := ha.trans haT
  have hm : MeasurableSet M := measurableSet_nullCapRegion T a
  have hE : Continuous E := by
    have hs : Continuous (fun x : Spacetime => intervalSq x 0) :=
      continuous_intervalSq.comp (continuous_id.prodMk continuous_const)
    dsimp [E]
    exact Real.continuous_exp.comp (by fun_prop)
  have hi1 : IntegrableOn (fun _ : Spacetime => (1 : ℝ)) M :=
    integrableOn_nullCapRegion T a hT _ continuous_const
  have hiE : IntegrableOn E M :=
    integrableOn_nullCapRegion T a hT E hE
  have hQ (x : Spacetime) (hx : x ∈ M) :
      Q x = (1 - E x) / ρ := by
    have h := nullCap_future_kernel_identity T a ρ hρ x hx
    dsimp only [M, Q, E] at h ⊢
    apply (eq_div_iff hρ.ne').mpr
    linarith
  have hinner : (∫ x in M, Q x) = ∫ x in M, (1 - E x) / ρ := by
    apply setIntegral_congr_fun hm
    exact hQ
  have hrho : ρ * (∫ x in M, (1 - E x) / ρ) =
      ∫ x in M, 1 - E x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hm
    intro x _
    field_simp
  change continuumMean ρ M =
    (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ x in M, E x
  unfold continuumMean
  change (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ _x in M, (1 : ℝ)) - ρ * ∫ x in M, Q x) = _
  rw [hinner, hrho, integral_sub hi1 hiE]
  ring

/-- Exact positive half-line Gaussian representation of the original
four-dimensional `continuumMean`. -/
theorem nullCap_continuumMean_eq_weightExtension (T a ρ : ℝ)
    (ha : 0 < a) (haT : a < T) (hρ : 0 < ρ) :
    continuumMean ρ (nullCapRegion T a) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ σ in Ioi (0 : ℝ),
          Real.exp (-(Real.pi / 24) * ρ * σ ^ 2) *
            nullCapWeightExtension T a σ := by
  rw [nullCap_continuumMean_eq_spacetimeGaussian T a ρ ha haT hρ]
  congr 1
  simpa only using integral_nullCap_eq_weightExtension T a ha haT
    (fun σ => Real.exp (-(Real.pi / 24) * ρ * σ ^ 2)) (by fun_prop)

/-- Proof term for the existing, unchanged deterministic null-cap target.
It asserts neither a Poisson expectation bridge nor an arbitrary-null-boundary
theorem. -/
theorem nullCapLimitGoal : NullCapLimitGoal := by
  intro T a ha haT
  obtain ⟨C, hC⟩ := exists_norm_nullCapWeightExtension_le T a ha haT
  have hlim := nullGaussian_density_limit (nullCapWeightExtension T a)
    (continuous_nullCapWeightExtension T a) C hC
  have hT : 0 < T := ha.trans haT
  rw [nullCapWeightExtension_zero T a (mul_nonneg ha.le hT.le),
    show 4 * (Real.pi / 4 * (a * (2 * T - a))) = nullJointArea T a by
      unfold nullJointArea
      ring] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (nullCap_continuumMean_eq_weightExtension T a ρ ha haT hρ).symm

end BoundaryDraft
