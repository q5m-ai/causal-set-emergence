import BoundaryDraft.ThinTorusLimit
import BoundaryDraft.ThinTorusGeometry
import BoundaryDraft.MeasuredOrderBDG4Compatibility
import BoundaryDraft.TwoFaceLimit
import Mathlib.Data.Real.Pi.Bounds

/-! Standalone expanded contracts and nonvacuous quotient/seam regressions. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace BoundaryDraft.ThinTorusRegression

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- The actual quotient observable, both measures, all causal partners and the
-- actual restricted interval volume occur explicitly in this conclusion.
example (L T : ℝ) [Fact (0 < L)] (hT : 0 < T) (hthin : 2 * T < L) :
    Tendsto (fun ρ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (T * L ^ 3 - ρ * ∫ x, ∫ y in {y | (CompactTorus.measuredOrder L).Rel x y},
        bdgKernel (ρ * (CompactTorus.slabVolume L T ((CompactTorus.measuredOrder L).interval x y)).toReal)
          ∂CompactTorus.slabVolume L T ∂CompactTorus.slabVolume L T)) atTop (𝓝 0) := by
  have h := CompactTorus.action_limit L hT hthin
  simpa only [MeasuredOrderBDG4.action_eq, CompactTorus.slabVolume_univ,
    ENNReal.toReal_ofReal (mul_nonneg hT.le (pow_nonneg (le_of_lt (Fact.out : 0 < L)) 3))] using h

example (L T : ℝ) [Fact (0 < L)] (hT : 0 < T) (hthin : 2 * T < L) :
    Tendsto (fun ρ => ∫ c, MeasuredOrderBDG4.discreteAction (CompactTorus.measuredOrder L) ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • CompactTorus.slabVolume L T)) atTop (𝓝 0) :=
  CompactTorus.expectedAction_limit L hT hthin

-- Fixed nonempty positive-volume instance; neither target zero nor empty joint
-- sets the finite-density observable to zero by definition.
example : CompactTorus.slabVolume 1 (2 / 5) univ = ENNReal.ofReal (2 / 5) := by
  rw [CompactTorus.slabVolume_univ]
  norm_num

example : CompactTorus.pastFace 1 (2 / 5) ∩ CompactTorus.futureFace 1 (2 / 5) = ∅ :=
  CompactTorus.joint_empty 1 (by norm_num)

example : CompactTorus.scalarCurvature 1 (0, 0, 0, 0) = 0 := CompactTorus.scalarCurvature_zero _ _

example : Tendsto (fun ρ => MeasuredOrderBDG4.action (CompactTorus.measuredOrder 1)
    (CompactTorus.slabVolume 1 (2 / 5)) ρ) atTop (𝓝 0) :=
  CompactTorus.action_limit 1 (by norm_num) (by norm_num)

def seamPast : ℝ × CompactTorus.Space 1 := (-3 / 20, ((9 / 10 : ℝ), 0, 0))
def seamFuture : ℝ × CompactTorus.Space 1 := (3 / 20, ((1 / 10 : ℝ), 0, 0))

theorem seam_distance : (CompactTorus.spatialDistance 1).distance seamPast.2 seamFuture.2 = 1 / 5 := by
  rw [CompactTorus.distance_eq]
  have hd : dist ((9 / 10 : ℝ) : AddCircle (1 : ℝ)) ((1 / 10 : ℝ) : AddCircle (1 : ℝ)) = 1 / 5 := by
    rw [CompactTorus.circle_distance_lifts]
    norm_num [round, Int.fract, Int.floor_eq_iff, abs_div]
  simp only [seamPast, seamFuture, hd, dist_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact Real.sqrt_sq (by norm_num)

theorem seam_related : (CompactTorus.measuredOrder 1).Rel seamPast seamFuture := by
  change (CompactTorus.spatialDistance 1).distance seamPast.2 seamFuture.2 ≤ _
  rw [seam_distance]
  norm_num [seamPast, seamFuture]

example : ¬ |(1 / 10 : ℝ) - 9 / 10| ≤ seamFuture.1 - seamPast.1 := by
  norm_num [seamPast, seamFuture, abs_div]

example : CompactTorus.slabVolume 1 (2 / 5) ((CompactTorus.measuredOrder 1).interval seamPast seamFuture) =
    ENNReal.ofReal (Real.pi / 9600) := by
  rw [CompactTorus.intervalVolume_thin 1 (by norm_num : 2 * (2 / 5 : ℝ) < 1)
    (by norm_num [seamPast, CompactTorus.slab, Ultrastatic.slab])
    (by norm_num [seamFuture, CompactTorus.slab, Ultrastatic.slab]) seam_related, seam_distance]
  congr 1
  norm_num [seamPast, seamFuture]
  ring

-- Full finite-density reduction, including its physical point subtraction.
example (ρ : ℝ) : MeasuredOrderBDG4.action (CompactTorus.measuredOrder 1)
    (CompactTorus.slabVolume 1 (2 / 5)) ρ = planeKernel ρ (2 / 5) := by
  simpa using CompactTorus.action_eq_planeKernel 1 (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num) ρ

example (ρ : ℝ) :
    (∫ x, ∫ y in {y | (CompactTorus.measuredOrder 1).Rel x y},
      bdgKernel (ρ * (CompactTorus.slabVolume 1 (2 / 5)
        ((CompactTorus.measuredOrder 1).interval x y)).toReal)
      ∂CompactTorus.slabVolume 1 (2 / 5) ∂CompactTorus.slabVolume 1 (2 / 5)) =
    ∫ w in (0 : ℝ)..(2 / 5 : ℝ) ^ 2,
      CompactTorus.phaseAmplitude (2 / 5) w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2) := by
  simpa using CompactTorus.pair_integral_phase 1 (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num) ρ

-- Every signed moment and the logarithmic response retain their original signs.
example : (∫ z : ℝ in Ioi 0, bdgKernel (z ^ 2)) = 0 := integral_bdgKernel_transverse_zero
example : (∫ z : ℝ in Ioi 0, z * bdgKernel (z ^ 2)) = 0 := integral_bdgKernel_transverse_one
example : (∫ z : ℝ in Ioi 0, z ^ 2 * bdgKernel (z ^ 2)) = 0 := integral_bdgKernel_transverse_two
example : (∫ z : ℝ in Ioi 0, z * Real.log z * bdgKernel (z ^ 2)) = 1 / 12 :=
  integral_bdgKernel_transverse_log_one
example (L T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ * (L ^ 3 * T - ρ * L ^ 3 *
      ∫ w : ℝ in Ioi 0, CompactTorus.phaseLog T w * bdgKernel ((Real.pi / 24) * ρ * w ^ 2)) = 0 :=
  CompactTorus.phaseLog_point_cancellation L T hρ

-- Four ordered terms for a duplicated smooth partition; point weights sum to
-- one, not two, and each off-diagonal term is a quarter of the ACTUAL pair.
def fullPair (ρ : ℝ) : ℝ := ∫ x, ∫ y in {y | (CompactTorus.measuredOrder 1).Rel x y},
  bdgKernel (ρ * (CompactTorus.slabVolume 1 (2 / 5)
    ((CompactTorus.measuredOrder 1).interval x y)).toReal)
    ∂CompactTorus.slabVolume 1 (2 / 5) ∂CompactTorus.slabVolume 1 (2 / 5)

def partitionPair (ρ : ℝ) (_i _j : Fin 2) : ℝ := ∫ x, ∫ y in {y | (CompactTorus.measuredOrder 1).Rel x y},
  ((1 / 2 : ℝ) * (1 / 2)) * bdgKernel (ρ * (CompactTorus.slabVolume 1 (2 / 5)
    ((CompactTorus.measuredOrder 1).interval x y)).toReal)
    ∂CompactTorus.slabVolume 1 (2 / 5) ∂CompactTorus.slabVolume 1 (2 / 5)

theorem partitionPair_eq (ρ : ℝ) (i j : Fin 2) : partitionPair ρ i j = (1 / 4) * fullPair ρ := by
  simp only [partitionPair, integral_const_mul, fullPair]
  ring

example (ρ : ℝ) : (∑ i : Fin 2, ∑ j : Fin 2, partitionPair ρ i j) = fullPair ρ := by
  simp [partitionPair_eq, Fin.sum_univ_two]
  ring

example : (∑ _i : Fin 2, ∑ _j : Fin 2, (1 / 2 : ℝ) * (1 / 2)) = 1 := by norm_num

private theorem kernel_pos {z : ℝ} (hz' : z ≤ 1 / 16) : 0 < bdgKernel z := by
  apply mul_pos _ (Real.exp_pos _)
  unfold bdgPolynomial
  have hc : 0 ≤ z ^ 2 * (1 - z) := mul_nonneg (sq_nonneg z) (by linarith)
  nlinarith [sq_nonneg z]

private theorem slice_arg_le {τ r : ℝ} (hτ : τ ∈ Icc 0 (2 / 5 : ℝ)) (hr : r ∈ Icc 0 τ) :
    (Real.pi / 24) * (τ ^ 2 - r ^ 2) ^ 2 ≤ 1 / 16 := by
  have ht : τ ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hτ.1 hτ.2 2
  have hrt : r ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
  have hs : (τ ^ 2 - r ^ 2) ^ 2 ≤ (4 / 25 : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (sub_nonneg.mpr hrt) (by nlinarith [sq_nonneg r])
  nlinarith [Real.pi_pos, Real.pi_lt_four, sq_nonneg (τ ^ 2 - r ^ 2),
    mul_nonneg (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four]) (sq_nonneg (τ ^ 2 - r ^ 2))]

private theorem slice_kernel_pos {τ r : ℝ} (hτ : τ ∈ Icc 0 (2 / 5 : ℝ)) (hr : r ∈ Icc 0 τ) :
    0 < bdgKernel ((Real.pi / 24) * (τ ^ 2 - r ^ 2) ^ 2) := kernel_pos (slice_arg_le hτ hr)

private theorem kernel_le_one {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1 / 16) : bdgKernel z ≤ 1 := by
  have hp : bdgPolynomial z ≤ 1 := by
    unfold bdgPolynomial
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hz'), pow_nonneg hz 3]
  exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-z)).le).trans
    (by simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz))

theorem fullPair_pos : 0 < fullPair 1 := by
  have hs (τ : ℝ) (hτ : τ ∈ Icc 0 (2 / 5 : ℝ)) : 0 ≤ coneRadialSlice 1 τ := by
    rw [coneRadialSlice_eq_radial]
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg hτ.1
    intro r hr
    simp only [mul_one]
    exact mul_nonneg (sq_nonneg r) (slice_kernel_pos hτ hr).le
  have hsp : 0 < coneRadialSlice 1 (1 / 5) := by
    rw [coneRadialSlice_eq_radial]
    apply mul_pos (by positivity)
    apply intervalIntegral.integral_pos (by norm_num)
      (by unfold bdgKernel bdgPolynomial; fun_prop)
    · intro r hr
      simp only [mul_one]
      exact mul_nonneg (sq_nonneg r) (slice_kernel_pos (by norm_num) ⟨hr.1.le, hr.2⟩).le
    · refine ⟨1 / 10, by norm_num, ?_⟩
      simp only [mul_one]
      exact mul_pos (by norm_num) (slice_kernel_pos (by norm_num) (by norm_num))
  have ht : 0 < ∫ τ in (0 : ℝ)..(2 / 5 : ℝ), (2 / 5 - τ) * coneRadialSlice 1 τ := by
    apply intervalIntegral.integral_pos (by norm_num)
      (((continuous_const.sub continuous_id).mul (continuous_coneRadialSlice 1)).continuousOn)
    · intro τ hτ
      exact mul_nonneg (sub_nonneg.mpr hτ.2) (hs τ ⟨hτ.1.le, hτ.2⟩)
    · exact ⟨1 / 5, by norm_num, mul_pos (by norm_num) hsp⟩
  rw [fullPair, CompactTorus.pair_integral_radial 1 (by norm_num) (by norm_num)]
  simp only [one_pow, one_mul]
  simp_rw [coneRadialSlice_eq_radial] at ht
  convert ht using 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro τ _
  ring

example : 0 < partitionPair 1 0 1 := by rw [partitionPair_eq]; exact mul_pos (by norm_num) fullPair_pos
example : 0 < partitionPair 1 1 0 := by rw [partitionPair_eq]; exact mul_pos (by norm_num) fullPair_pos

-- A genuinely nonzero canonical finite-density action at positive density.
theorem finite_action_pos : 0 < MeasuredOrderBDG4.action (CompactTorus.measuredOrder 1)
    (CompactTorus.slabVolume 1 (2 / 5)) 1 := by
  let F : ℝ → ℝ := fun τ => ∫ r in (0 : ℝ)..τ,
    r ^ 2 * bdgKernel ((Real.pi / 24) * (τ ^ 2 - r ^ 2) ^ 2)
  have hc : Continuous F := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (by unfold bdgKernel bdgPolynomial; fun_prop) continuous_id
  have hb (τ : ℝ) (hτ : τ ∈ Icc 0 (2 / 5 : ℝ)) : F τ ≤ 8 / 125 := by
    have hle : F τ ≤ ∫ _r in (0 : ℝ)..τ, (4 / 25 : ℝ) := by
      apply intervalIntegral.integral_mono_on hτ.1
        ((show Continuous (fun r : ℝ => r ^ 2 * bdgKernel ((Real.pi / 24) * (τ ^ 2 - r ^ 2) ^ 2)) by
          unfold bdgKernel bdgPolynomial; fun_prop).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro r hr
      have hk := kernel_le_one (by positivity) (slice_arg_le hτ hr)
      have hrT : r ≤ (2 / 5 : ℝ) := hr.2.trans hτ.2
      calc
        _ ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hk (sq_nonneg r)
        _ ≤ 4 / 25 := by nlinarith [pow_le_pow_left₀ hr.1 hrT 2]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
    nlinarith [hτ.2]
  have hb' : (∫ τ in (0 : ℝ)..(2 / 5 : ℝ), (2 / 5 - τ) * F τ) ≤ 32 / 3125 := by
    have hle : (∫ τ in (0 : ℝ)..(2 / 5 : ℝ), (2 / 5 - τ) * F τ) ≤
        ∫ _τ in (0 : ℝ)..(2 / 5 : ℝ), (16 / 625 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (((continuous_const.sub continuous_id).mul hc).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro τ hτ
      calc
        _ ≤ (2 / 5 - τ) * (8 / 125) := mul_le_mul_of_nonneg_left (hb τ hτ) (sub_nonneg.mpr hτ.2)
        _ ≤ 16 / 625 := by nlinarith [hτ.1]
    norm_num only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
    exact hle
  have hfull : fullPair 1 < 2 / 5 := by
    rw [fullPair, CompactTorus.pair_integral_radial 1 (by norm_num) (by norm_num)]
    simp only [one_pow, one_mul, mul_one]
    have hle := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 4 * Real.pi)
    change 4 * Real.pi * _ ≤ _ at hle
    nlinarith [Real.pi_lt_four]
  rw [MeasuredOrderBDG4.action_eq, CompactTorus.slabVolume_univ]
  norm_num only [one_pow, mul_one, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 / 5),
    Real.sqrt_one, one_mul]
  exact mul_pos (by positivity) (sub_pos.mpr (by simpa only [fullPair, one_mul] using hfull))

-- Old coordinate and two-face contracts are unchanged.
example {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset Spacetime) :
    MeasuredOrderBDG4.discreteAction MeasuredOrderBDG4.coordinateOrder ρ c = discreteBDGAction ρ c :=
  MeasuredOrderBDG4.coordinate_discreteAction hρ c
example : TwoFaceLimitGoal := twoFaceLimitGoal
example : TwoFaceExpectedLimitGoal := twoFaceExpectedLimitGoal

end BoundaryDraft.ThinTorusRegression
