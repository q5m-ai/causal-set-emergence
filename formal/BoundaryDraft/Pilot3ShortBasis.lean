import BoundaryDraft.Pilot3NullCoordinates
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Exact three-dimensional sharp radial fibres

The four functions retain both moving-endpoint fractional powers. They vanish
outside the closed nonnegative cutoff interval. The integral identities use the
actual three-dimensional null Jacobian, not the four-dimensional radial measure.
-/

open MeasureTheory Set
open scoped Interval
noncomputable section
namespace BoundaryDraft
namespace Pilot3ShortBasis

/-- Constant radial fibre, without angular mass. -/
def F0 (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then δ / 4 + σ / (4 * δ) - σ ^ (1 / 2 : ℝ) / 2 else 0

/-- Time-linear radial fibre, without angular mass. -/
def Ftau (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then δ ^ 2 / 16 - σ / 8 + σ ^ 2 / (16 * δ ^ 2) else 0

/-- Time-square radial fibre, without angular mass. -/
def Ftt (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then
    δ ^ 3 / 48 + σ * δ / 16 + σ ^ 2 / (16 * δ) + σ ^ 3 / (48 * δ ^ 3) -
      σ ^ (3 / 2 : ℝ) / 6 else 0

/-- Radius-square radial fibre, without angular mass. -/
def Frr (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then
    δ ^ 3 / 48 - 3 * σ * δ / 16 - 3 * σ ^ 2 / (16 * δ) + σ ^ 3 / (48 * δ ^ 3) +
      σ ^ (3 / 2 : ℝ) / 3 else 0

@[simp] theorem F0_above {δ σ : ℝ} (h : δ ^ 2 < σ) : F0 δ σ = 0 := by
  simp [F0, not_le.mpr h]
@[simp] theorem Ftau_above {δ σ : ℝ} (h : δ ^ 2 < σ) : Ftau δ σ = 0 := by
  simp [Ftau, not_le.mpr h]
@[simp] theorem Ftt_above {δ σ : ℝ} (h : δ ^ 2 < σ) : Ftt δ σ = 0 := by
  simp [Ftt, not_le.mpr h]
@[simp] theorem Frr_above {δ σ : ℝ} (h : δ ^ 2 < σ) : Frr δ σ = 0 := by
  simp [Frr, not_le.mpr h]

theorem measurable_F0 (δ : ℝ) : Measurable (F0 δ) := by
  unfold F0
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

theorem measurable_Ftau (δ : ℝ) : Measurable (Ftau δ) := by
  unfold Ftau
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

theorem measurable_Ftt (δ : ℝ) : Measurable (Ftt δ) := by
  unfold Ftt
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

theorem measurable_Frr (δ : ℝ) : Measurable (Frr δ) := by
  unfold Frr
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

def primitive0 (σ v : ℝ) : ℝ := v / 4 + σ / 4 * v⁻¹

def primitiveTau (σ v : ℝ) : ℝ := v ^ 2 / 16 + σ ^ 2 / 16 * (v ^ 2)⁻¹

def primitiveTT (σ v : ℝ) : ℝ :=
  v ^ 3 / 48 + σ / 16 * v + σ ^ 2 / 16 * v⁻¹ + σ ^ 3 / 48 * (v ^ 3)⁻¹

def primitiveRR (σ v : ℝ) : ℝ :=
  v ^ 3 / 48 - 3 * σ / 16 * v - 3 * σ ^ 2 / 16 * v⁻¹ + σ ^ 3 / 48 * (v ^ 3)⁻¹

theorem hasDerivAt_primitive0 (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (primitive0 σ) (pilot3ShortNullJacobian v σ) v := by
  convert ((hasDerivAt_id v).div_const 4).add
    (((hasDerivAt_id v).inv hv.ne').const_mul (σ / 4)) using 1
  dsimp only [pilot3ShortNullJacobian, pilot3NullJacobian, id_eq]
  field_simp
  ring

theorem hasDerivAt_primitiveTau (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (primitiveTau σ) (pilot3ShortNullJacobian v σ * ((v + σ / v) / 2)) v := by
  convert (((hasDerivAt_id v).pow 2).div_const 16).add
    ((((hasDerivAt_id v).pow 2).inv (pow_ne_zero 2 hv.ne')).const_mul (σ ^ 2 / 16)) using 1
  dsimp only [pilot3ShortNullJacobian, pilot3NullJacobian, id_eq]
  field_simp
  ring

theorem hasDerivAt_primitiveTT (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (primitiveTT σ) (pilot3ShortNullJacobian v σ * ((v + σ / v) / 2) ^ 2) v := by
  convert (((((hasDerivAt_id v).pow 3).div_const 48).add
    ((hasDerivAt_id v).const_mul (σ / 16))).add
      (((hasDerivAt_id v).inv hv.ne').const_mul (σ ^ 2 / 16))).add
        ((((hasDerivAt_id v).pow 3).inv (pow_ne_zero 3 hv.ne')).const_mul (σ ^ 3 / 48)) using 1
  dsimp only [pilot3ShortNullJacobian, pilot3NullJacobian, id_eq]
  field_simp
  ring

theorem hasDerivAt_primitiveRR (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (primitiveRR σ) (pilot3ShortNullJacobian v σ * ((v - σ / v) / 2) ^ 2) v := by
  convert (((((hasDerivAt_id v).pow 3).div_const 48).sub
    ((hasDerivAt_id v).const_mul (3 * σ / 16))).sub
      (((hasDerivAt_id v).inv hv.ne').const_mul (3 * σ ^ 2 / 16))).add
        ((((hasDerivAt_id v).pow 3).inv (pow_ne_zero 3 hv.ne')).const_mul (σ ^ 3 / 48)) using 1
  dsimp only [pilot3ShortNullJacobian, pilot3NullJacobian, id_eq]
  field_simp
  ring

/-- The lower endpoint in the constant mode is nonzero. -/
theorem primitive0_sqrt {σ : ℝ} (hσ : 0 < σ) :
    primitive0 σ (Real.sqrt σ) = σ ^ (1 / 2 : ℝ) / 2 := by
  rw [← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt hσ.le
  have hn := (Real.sqrt_pos.mpr hσ).ne'
  unfold primitive0
  field_simp
  nlinarith

theorem primitiveTau_sqrt {σ : ℝ} (hσ : 0 < σ) :
    primitiveTau σ (Real.sqrt σ) = σ / 8 := by
  rw [primitiveTau, Real.sq_sqrt hσ.le]
  field_simp
  ring

/-- The lower endpoint is exactly the critical fractional power. -/
theorem primitiveTT_sqrt {σ : ℝ} (hσ : 0 < σ) :
    primitiveTT σ (Real.sqrt σ) = σ ^ (3 / 2 : ℝ) / 6 := by
  have hp : σ ^ (3 / 2 : ℝ) = Real.sqrt σ ^ 3 :=
    (Real.rpow_div_two_eq_sqrt 3 hσ.le).trans (Real.rpow_natCast _ 3)
  rw [hp]
  have hs := Real.sq_sqrt hσ.le
  have hn := (Real.sqrt_pos.mpr hσ).ne'
  unfold primitiveTT
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg σ)]
  ring

theorem primitiveRR_sqrt {σ : ℝ} (hσ : 0 < σ) :
    primitiveRR σ (Real.sqrt σ) = -(σ ^ (3 / 2 : ℝ)) / 3 := by
  have hp : σ ^ (3 / 2 : ℝ) = Real.sqrt σ ^ 3 :=
    (Real.rpow_div_two_eq_sqrt 3 hσ.le).trans (Real.rpow_natCast _ 3)
  rw [hp]
  have hs := Real.sq_sqrt hσ.le
  have hn := (Real.sqrt_pos.mpr hσ).ne'
  unfold primitiveRR
  field_simp
  rw [← hs]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg σ)]
  ring

private theorem positive_interval {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) {v : ℝ} (hv : v ∈ uIcc (Real.sqrt σ) δ) : 0 < v := by
  rw [uIcc_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hs⟩)] at hv
  exact (Real.sqrt_pos.mpr hσ).trans_le hv.1

private theorem continuous_fibre {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) :
    ContinuousOn (fun v => pilot3ShortNullJacobian v σ) (uIcc (Real.sqrt σ) δ) ∧
    ContinuousOn (fun v => (v + σ / v) / 2) (uIcc (Real.sqrt σ) δ) ∧
    ContinuousOn (fun v => (v - σ / v) / 2) (uIcc (Real.sqrt σ) δ) := by
  have hn (v : ℝ) (hv : v ∈ uIcc (Real.sqrt σ) δ) : v ≠ 0 :=
    (positive_interval hδ hσ hs hv).ne'
  refine ⟨?_, ?_, ?_⟩
  · exact (continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun v hv => pow_ne_zero 2 (hn v hv)))).div_const 4
  · exact (continuousOn_id.add (continuousOn_const.div continuousOn_id hn)).div_const 2
  · exact (continuousOn_id.sub (continuousOn_const.div continuousOn_id hn)).div_const 2

/-- Exact constant fibre, including zero and the cutoff endpoint. -/
theorem F0_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ ≤ δ ^ 2) :
    F0 δ σ = ∫ v in (Real.sqrt σ)..δ, pilot3ShortNullJacobian v σ := by
  rcases eq_or_lt_of_le hσ with hσ | hσ
  · subst σ
    simp [F0, pilot3ShortNullJacobian, pilot3NullJacobian, sq_nonneg δ, div_eq_mul_inv]
  · have hc := (continuous_fibre hδ hσ hs).1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hasDerivAt_primitive0 σ (positive_interval hδ hσ hs hv)) hc.intervalIntegrable,
      primitive0_sqrt hσ, F0, if_pos ⟨hσ.le, hs⟩, primitive0]
    ring

/-- Exact time-linear fibre; its lower-endpoint term is retained. -/
theorem Ftau_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ ≤ δ ^ 2) :
    Ftau δ σ = ∫ v in (Real.sqrt σ)..δ, pilot3ShortNullJacobian v σ * ((v + σ / v) / 2) := by
  rcases eq_or_lt_of_le hσ with hσ | hσ
  · subst σ
    have he (v : ℝ) : pilot3ShortNullJacobian v 0 * ((v + 0 / v) / 2) = v / 8 := by
      simp [pilot3ShortNullJacobian, pilot3NullJacobian]
      ring
    simp_rw [he]
    rw [Real.sqrt_zero, intervalIntegral.integral_div, integral_id]
    simp [Ftau, sq_nonneg δ]
    ring
  · have hc := continuous_fibre hδ hσ hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hasDerivAt_primitiveTau σ (positive_interval hδ hσ hs hv))
        (hc.1.mul hc.2.1).intervalIntegrable,
      primitiveTau_sqrt hσ, Ftau, if_pos ⟨hσ.le, hs⟩, primitiveTau]
    ring

/-- Exact time-square fibre, with its nonzero three-halves lower endpoint. -/
theorem Ftt_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ ≤ δ ^ 2) :
    Ftt δ σ = ∫ v in (Real.sqrt σ)..δ, pilot3ShortNullJacobian v σ * ((v + σ / v) / 2) ^ 2 := by
  rcases eq_or_lt_of_le hσ with hσ | hσ
  · subst σ
    have he (v : ℝ) : pilot3ShortNullJacobian v 0 * ((v + 0 / v) / 2) ^ 2 = v ^ 2 / 16 := by
      simp [pilot3ShortNullJacobian, pilot3NullJacobian]
      ring
    simp_rw [he]
    rw [Real.sqrt_zero, intervalIntegral.integral_div, integral_pow]
    simp [Ftt, sq_nonneg δ, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    ring
  · have hc := continuous_fibre hδ hσ hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hasDerivAt_primitiveTT σ (positive_interval hδ hσ hs hv))
        (hc.1.mul (hc.2.1.pow 2)).intervalIntegrable,
      primitiveTT_sqrt hσ, Ftt, if_pos ⟨hσ.le, hs⟩, primitiveTT]
    ring

/-- Exact radius-square fibre, with its nonzero three-halves lower endpoint. -/
theorem Frr_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hs : σ ≤ δ ^ 2) :
    Frr δ σ = ∫ v in (Real.sqrt σ)..δ, pilot3ShortNullJacobian v σ * ((v - σ / v) / 2) ^ 2 := by
  rcases eq_or_lt_of_le hσ with hσ | hσ
  · subst σ
    have he (v : ℝ) : pilot3ShortNullJacobian v 0 * ((v - 0 / v) / 2) ^ 2 = v ^ 2 / 16 := by
      simp [pilot3ShortNullJacobian, pilot3NullJacobian]
      ring
    simp_rw [he]
    rw [Real.sqrt_zero, intervalIntegral.integral_div, integral_pow]
    simp [Frr, sq_nonneg δ, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    ring
  · have hc := continuous_fibre hδ hσ hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hasDerivAt_primitiveRR σ (positive_interval hδ hσ hs hv))
        (hc.1.mul (hc.2.2.pow 2)).intervalIntegrable,
      primitiveRR_sqrt hσ, Frr, if_pos ⟨hσ.le, hs⟩, primitiveRR]
    ring

/-- All four fibres vanish exactly at the sharp cutoff square. -/
theorem at_cutoff {δ : ℝ} (hδ : 0 < δ) :
    F0 δ (δ ^ 2) = 0 ∧ Ftau δ (δ ^ 2) = 0 ∧ Ftt δ (δ ^ 2) = 0 ∧ Frr δ (δ ^ 2) = 0 := by
  rw [F0_eq_integral hδ (sq_nonneg _) le_rfl,
    Ftau_eq_integral hδ (sq_nonneg _) le_rfl,
    Ftt_eq_integral hδ (sq_nonneg _) le_rfl,
    Frr_eq_integral hδ (sq_nonneg _) le_rfl, Real.sqrt_sq hδ.le]
  simp

/-- Independent check of the time-square/radius-square signs. -/
theorem Ftt_eq_Frr_add (δ σ : ℝ) : Ftt δ σ = Frr δ σ + σ * F0 δ σ := by
  by_cases hs : 0 ≤ σ ∧ σ ≤ δ ^ 2
  · rw [Ftt, Frr, F0, if_pos hs, if_pos hs, if_pos hs]
    have hp : σ ^ (3 / 2 : ℝ) = σ * σ ^ (1 / 2 : ℝ) := by
      conv_rhs => lhs; rw [← Real.rpow_one σ]
      rw [← Real.rpow_add' hs.1 (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]
      norm_num
    rw [hp]
    ring
  · simp [Ftt, Frr, F0, hs]

end Pilot3ShortBasis
end BoundaryDraft
