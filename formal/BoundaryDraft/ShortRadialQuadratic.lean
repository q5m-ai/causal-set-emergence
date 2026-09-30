import BoundaryDraft.NullCubicRemainder
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# The radial quadratic short-displacement density

This is the one universal basis response left after subtracting the planar cap
with the same height. The density retains the sharp long-coordinate cutoff.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- The radial-square term after angular averaging, before the signed kernel. -/
def shortRadialQuadratic (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then
    δ ^ 4 / 128 - σ * δ ^ 2 / 16 + 3 * σ ^ 2 / 16 * Real.log δ +
      σ ^ 3 / (16 * δ ^ 2) - σ ^ 4 / (128 * δ ^ 4) -
        3 * σ ^ 2 / 32 * Real.log σ
  else 0

/-- An explicit antiderivative on the positive long-coordinate axis. -/
def shortRadialQuadraticPrimitive (σ v : ℝ) : ℝ :=
  v ^ 4 / 128 - σ / 16 * v ^ 2 + (3 * σ ^ 2 / 16) * Real.log v +
    (σ ^ 3 / 16) * (v ^ 2)⁻¹ - (σ ^ 4 / 128) * (v ^ 4)⁻¹

theorem hasDerivAt_shortRadialQuadraticPrimitive (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (shortRadialQuadraticPrimitive σ)
      ((v - σ / v) ^ 4 / (32 * v)) v := by
  have ha := (((hasDerivAt_id v).pow 4).div_const 128).sub
    (((hasDerivAt_id v).pow 2).const_mul (σ / 16))
  have hb := ha.add ((Real.hasDerivAt_log hv.ne').const_mul (3 * σ ^ 2 / 16))
  have hd := (hb.add ((((hasDerivAt_id v).pow 2).inv (pow_ne_zero 2 hv.ne')).const_mul
    (σ ^ 3 / 16))).sub
      ((((hasDerivAt_id v).pow 4).inv (pow_ne_zero 4 hv.ne')).const_mul (σ ^ 4 / 128))
  convert hd using 1
  dsimp only [id_eq]
  field_simp [hv.ne']
  ring

/-- The lower endpoint supplies the logarithm; its other four terms cancel. -/
theorem shortRadialQuadraticPrimitive_sqrt {σ : ℝ} (hσ : 0 < σ) :
    shortRadialQuadraticPrimitive σ (Real.sqrt σ) = 3 * σ ^ 2 / 32 * Real.log σ := by
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hs2 := Real.sq_sqrt hσ.le
  have hs4 : Real.sqrt σ ^ 4 = σ ^ 2 := by nlinarith only [congrArg (fun x : ℝ => x ^ 2) hs2]
  rw [shortRadialQuadraticPrimitive, hs4, hs2, Real.log_sqrt hσ.le]
  field_simp [hσ.ne']
  ring

/-- Exact integration of the original Jacobian times the squared radius. -/
theorem shortRadialQuadratic_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) :
    shortRadialQuadratic δ σ = ∫ v in (Real.sqrt σ)..δ,
      ((v - σ / v) ^ 2 / (8 * v)) * ((v - σ / v) / 2) ^ 2 := by
  have hroot : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hrootδ : Real.sqrt σ ≤ δ := (Real.sqrt_le_iff).mpr ⟨hδ.le, hs⟩
  have hv (v : ℝ) (hv : v ∈ uIcc (Real.sqrt σ) δ) : 0 < v := by
    rw [uIcc_of_le hrootδ] at hv
    exact hroot.trans_le hv.1
  have hc : ContinuousOn (fun v : ℝ => (v - σ / v) ^ 4 / (32 * v))
      (uIcc (Real.sqrt σ) δ) :=
    ((continuousOn_id.sub (continuousOn_const.div continuousOn_id
      (fun v hv' => (hv v hv').ne'))).pow 4).div
        (continuousOn_const.mul continuousOn_id) (fun v hv' => mul_ne_zero (by norm_num) (hv v hv').ne')
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv' => hasDerivAt_shortRadialQuadraticPrimitive σ (hv v hv')) hc.intervalIntegrable
  have he (v : ℝ) : (v - σ / v) ^ 2 / (8 * v) * ((v - σ / v) / 2) ^ 2 =
      (v - σ / v) ^ 4 / (32 * v) := by ring
  simp_rw [he]
  rw [hi, shortRadialQuadraticPrimitive_sqrt hσ, shortRadialQuadratic,
    if_pos ⟨hσ.le, hs⟩, shortRadialQuadraticPrimitive]
  ring

theorem measurable_shortRadialQuadratic (δ : ℝ) : Measurable (shortRadialQuadratic δ) := by
  unfold shortRadialQuadratic
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

/-- The full polynomial/logarithmic model, without the artificial upper
cutoff. Its difference from the actual density is globally cubic. -/
def shortRadialQuadraticModel (δ σ : ℝ) : ℝ :=
  δ ^ 4 / 128 + (-δ ^ 2 / 16) * σ + (3 / 16 * Real.log δ) * σ ^ 2 +
    (-3 / 32) * (σ ^ 2 * Real.log σ)

private theorem abs_log_div_bound {q s : ℝ} (hq : 0 < q) (hs : q ≤ s) :
    |Real.log s| / s ≤ 1 + 1 / q ^ 2 := by
  have hs0 := hq.trans_le hs
  have hl : |Real.log s| ≤ s + s⁻¹ := by
    have hu := Real.log_le_sub_one_of_pos hs0
    have hd := Real.log_le_sub_one_of_pos (inv_pos.mpr hs0)
    rw [Real.log_inv] at hd
    apply abs_le.mpr
    constructor <;> linarith [inv_pos.mpr hs0]
  calc
    _ ≤ (s + s⁻¹) / s := div_le_div_of_nonneg_right hl hs0.le
    _ = 1 + 1 / s ^ 2 := by field_simp; ring
    _ ≤ 1 + 1 / q ^ 2 := by gcongr

private theorem polynomial_log_bound {q s : ℝ} (hq : 0 < q) (hs : q ≤ s)
    (a b d L : ℝ) :
    |a + b * s + d * s ^ 2 + L * (s ^ 2 * Real.log s)| ≤
      (|a| / q ^ 3 + |b| / q ^ 2 + |d| / q + |L| * (1 + 1 / q ^ 2)) * s ^ 3 := by
  have hs0 := hq.trans_le hs
  apply (div_le_iff₀ (pow_pos hs0 3)).mp
  have he : (a + b * s + d * s ^ 2 + L * (s ^ 2 * Real.log s)) / s ^ 3 =
      a / s ^ 3 + b / s ^ 2 + d / s + L * (Real.log s / s) := by
    field_simp
    ring
  rw [← abs_of_pos (pow_pos hs0 3), ← abs_div, he]
  calc
    _ ≤ |a / s ^ 3| + |b / s ^ 2| + |d / s| + |L * (Real.log s / s)| := by
      exact (abs_add _ _).trans (add_le_add_right
        ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)
    _ = |a| / s ^ 3 + |b| / s ^ 2 + |d| / s + |L| * (|Real.log s| / s) := by
      rw [abs_div, abs_div, abs_div, abs_mul, abs_div,
        abs_of_pos (pow_pos hs0 3), abs_of_nonneg (sq_nonneg s), abs_of_pos hs0]
    _ ≤ |a| / q ^ 3 + |b| / q ^ 2 + |d| / q + |L| * (1 + 1 / q ^ 2) := by
      gcongr
      exact abs_log_div_bound hq hs

/-- All fixed-cutoff tails, including the logarithm and the subtracted
quadratic polynomial, are controlled by the third absolute moment. -/
theorem shortRadialQuadratic_model_cubic_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ σ, 0 < σ →
      ‖shortRadialQuadratic δ σ - shortRadialQuadraticModel δ σ‖ ≤ C * σ ^ 3 := by
  let Cnear := |1 / (16 * δ ^ 2)| + |-(1 / (128 * δ ^ 4))| * δ ^ 2
  let Cfar := |δ ^ 4 / 128| / (δ ^ 2) ^ 3 + |-δ ^ 2 / 16| / (δ ^ 2) ^ 2 +
    |3 / 16 * Real.log δ| / (δ ^ 2) + |(-3 / 32 : ℝ)| * (1 + 1 / (δ ^ 2) ^ 2)
  refine ⟨max Cnear Cfar, fun σ hσ => ?_⟩
  by_cases hs : σ ≤ δ ^ 2
  · have he : shortRadialQuadratic δ σ - shortRadialQuadraticModel δ σ =
        (1 / (16 * δ ^ 2)) * σ ^ 3 + (-(1 / (128 * δ ^ 4))) * σ ^ 4 := by
      rw [shortRadialQuadratic, if_pos ⟨hσ.le, hs⟩, shortRadialQuadraticModel]
      ring
    rw [he, Real.norm_eq_abs]
    calc
      _ ≤ |1 / (16 * δ ^ 2) * σ ^ 3| + |-(1 / (128 * δ ^ 4)) * σ ^ 4| := abs_add _ _
      _ = |1 / (16 * δ ^ 2)| * σ ^ 3 + |-(1 / (128 * δ ^ 4))| * σ * σ ^ 3 := by
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos hσ 3), abs_of_pos (pow_pos hσ 4)]
        ring
      _ ≤ |1 / (16 * δ ^ 2)| * σ ^ 3 + |-(1 / (128 * δ ^ 4))| * δ ^ 2 * σ ^ 3 := by
        gcongr
      _ = Cnear * σ ^ 3 := by dsimp only [Cnear]; ring
      _ ≤ max Cnear Cfar * σ ^ 3 := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hσ.le _)
  · rw [shortRadialQuadratic, if_neg (by simp [hs]), zero_sub, norm_neg, Real.norm_eq_abs]
    exact (polynomial_log_bound (sq_pos_of_pos hδ) (le_of_not_ge hs)
      (δ ^ 4 / 128) (-δ ^ 2 / 16) (3 / 16 * Real.log δ) (-3 / 32)).trans
        (mul_le_mul_of_nonneg_right (le_max_right Cnear Cfar) (pow_nonneg hσ.le _))

/-- Normalized cancellation of the difference from the complete model. -/
theorem shortRadialQuadratic_model_error_limit {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
      (shortRadialQuadratic δ σ - shortRadialQuadraticModel δ σ) *
        bdgKernel (c * ρ * σ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := shortRadialQuadratic_model_cubic_bound hδ
  exact bdgKernel_cubic_cancellation _ ((measurable_shortRadialQuadratic δ).sub
    (by unfold shortRadialQuadraticModel; fun_prop)) C hC c hc

end BoundaryDraft
