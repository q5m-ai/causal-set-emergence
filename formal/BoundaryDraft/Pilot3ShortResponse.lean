import BoundaryDraft.Pilot3ShortBasis
import BoundaryDraft.Pilot3ShortMoments

/-!
# Physical signed response of the sharp three-dimensional quadratic model

This analytic model retains the point volume and all four angularly averaged
modes. No global planar theorem is used. Its exact sharp fibres differ from the
fractional/affine model by a globally quadratically bounded function; the second
absolute transverse moment makes that difference vanish after normalization.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace Pilot3ShortResponse

open Pilot3ShortBasis Pilot3ShortMoments

/-- The point and pair coefficients really coincide in dimension three. -/
theorem point_eq_pair : dimensionPointCoefficient 3 = dimensionPairCoefficient 3 := by
  norm_num [dimensionPointCoefficient, dimensionPairCoefficient]

theorem pair_eq : dimensionPairCoefficient 3 =
    2 * dimensionIntervalCoefficient 3 ^ (2 / 3 : ℝ) / Real.Gamma (5 / 3) := by
  norm_num [dimensionPairCoefficient, dimensionActionScale]
  ring

/-- The signed critical coefficient, including the minus sign in the action. -/
theorem normalized_action_coefficient :
    -dimensionPairCoefficient 3 * dimensionIntervalCoefficient 3 ^ (-(5 / 3 : ℝ)) *
      moment (3 / 2) = -6 / Real.pi := by
  have hc := dimensionIntervalCoefficient_pos 3 (by norm_num)
  have hg : Real.Gamma (5 / 3 : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  rw [pair_eq, moment_three_halves]
  calc
    _ = -(1 / 2 : ℝ) * (dimensionIntervalCoefficient 3 ^ (2 / 3 : ℝ) *
        dimensionIntervalCoefficient 3 ^ (-(5 / 3 : ℝ))) := by field_simp; ring
    _ = -(1 / 2 : ℝ) * dimensionIntervalCoefficient 3 ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hc]
      norm_num
    _ = _ := by
      rw [Real.rpow_neg_one, dimensionIntervalCoefficient_three]
      field_simp
      ring

/-- The four-mode density uses the full circle mass only on the volume mode. -/
def modelDensity (δ V ℓ α β σ : ℝ) : ℝ :=
  (2 * Real.pi * V) * F0 δ σ + ℓ * Ftau δ σ + α * Ftt δ σ + β * Frr δ σ

private theorem integral_fibre_eq_Ico (δ : ℝ) {σ : ℝ} (hσ : 0 < σ) (F : ℝ → ℝ) :
    (∫ v : ℝ in Ioo 0 δ, if σ ≤ v ^ 2 then F v else 0) =
      ∫ v : ℝ in Ico (Real.sqrt σ) δ, F v := by
  have hset : Ico (Real.sqrt σ) δ ⊆ Ioo 0 δ := by
    intro v hv
    exact ⟨(Real.sqrt_pos.mpr hσ).trans_le hv.1, hv.2⟩
  calc
    _ = ∫ v : ℝ in Ioo 0 δ, (Ico (Real.sqrt σ) δ).indicator F v := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro v hv
      by_cases hs : σ ≤ v ^ 2
      · have hr : v ∈ Ico (Real.sqrt σ) δ :=
          ⟨Real.sqrt_le_iff.mpr ⟨hv.1.le, hs⟩, hv.2⟩
        simp only [if_pos hs, Set.indicator_of_mem hr]
      · have hr : v ∉ Ico (Real.sqrt σ) δ := by
          intro h
          exact hs (Real.sqrt_le_iff.mp h.1).2
        simp only [if_neg hs, Set.indicator_of_not_mem hr]
    _ = _ := by rw [setIntegral_indicator measurableSet_Ico, inter_eq_right.mpr hset]

/-- Exact sharp-fibre bridge for the full angularly averaged quadratic model.
The large-proper-time case is an empty fibre, and the endpoint replacements
are Lebesgue-null. Absolute integrability precedes the signed mode sum. -/
theorem modelDensity_eq_fibre {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (V ℓ α β : ℝ) :
    modelDensity δ V ℓ α β σ = ∫ v : ℝ in Ioo 0 δ, if σ ≤ v ^ 2 then
      pilot3ShortNullJacobian v σ * (2 * Real.pi * V + ℓ * ((v + σ / v) / 2) +
        α * ((v + σ / v) / 2) ^ 2 + β * ((v - σ / v) / 2) ^ 2) else 0 := by
  rw [integral_fibre_eq_Ico δ hσ]
  by_cases hs : σ ≤ δ ^ 2
  · have hrootδ : Real.sqrt σ ≤ δ := Real.sqrt_le_iff.mpr ⟨hδ.le, hs⟩
    have hn (v : ℝ) (hv : v ∈ Icc (Real.sqrt σ) δ) : v ≠ 0 :=
      ((Real.sqrt_pos.mpr hσ).trans_le hv.1).ne'
    have hJ : ContinuousOn (fun v => pilot3ShortNullJacobian v σ) (Icc (Real.sqrt σ) δ) :=
      (continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
        (fun v hv => pow_ne_zero 2 (hn v hv)))).div_const 4
    have hτ : ContinuousOn (fun v => (v + σ / v) / 2) (Icc (Real.sqrt σ) δ) :=
      (continuousOn_id.add (continuousOn_const.div continuousOn_id hn)).div_const 2
    have hr : ContinuousOn (fun v => (v - σ / v) / 2) (Icc (Real.sqrt σ) δ) :=
      (continuousOn_id.sub (continuousOn_const.div continuousOn_id hn)).div_const 2
    have h0 := ((hJ.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self).const_mul
      (2 * Real.pi * V)
    have h1 := (((hJ.mul hτ).integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self).const_mul ℓ
    have h2 := (((hJ.mul (hτ.pow 2)).integrableOn_Icc (μ := volume)).mono_set
      Ioo_subset_Icc_self).const_mul α
    have h3 := (((hJ.mul (hr.pow 2)).integrableOn_Icc (μ := volume)).mono_set
      Ioo_subset_Icc_self).const_mul β
    rw [modelDensity, F0_eq_integral hδ hσ.le hs, Ftau_eq_integral hδ hσ.le hs,
      Ftt_eq_integral hδ hσ.le hs, Frr_eq_integral hδ hσ.le hs]
    simp only [intervalIntegral.integral_of_le hrootδ,
      integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
    symm
    calc
      _ = ∫ v : ℝ in Ioo (Real.sqrt σ) δ,
          (2 * Real.pi * V) * pilot3ShortNullJacobian v σ +
          ℓ * (pilot3ShortNullJacobian v σ * ((v + σ / v) / 2)) +
          α * (pilot3ShortNullJacobian v σ * ((v + σ / v) / 2) ^ 2) +
          β * (pilot3ShortNullJacobian v σ * ((v - σ / v) / 2) ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro v _
        dsimp only
        ring
      _ = _ := by
        have he0 := integral_add h0 h1
        have he1 := integral_add (h0.add h1) h2
        have he2 := integral_add ((h0.add h1).add h2) h3
        simp only [Pi.add_apply] at he0 he1 he2
        rw [he2, he1, he0]
        simp only [integral_const_mul]
  · have hr : δ ≤ Real.sqrt σ := by
      by_contra! h
      exact hs (Real.sqrt_le_iff.mp h.le).2
    simp [modelDensity, F0, Ftau, Ftt, Frr, hs, Ico_eq_empty_of_le hr]

/-- Physical short action of this exact sharp quadratic model. -/
def modelAction (δ V ℓ α β ρ : ℝ) : ℝ :=
  ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * V - dimensionPairCoefficient 3 * ρ *
    ∫ σ : ℝ in Ioi 0, modelDensity δ V ℓ α β σ *
      dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))

/-- The affine and fractional terms whose signed responses survive the comparison.
This is not the actual sharp density. -/
def lowModel (a b h t σ : ℝ) : ℝ :=
  a + b * σ + h * σ ^ (1 / 2 : ℝ) + t * σ ^ (3 / 2 : ℝ)

/-- A general exact sharp expression, including its degree-two and degree-three terms. -/
def cutoffModel (δ a b h t d e σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then lowModel a b h t σ + d * σ ^ 2 + e * σ ^ 3 else 0

theorem measurable_modelDensity (δ V ℓ α β : ℝ) : Measurable (modelDensity δ V ℓ α β) := by
  exact ((((measurable_F0 δ).const_mul _).add ((measurable_Ftau δ).const_mul _)).add
    ((measurable_Ftt δ).const_mul _)).add ((measurable_Frr δ).const_mul _)

theorem measurable_lowModel (a b h t : ℝ) : Measurable (lowModel a b h t) := by
  unfold lowModel
  fun_prop

theorem measurable_cutoffModel (δ a b h t d e : ℝ) : Measurable (cutoffModel δ a b h t d e) := by
  unfold cutoffModel lowModel
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

theorem integrable_lowModel (a b h t : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ => lowModel a b h t σ *
      dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) (Ioi 0) := by
  have h0 := (integrable (j := 0) (by norm_num) hc hρ).const_mul a
  have h1 := (integrable (j := 1) (by norm_num) hc hρ).const_mul b
  have hh := (integrable (j := 1 / 2) (by norm_num) hc hρ).const_mul h
  have ht := (integrable (j := 3 / 2) (by norm_num) hc hρ).const_mul t
  apply (((h0.add h1).add hh).add ht).congr
  exact Eventually.of_forall fun σ => by dsimp [lowModel]; simp only [Real.rpow_zero, Real.rpow_one]; ring

/-- Only the affine part cancels exactly. The high-degree sharp terms are not
assigned zero finite-density moments. -/
theorem integral_lowModel (a b h t : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ σ : ℝ in Ioi 0, lowModel a b h t σ *
      dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) =
      h * (c * ρ) ^ (-1 : ℝ) * moment (1 / 2) +
        t * (c * ρ) ^ (-(5 / 3 : ℝ)) * moment (3 / 2) := by
  have h0 := (integrable (j := 0) (by norm_num) hc hρ).const_mul a
  have h1 := (integrable (j := 1) (by norm_num) hc hρ).const_mul b
  have hh := (integrable (j := 1 / 2) (by norm_num) hc hρ).const_mul h
  have ht := (integrable (j := 3 / 2) (by norm_num) hc hρ).const_mul t
  have he (σ : ℝ) : lowModel a b h t σ * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ)) =
      a * (σ ^ (0 : ℝ) * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) +
      b * (σ ^ (1 : ℝ) * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) +
      h * (σ ^ (1 / 2 : ℝ) * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) +
      t * (σ ^ (3 / 2 : ℝ) * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) := by
    simp only [lowModel, Real.rpow_zero, Real.rpow_one]
    ring
  simp_rw [he]
  have he0 := integral_add h0 h1
  have he1 := integral_add (h0.add h1) hh
  have he2 := integral_add ((h0.add h1).add hh) ht
  simp only [Pi.add_apply] at he0 he1 he2
  rw [he2, he1, he0]
  simp only [integral_const_mul]
  rw [density_moment 0 hc hρ, density_moment 1 hc hρ,
    density_moment (1 / 2) hc hρ, density_moment (3 / 2) hc hρ]
  norm_num
  ring

private theorem tail_power_bound {q σ j : ℝ} (hq : 0 < q) (hs : q ≤ σ) (hj : j ≤ 2) :
    σ ^ j ≤ q ^ (j - 2) * σ ^ 2 := by
  have hσ := hq.trans_le hs
  calc
    _ = σ ^ (j - 2) * σ ^ (2 : ℝ) := by rw [← Real.rpow_add hσ]; congr 1; ring
    _ ≤ _ := by
      rw [Real.rpow_two]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hq hs (sub_nonpos.mpr hj)) (sq_nonneg σ)

private theorem lowModel_tail_bound {q σ : ℝ} (hq : 0 < q) (hs : q ≤ σ) (a b h t : ℝ) :
    |lowModel a b h t σ| ≤
      (|a| * q ^ (-2 : ℝ) + |b| * q ^ (-1 : ℝ) +
        |h| * q ^ (-(3 / 2 : ℝ)) + |t| * q ^ (-(1 / 2 : ℝ))) * σ ^ 2 := by
  have hσ := hq.trans_le hs
  have h0 := tail_power_bound (j := 0) hq hs (by norm_num)
  have h1 := tail_power_bound (j := 1) hq hs (by norm_num)
  have hh := tail_power_bound (j := 1 / 2) hq hs (by norm_num)
  have ht := tail_power_bound (j := 3 / 2) hq hs (by norm_num)
  norm_num only [Real.rpow_zero, Real.rpow_one] at h0 h1 hh ht
  calc
    _ ≤ |a| + |b| * σ + |h| * σ ^ (1 / 2 : ℝ) + |t| * σ ^ (3 / 2 : ℝ) := by
      unfold lowModel
      exact ((abs_add _ _).trans (add_le_add_right
        ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)).trans_eq (by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hσ,
            abs_of_pos (Real.rpow_pos_of_pos hσ _), abs_of_pos (Real.rpow_pos_of_pos hσ _)])
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg a),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg b),
        mul_le_mul_of_nonneg_left hh (abs_nonneg h),
        mul_le_mul_of_nonneg_left ht (abs_nonneg t)]

/-- Global second-order domination, including all omitted fixed-cutoff tails. -/
theorem cutoffModel_error_bound {δ : ℝ} (hδ : 0 < δ) (a b h t d e : ℝ) :
    ∃ C : ℝ, ∀ σ, 0 < σ →
      ‖cutoffModel δ a b h t d e σ - lowModel a b h t σ‖ ≤ C * σ ^ 2 := by
  let Cnear := |d| + |e| * δ ^ 2
  let Cfar := |a| * (δ ^ 2) ^ (-2 : ℝ) + |b| * (δ ^ 2) ^ (-1 : ℝ) +
    |h| * (δ ^ 2) ^ (-(3 / 2 : ℝ)) + |t| * (δ ^ 2) ^ (-(1 / 2 : ℝ))
  refine ⟨max Cnear Cfar, fun σ hσ => ?_⟩
  by_cases hs : σ ≤ δ ^ 2
  · have he : cutoffModel δ a b h t d e σ - lowModel a b h t σ = d * σ ^ 2 + e * σ ^ 3 := by
      rw [cutoffModel, if_pos ⟨hσ.le, hs⟩]
      ring
    rw [he, Real.norm_eq_abs]
    calc
      _ ≤ |d * σ ^ 2| + |e * σ ^ 3| := abs_add _ _
      _ = (|d| + |e| * σ) * σ ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ), abs_of_pos (pow_pos hσ 3)]
        ring
      _ ≤ Cnear * σ ^ 2 := by dsimp [Cnear]; gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg σ)
  · rw [cutoffModel, if_neg (by simp [hs]), zero_sub, norm_neg, Real.norm_eq_abs]
    exact (lowModel_tail_bound (sq_pos_of_pos hδ) (le_of_not_ge hs) a b h t).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cnear Cfar) (sq_nonneg σ))

/-- The full cutoff expression is integrable before signed subtraction. -/
theorem integrable_cutoffModel {δ c ρ : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ)
    (a b h t d e : ℝ) :
    IntegrableOn (fun σ => cutoffModel δ a b h t d e σ *
      dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) (Ioi 0) := by
  obtain ⟨C, hC⟩ := cutoffModel_error_bound hδ a b h t d e
  have hi := integrable_of_bound _ ((measurable_cutoffModel δ a b h t d e).sub
    (measurable_lowModel a b h t)) C (j := 2) (by norm_num)
      (by simpa only [Real.rpow_two] using hC) hc hρ
  apply (hi.add (integrable_lowModel a b h t hc hρ)).congr
  exact Eventually.of_forall fun σ => by dsimp; ring

/-- This is a vanishing correction, not a finite-density zero identity. -/
theorem cutoffModel_error_limit {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (a b h t d e : ℝ) :
    Tendsto (fun ρ : ℝ => ρ ^ (5 / 3 : ℝ) * ∫ σ : ℝ in Ioi 0,
      (cutoffModel δ a b h t d e σ - lowModel a b h t σ) *
        dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := cutoffModel_error_bound hδ a b h t d e
  exact limit_of_bound _ ((measurable_cutoffModel δ a b h t d e).sub
    (measurable_lowModel a b h t)) C (j := 2) (by norm_num)
      (by simpa only [Real.rpow_two] using hC) hc

/-- The affine/fractional comparison for the complete model. Its half-power
coefficient is minus pi times the actual point volume. -/
def modelGerm (δ V ℓ α β σ : ℝ) : ℝ :=
  lowModel ((2 * Real.pi * V) * δ / 4 + ℓ * δ ^ 2 / 16 + (α + β) * δ ^ 3 / 48)
    ((2 * Real.pi * V) / (4 * δ) - ℓ / 8 + (α - 3 * β) * δ / 16)
    (-Real.pi * V) (-α / 6 + β / 3) σ

/-- Exact finite-density algebra: the degree-two and degree-three coefficients
remain in the sharp model, including the time-linear degree-two term. -/
theorem modelDensity_eq_cutoffModel (δ V ℓ α β σ : ℝ) :
    modelDensity δ V ℓ α β σ =
      cutoffModel δ
        ((2 * Real.pi * V) * δ / 4 + ℓ * δ ^ 2 / 16 + (α + β) * δ ^ 3 / 48)
        ((2 * Real.pi * V) / (4 * δ) - ℓ / 8 + (α - 3 * β) * δ / 16)
        (-Real.pi * V) (-α / 6 + β / 3)
        (ℓ / (16 * δ ^ 2) + (α - 3 * β) / (16 * δ))
        ((α + β) / (48 * δ ^ 3)) σ := by
  by_cases hs : 0 ≤ σ ∧ σ ≤ δ ^ 2
  · simp only [modelDensity, F0, Ftau, Ftt, Frr, cutoffModel, if_pos hs, lowModel]
    ring
  · simp [modelDensity, F0, Ftau, Ftt, Frr, cutoffModel, hs]

theorem integrable_modelDensity {δ c ρ : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ)
    (V ℓ α β : ℝ) :
    IntegrableOn (fun σ => modelDensity δ V ℓ α β σ *
      dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) (Ioi 0) := by
  simp_rw [modelDensity_eq_cutoffModel]
  exact integrable_cutoffModel hδ hc hρ _ _ _ _ _ _

theorem integrable_modelGerm (δ V ℓ α β : ℝ) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ => modelGerm δ V ℓ α β σ *
      dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) (Ioi 0) :=
  integrable_lowModel _ _ _ _ hc hρ

theorem modelDensity_error_bound {δ : ℝ} (hδ : 0 < δ) (V ℓ α β : ℝ) :
    ∃ C : ℝ, ∀ σ, 0 < σ →
      ‖modelDensity δ V ℓ α β σ - modelGerm δ V ℓ α β σ‖ ≤ C * σ ^ 2 := by
  simp_rw [modelDensity_eq_cutoffModel]
  exact cutoffModel_error_bound hδ _ _ _ _ _ _

theorem modelDensity_error_limit {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (V ℓ α β : ℝ) :
    Tendsto (fun ρ : ℝ => ρ ^ (5 / 3 : ℝ) * ∫ σ : ℝ in Ioi 0,
      (modelDensity δ V ℓ α β σ - modelGerm δ V ℓ α β σ) *
        dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  simp_rw [modelDensity_eq_cutoffModel]
  exact cutoffModel_error_limit hδ hc _ _ _ _ _ _

/-- The half-power produces exactly volume divided by density, rather than an
assumed planar-base identity. The other displayed term is the critical response. -/
theorem modelGerm_integral (δ V ℓ α β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ σ : ℝ in Ioi 0, modelGerm δ V ℓ α β σ *
      dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) =
      V / ρ + (-α / 6 + β / 3) *
        (dimensionIntervalCoefficient 3 * ρ) ^ (-(5 / 3 : ℝ)) * moment (3 / 2) := by
  have hc := dimensionIntervalCoefficient_pos 3 (by norm_num)
  simp only [modelGerm]
  rw [integral_lowModel _ _ _ _ hc hρ]
  have hv : (-Real.pi * V) * (dimensionIntervalCoefficient 3 * ρ) ^ (-1 : ℝ) *
      moment (1 / 2) = V / ρ := by
    rw [moment_half, Real.rpow_neg_one, dimensionIntervalCoefficient_three]
    field_simp
    ring
  rw [hv]

theorem rho_normalization {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (2 / 3 : ℝ) * ρ = ρ ^ (5 / 3 : ℝ) := by
  have he := Real.rpow_add hρ (2 / 3) 1
  norm_num at he
  exact he.symm

private theorem critical_density_factor {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    ρ ^ (5 / 3 : ℝ) * (c * ρ) ^ (-(5 / 3 : ℝ)) = c ^ (-(5 / 3 : ℝ)) := by
  rw [Real.mul_rpow hc.le hρ.le]
  calc
    _ = c ^ (-(5 / 3 : ℝ)) * (ρ ^ (5 / 3 : ℝ) * ρ ^ (-(5 / 3 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hρ, add_neg_cancel, Real.rpow_zero, mul_one]

/-- Exact cancellation of the physical point term in the comparison model.
Both the point/pair equality and the nonzero half moment are proved inputs. -/
theorem modelGerm_point_cancellation (δ V ℓ α β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (2 / 3 : ℝ) * (dimensionPointCoefficient 3 * V - dimensionPairCoefficient 3 * ρ *
      ∫ σ : ℝ in Ioi 0, modelGerm δ V ℓ α β σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) =
      (α - 2 * β) / Real.pi := by
  rw [modelGerm_integral δ V ℓ α β hρ, point_eq_pair]
  have hc := dimensionIntervalCoefficient_pos 3 (by norm_num)
  calc
    _ = (-α / 6 + β / 3) * (-dimensionPairCoefficient 3) *
        (ρ ^ (2 / 3 : ℝ) * ρ) *
        (dimensionIntervalCoefficient 3 * ρ) ^ (-(5 / 3 : ℝ)) * moment (3 / 2) := by
      field_simp
      ring
    _ = (-α / 6 + β / 3) * (-dimensionPairCoefficient 3 *
        dimensionIntervalCoefficient 3 ^ (-(5 / 3 : ℝ)) * moment (3 / 2)) := by
      rw [rho_normalization hρ]
      calc
        _ = (-α / 6 + β / 3) * (-dimensionPairCoefficient 3) *
            (ρ ^ (5 / 3 : ℝ) * (dimensionIntervalCoefficient 3 * ρ) ^ (-(5 / 3 : ℝ))) *
              moment (3 / 2) := by ring
        _ = _ := by rw [critical_density_factor hc hρ]; ring
    _ = _ := by rw [normalized_action_coefficient]; ring

/-- Unconditional analytic limit of the exact sharp quadratic model at every
fixed positive cutoff. No long estimate, geometric jet or planar-base theorem
is a hypothesis. -/
theorem modelAction_limit {δ : ℝ} (hδ : 0 < δ) (V ℓ α β : ℝ) :
    Tendsto (modelAction δ V ℓ α β) atTop (𝓝 ((α - 2 * β) / Real.pi)) := by
  have hc := dimensionIntervalCoefficient_pos 3 (by norm_num)
  have he := (modelDensity_error_limit hδ hc V ℓ α β).const_mul (-dimensionPairCoefficient 3)
  have hl := (tendsto_const_nhds (x := (α - 2 * β) / Real.pi)).add he
  simp only [mul_zero, add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hiA := integrable_modelDensity hδ hc hρ V ℓ α β
  have hiG := integrable_modelGerm δ V ℓ α β hc hρ
  have hs : (∫ σ : ℝ in Ioi 0, (modelDensity δ V ℓ α β σ - modelGerm δ V ℓ α β σ) *
      dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) =
      (∫ σ : ℝ in Ioi 0, modelDensity δ V ℓ α β σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ))) -
      ∫ σ : ℝ in Ioi 0, modelGerm δ V ℓ α β σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) := by
    simp_rw [sub_mul]
    exact integral_sub hiA hiG
  rw [hs, ← modelGerm_point_cancellation δ V ℓ α β hρ, ← rho_normalization hρ]
  unfold modelAction
  ring

/-- Positive one-over-pi time-square response in dimension three. -/
theorem Ftt_action_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, Ftt δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 (1 / Real.pi)) := by
  have hl := modelAction_limit hδ 0 0 1 0
  norm_num only [mul_zero, sub_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  simp only [modelAction, modelDensity, mul_zero, zero_mul, one_mul, add_zero, zero_add, zero_sub]
  rw [← rho_normalization hρ]
  ring

/-- Negative two-over-pi radial-square response in dimension three. -/
theorem Frr_action_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, Frr δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 (-2 / Real.pi)) := by
  have hl := modelAction_limit hδ 0 0 0 1
  norm_num only [mul_one, zero_sub] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  simp only [modelAction, modelDensity, mul_zero, zero_mul, one_mul, add_zero, zero_add, zero_sub]
  rw [← rho_normalization hρ]
  ring

/-- The linear mode has a vanishing normalized response, not a zero truncated integral. -/
theorem Ftau_action_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, Ftau δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hl := modelAction_limit hδ 0 1 0 0
  norm_num only [mul_zero, sub_zero, zero_div] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  simp only [modelAction, modelDensity, mul_zero, zero_mul, one_mul, add_zero, zero_add, zero_sub]
  rw [← rho_normalization hρ]
  ring

end Pilot3ShortResponse
end BoundaryDraft
