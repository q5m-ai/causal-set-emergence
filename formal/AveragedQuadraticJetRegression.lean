import BoundaryDraft.AveragedQuadraticJet
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Regressions for parameterized quadratic-jet averaging

The approaching-contact tests retain the discontinuous quadratic coefficient
at contact.  They include a measure with an atom at that contact and therefore
do not hide the cutoff-contact locus behind a null-set assumption.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval

noncomputable section
namespace BoundaryDraft.AveragedQuadraticJet.Regression

open MonotoneHinge

/-! ## A finite family containing all three hinge regimes -/

def finiteQ (i : Fin 3) : ℝ := if i = 0 then 1 else if i = 1 then 0 else -1

theorem finiteQ_bounds (i : Fin 3) : -1 ≤ finiteQ i ∧ finiteQ i ≤ 1 := by
  fin_cases i <;> norm_num [finiteQ]

def finiteGap (q σ v : ℝ) : ℝ := q - σ - v

def finiteWeight (_σ _v : ℝ) : ℝ := 1

@[simp] private theorem finite_productD1 (q σ v : ℝ) :
    productD1 (finiteGap q) finiteWeight σ v = -1 := by
  unfold productD1 finiteGap finiteWeight
  simpa using (((hasDerivAt_const σ q).sub (hasDerivAt_id σ)).sub_const v).deriv

@[simp] private theorem finite_productD2 (q σ v : ℝ) :
    productD2 (finiteGap q) finiteWeight σ v = 0 := by
  simp [productD2]

private theorem finite_hypotheses (q : ℝ) (hq : q < 2) :
    Hypotheses (finiteGap q) finiteWeight 0 2 1 1 1 1 0 where
  cutoff_lt := by norm_num
  epsilon_pos := by norm_num
  transverse_pos := by norm_num
  speed_nonneg := by norm_num
  weight_nonneg := by norm_num
  second_nonneg := le_rfl
  null_continuous := by unfold finiteGap; fun_prop
  null_decrease := by intros; dsimp [finiteGap]; linarith
  clearance := by simpa [finiteGap] using hq
  nonopening := by
    intro σ hσ v _hv
    dsimp [finiteGap]
    constructor
    · linarith
    · linarith [hσ.1]
  gap_continuous := by intros; unfold finiteGap; fun_prop
  weight_continuous := by intros; exact continuousOn_const
  gap_differentiable := by intros; unfold finiteGap; fun_prop
  weight_continuousAt := by intros; exact continuousAt_const
  product_deriv := by
    intro v _hv σ _hσ
    simpa [finiteGap, finiteWeight] using
      (((hasDerivAt_const σ q).sub (hasDerivAt_id σ)).sub_const v)
  product_deriv2 := by
    intro v _hv σ _hσ
    simpa only [finite_productD1, finite_productD2] using hasDerivAt_const σ (-1)
  first_continuous := by
    have he : productD1 (finiteGap q) finiteWeight 0 = fun _v => (-1 : ℝ) := by
      funext v
      exact finite_productD1 q 0 v
    rw [he]
    exact continuousOn_const
  second_continuous := by
    have he : productD2 (finiteGap q) finiteWeight 0 = fun _v => (0 : ℝ) := by
      funext v
      exact finite_productD2 q 0 v
    rw [he]
    exact continuousOn_const
  weight_bound := by intros; norm_num [finiteWeight]
  second_bound := by intros; simp

/-- Counting weights are not normalized: this works for every finite measure
on the three-point parameter space. -/
theorem finite_active_contact_inactive (μ : Measure (Fin 3)) [IsFiniteMeasure μ] :
    (fun σ =>
      (∫ i, parameterFibre (fun i => finiteGap (finiteQ i))
          (fun _i => finiteWeight) 0 2 i σ ∂μ) -
        ((∫ i, parameterF0 (fun i => finiteGap (finiteQ i))
            (fun _i => finiteWeight) 0 2 i ∂μ) +
          (∫ i, parameterF1 (fun i => finiteGap (finiteQ i))
            (fun _i => finiteWeight) 0 2 i ∂μ) * σ +
          (∫ i, parameterF2 (fun i => finiteGap (finiteQ i))
            (fun _i => finiteWeight) 0 2 i ∂μ) * σ ^ 2)) =o[𝓝[>] 0]
      (fun σ => σ ^ 2) := by
  apply MonotoneHinge.averaged_right_quadratic_jet
  · intro i
    exact finite_hypotheses (finiteQ i) (by linarith [finiteQ_bounds i |>.2])
  · intro σ hσ
    exact measurable_of_finite _
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  · exact Integrable.of_finite
  · exact Integrable.of_finite

/-! ## The approaching-contact model on `[0,1]` -/

/-- Clipping only totalizes the regression outside the measured interval. -/
def clipped (q : ℝ) : ℝ := max 0 (min q 1)

def approachingF (q σ : ℝ) : ℝ := (1 / 2) * max (clipped q - σ) 0 ^ 2

def approachingC0 (q : ℝ) : ℝ := (clipped q) ^ 2 / 2

def approachingC1 (q : ℝ) : ℝ := -clipped q

/-- This coefficient jumps at the cutoff-contact point `q = 0`. -/
def approachingC2 (q : ℝ) : ℝ := if 0 < clipped q then 1 / 2 else 0

/-- On the measured interval this is exactly
`F_q(σ) = (1/2) * max (q-σ) 0 ^ 2`. -/
theorem approachingF_eq_model {q : ℝ} (hq : q ∈ Icc 0 1) (σ : ℝ) :
    approachingF q σ = (1 / 2) * max (q - σ) 0 ^ 2 := by
  simp [approachingF, clipped, hq.1, hq.2]

private theorem clipped_bounds (q : ℝ) : 0 ≤ clipped q ∧ clipped q ≤ 1 := by
  simp only [clipped]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

private theorem approaching_jet (q : ℝ) :
    (fun σ => approachingF q σ -
      (approachingC0 q + approachingC1 q * σ + approachingC2 q * σ ^ 2))
      =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  by_cases hp : clipped q = 0
  · apply (isLittleO_zero (fun σ : ℝ => σ ^ 2) (𝓝[>] 0)).congr'
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change 0 < σ at hσ
      have hs0 : -σ ≤ 0 := neg_nonpos.mpr hσ.le
      simp [approachingF, approachingC0, approachingC1, approachingC2, hp,
        max_eq_right hs0]
    · exact EventuallyEq.rfl
  · have hp0 : 0 < clipped q := lt_of_le_of_ne (clipped_bounds q).1 (Ne.symm hp)
    apply (isLittleO_zero (fun σ : ℝ => σ ^ 2) (𝓝[>] 0)).congr'
    · filter_upwards [Ioo_mem_nhdsGT hp0] with σ hσ
      unfold approachingF approachingC0 approachingC1 approachingC2
      rw [max_eq_left (sub_nonneg.mpr hσ.2.le), if_pos hp0]
      ring
    · exact EventuallyEq.rfl

private theorem approaching_bound (q σ : ℝ) (hσ : σ ∈ Ioc 0 1) :
    |approachingF q σ -
      (approachingC0 q + approachingC1 q * σ + approachingC2 q * σ ^ 2)| /
        σ ^ 2 ≤ 1 := by
  by_cases hp : clipped q = 0
  · have hs0 : -σ ≤ 0 := neg_nonpos.mpr hσ.1.le
    simp [approachingF, approachingC0, approachingC1, approachingC2, hp,
      max_eq_right hs0]
  have hp0 : 0 < clipped q := lt_of_le_of_ne (clipped_bounds q).1 (Ne.symm hp)
  simp only [approachingF, approachingC0, approachingC1, approachingC2, if_pos hp0]
  by_cases hs : σ ≤ clipped q
  · rw [max_eq_left (sub_nonneg.mpr hs)]
    have he : (1 / 2) * (clipped q - σ) ^ 2 -
        (clipped q ^ 2 / 2 + -clipped q * σ + 1 / 2 * σ ^ 2) = 0 := by ring
    rw [he, abs_zero, zero_div]
    norm_num
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hs))]
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_sub, abs_neg]
    have he : clipped q ^ 2 / 2 + -clipped q * σ + 1 / 2 * σ ^ 2 =
        (σ - clipped q) ^ 2 / 2 := by ring
    rw [he, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    apply (div_le_iff₀ (sq_pos_of_pos hσ.1)).2
    nlinarith [sq_nonneg (σ - clipped q), (clipped_bounds q).1]

private theorem approaching_measurable (σ : ℝ) : Measurable fun q => approachingF q σ := by
  unfold approachingF clipped
  fun_prop

private theorem coefficients_measurable :
    Measurable approachingC0 ∧ Measurable approachingC1 ∧ Measurable approachingC2 := by
  have hp : Measurable clipped := by unfold clipped; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · unfold approachingC0
    fun_prop
  · unfold approachingC1
    fun_prop
  · unfold approachingC2
    exact Measurable.ite (hp measurableSet_Ioi) measurable_const measurable_const

private theorem coefficients_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable approachingC0 μ ∧ Integrable approachingC1 μ ∧ Integrable approachingC2 μ := by
  have hconst : Integrable (fun _q : ℝ => (1 : ℝ)) μ := integrable_const 1
  obtain ⟨h0m, h1m, h2m⟩ := coefficients_measurable
  refine ⟨?_, ?_, ?_⟩
  · apply hconst.mono' h0m.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs]
    unfold approachingC0
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    nlinarith [sq_nonneg (clipped q - 1), clipped_bounds q |>.1, clipped_bounds q |>.2]
  · apply hconst.mono' h1m.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs, approachingC1, abs_neg,
      abs_of_nonneg (clipped_bounds q).1]
    exact (clipped_bounds q).2
  · apply hconst.mono' h2m.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs]
    unfold approachingC2
    split_ifs <;> norm_num [abs_of_nonneg]

/-- The averaged jet for the approaching-contact model.  No probability
normalization is used; `μ` is any finite measure. -/
theorem approaching_contact_averaged (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (fun σ => (∫ q, approachingF q σ ∂μ) -
      ((∫ q, approachingC0 q ∂μ) + (∫ q, approachingC1 q ∂μ) * σ +
        (∫ q, approachingC2 q ∂μ) * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  obtain ⟨h0m, h1m, h2m⟩ := coefficients_measurable
  obtain ⟨h0, h1, h2⟩ := coefficients_integrable μ
  apply averaged_right_quadratic_jet approachingF approachingC0 approachingC1 approachingC2
    (fun _q => 1) (by norm_num : (0 : ℝ) < 1) approaching_jet
  · exact approaching_bound
  · intro; norm_num
  · exact integrable_const 1
  · exact fun σ _hσ => approaching_measurable σ
  · exact h0m
  · exact h1m
  · exact h2m
  · exact h0
  · exact h1
  · exact h2

/-- Lebesgue averaging on the requested interval. -/
theorem approaching_contact_interval :
    (fun σ => (∫ q, approachingF q σ ∂(volume.restrict (Icc 0 1))) -
      ((∫ q, approachingC0 q ∂(volume.restrict (Icc 0 1))) +
        (∫ q, approachingC1 q ∂(volume.restrict (Icc 0 1))) * σ +
        (∫ q, approachingC2 q ∂(volume.restrict (Icc 0 1))) * σ ^ 2))
      =o[𝓝[>] 0] (fun σ => σ ^ 2) :=
  approaching_contact_averaged (volume.restrict (Icc 0 1))

/-- Adding an atom at exact cutoff contact preserves the averaged jet. -/
theorem approaching_contact_with_atom :
    (fun σ => (∫ q, approachingF q σ ∂(volume.restrict (Icc 0 1) + Measure.dirac 0)) -
      ((∫ q, approachingC0 q ∂(volume.restrict (Icc 0 1) + Measure.dirac 0)) +
        (∫ q, approachingC1 q ∂(volume.restrict (Icc 0 1) + Measure.dirac 0)) * σ +
        (∫ q, approachingC2 q ∂(volume.restrict (Icc 0 1) + Measure.dirac 0)) * σ ^ 2))
      =o[𝓝[>] 0] (fun σ => σ ^ 2) :=
  approaching_contact_averaged (volume.restrict (Icc 0 1) + Measure.dirac 0)

/-- The contact set is genuinely non-null for the atomic regression. -/
theorem contact_atom_mass :
    (volume.restrict (Icc (0 : ℝ) 1) + Measure.dirac 0 : Measure ℝ) ({0} : Set ℝ) = 1 := by
  simp

/-- The pointwise quadratic coefficient really jumps at contact. -/
theorem approachingC2_contact_jump : approachingC2 0 = 0 ∧
    ∀ q ∈ Ioo (0 : ℝ) 1, approachingC2 q = 1 / 2 := by
  constructor
  · norm_num [approachingC2, clipped]
  · intro q hq
    simp [approachingC2, clipped, hq.1, hq.2.le]

/-- The normalized error stays `1/8` on the diagonal `q = σ/2`. -/
theorem approaching_diagonal {σ : ℝ} (hσ : σ ∈ Ioc 0 1) :
    |approachingF (σ / 2) σ -
      (approachingC0 (σ / 2) + approachingC1 (σ / 2) * σ +
        approachingC2 (σ / 2) * σ ^ 2)| / σ ^ 2 = 1 / 8 := by
  have hq0 : 0 < σ / 2 := by linarith [hσ.1]
  have hq1 : σ / 2 < 1 := by linarith [hσ.2]
  have hc : clipped (σ / 2) = σ / 2 := by simp [clipped, hq0.le, hq1.le]
  unfold approachingF approachingC0 approachingC1 approachingC2
  rw [hc, if_pos hq0]
  rw [max_eq_right (by linarith [hσ.1] : σ / 2 - σ ≤ 0)]
  have he : (1 / 2) * 0 ^ 2 -
      ((σ / 2) ^ 2 / 2 + -(σ / 2) * σ + 1 / 2 * σ ^ 2) = -(σ ^ 2 / 8) := by ring
  rw [he, abs_neg, abs_of_nonneg (by positivity)]
  field_simp [hσ.1.ne']
  ring

/-- Therefore no uniform little-o estimate holds across approaching contacts. -/
theorem approaching_contact_not_uniform :
    ¬ ∀ᶠ σ : ℝ in 𝓝[>] 0, ∀ q ∈ Ioo (0 : ℝ) 1,
      |approachingF q σ -
        (approachingC0 q + approachingC1 q * σ + approachingC2 q * σ ^ 2)| /
          σ ^ 2 ≤ 1 / 16 := by
  intro he
  obtain ⟨σ, hσ, hb⟩ := ((MonotoneHinge.eventually_right zero_lt_one).and he).exists
  have hq : σ / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have := hb (σ / 2) hq
  rw [approaching_diagonal hσ] at this
  norm_num at this

/-! ## A genuinely parameter-dependent integrable envelope -/

def gaussianD (q : ℝ) : ℝ := Real.exp (-q ^ 2)

def gaussianRemainderF (q σ : ℝ) : ℝ := gaussianD q * σ ^ 3

/-- Dominated convergence works with a nonconstant integrable `D`. -/
theorem parameter_dependent_dominator :
    (fun σ => ∫ q : ℝ, gaussianRemainderF q σ) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
  have hD : Integrable gaussianD volume := by
    simpa [gaussianD] using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))
  have hj : (fun σ => (∫ q : ℝ, gaussianRemainderF q σ) -
      ((∫ _q : ℝ, (0 : ℝ)) + (∫ _q : ℝ, (0 : ℝ)) * σ +
        (∫ _q : ℝ, (0 : ℝ)) * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) := by
    apply averaged_right_quadratic_jet gaussianRemainderF (fun _ => 0) (fun _ => 0)
      (fun _ => 0) gaussianD (by norm_num : (0 : ℝ) < 1)
    · intro q
      simpa [gaussianRemainderF] using
        ((isLittleO_pow_pow (by omega : 2 < 3)).const_mul_left (gaussianD q)).mono
          nhdsWithin_le_nhds
    · intro q σ hσ
      rw [gaussianRemainderF]
      simp only [zero_add, zero_mul, sub_zero, abs_mul, abs_pow,
        abs_of_nonneg (Real.exp_nonneg _), abs_of_pos hσ.1]
      have hs2 : 0 < σ ^ 2 := sq_pos_of_pos hσ.1
      apply (div_le_iff₀ hs2).2
      have hDabs : |gaussianD q| = gaussianD q := by
        rw [gaussianD, abs_of_nonneg (Real.exp_nonneg _)]
      rw [hDabs]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      nlinarith [mul_nonneg (sq_nonneg σ) (sub_nonneg.mpr hσ.2)]
    · intro q; exact Real.exp_nonneg _
    · exact hD
    · intro σ _hσ
      unfold gaussianRemainderF gaussianD
      fun_prop
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
    · exact integrable_zero _ _ _
    · exact integrable_zero _ _ _
    · exact integrable_zero _ _ _
  simpa only [integral_zero, zero_mul, add_zero, sub_zero] using hj

/-! ## Negative control: a logarithm from an unintegrable scale -/

/-- The scale `1/q` is not integrable at the contact endpoint. -/
theorem inverse_scale_not_integrable :
    ¬ IntegrableOn (fun q : ℝ => 1 / q) (Ioc 0 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [one_div, intervalIntegrable_inv_iff, zero_ne_one, false_or,
    not_not] using (show (0 : ℝ) ∈ uIcc 0 1 by simp)

/-- Integrating a quadratic contribution against that scale produces the
explicit `σ² log σ` term.  This is a scalar warning, not a counterexample to
any geometric theorem. -/
theorem quadratic_log_layer {σ : ℝ} (hσ : σ ∈ Ioc 0 1) :
    (∫ q in σ..1, σ ^ 2 / q) = -(σ ^ 2 * Real.log σ) := by
  have hi := integral_one_div_of_pos hσ.1 (by norm_num : (0 : ℝ) < 1)
  rw [show (fun q : ℝ => σ ^ 2 / q) = fun q => σ ^ 2 * (1 / q) by funext q; ring,
    intervalIntegral.integral_const_mul, hi]
  rw [show (1 : ℝ) / σ = σ⁻¹ by simp, Real.log_inv]
  ring

end BoundaryDraft.AveragedQuadraticJet.Regression
