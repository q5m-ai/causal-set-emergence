import BoundaryDraft.ShortCutoffPolynomial

/-!
# Absolute-overlap short densities

The constant, time-linear and time-square radial integrals missing from the
same-height difference route. These are analytic basis identities, not an
independent-envelope geometry theorem or an enlarged-class action limit.
The moving lower endpoint and the constant mode's first logarithm are retained.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- The sharp-cutoff density of the constant overlap mode, without sphere mass. -/
def shortRadialConstant (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then
    δ ^ 2 / 16 - σ / 4 * Real.log δ - σ ^ 2 / (16 * δ ^ 2) +
      σ / 8 * Real.log σ
  else 0

/-- The sharp-cutoff density of the time-linear overlap mode. -/
def shortRadialTime (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then
    δ ^ 3 / 48 - σ * δ / 16 + σ ^ 2 / (16 * δ) - σ ^ 3 / (48 * δ ^ 3)
  else 0

/-- The sharp-cutoff density of the time-square overlap mode. -/
def shortRadialTimeSquare (δ σ : ℝ) : ℝ :=
  if 0 ≤ σ ∧ σ ≤ δ ^ 2 then
    δ ^ 4 / 128 - σ ^ 2 / 16 * Real.log δ - σ ^ 4 / (128 * δ ^ 4) +
      σ ^ 2 / 32 * Real.log σ
  else 0

def shortRadialConstantPrimitive (σ v : ℝ) : ℝ :=
  v ^ 2 / 16 - σ / 4 * Real.log v - σ ^ 2 / 16 * (v ^ 2)⁻¹

def shortRadialTimePrimitive (σ v : ℝ) : ℝ :=
  v ^ 3 / 48 - σ * v / 16 + σ ^ 2 / 16 * v⁻¹ - σ ^ 3 / 48 * (v ^ 3)⁻¹

def shortRadialTimeSquarePrimitive (σ v : ℝ) : ℝ :=
  v ^ 4 / 128 - σ ^ 2 / 16 * Real.log v - σ ^ 4 / 128 * (v ^ 4)⁻¹

theorem hasDerivAt_shortRadialConstantPrimitive (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (shortRadialConstantPrimitive σ) ((v - σ / v) ^ 2 / (8 * v)) v := by
  have hd := ((((hasDerivAt_id v).pow 2).div_const 16).sub
    ((Real.hasDerivAt_log hv.ne').const_mul (σ / 4))).sub
      ((((hasDerivAt_id v).pow 2).inv (pow_ne_zero 2 hv.ne')).const_mul (σ ^ 2 / 16))
  convert hd using 1
  dsimp only [id_eq]
  field_simp [hv.ne']
  ring

theorem hasDerivAt_shortRadialTimePrimitive (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (shortRadialTimePrimitive σ)
      (((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2)) v := by
  have hd := (((((hasDerivAt_id v).pow 3).div_const 48).sub
    ((hasDerivAt_id v).const_mul (σ / 16))).add
      (((hasDerivAt_id v).inv hv.ne').const_mul (σ ^ 2 / 16))).sub
        ((((hasDerivAt_id v).pow 3).inv (pow_ne_zero 3 hv.ne')).const_mul (σ ^ 3 / 48))
  convert hd using 1
  · funext x
    dsimp [shortRadialTimePrimitive]
    ring
  · dsimp only [id_eq]
    field_simp [hv.ne']
    ring

theorem hasDerivAt_shortRadialTimeSquarePrimitive (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (shortRadialTimeSquarePrimitive σ)
      (((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2) ^ 2) v := by
  have hd := ((((hasDerivAt_id v).pow 4).div_const 128).sub
    ((Real.hasDerivAt_log hv.ne').const_mul (σ ^ 2 / 16))).sub
      ((((hasDerivAt_id v).pow 4).inv (pow_ne_zero 4 hv.ne')).const_mul (σ ^ 4 / 128))
  convert hd using 1
  dsimp only [id_eq]
  field_simp [hv.ne']
  ring

theorem shortRadialConstantPrimitive_sqrt {σ : ℝ} (hσ : 0 < σ) :
    shortRadialConstantPrimitive σ (Real.sqrt σ) = -σ / 8 * Real.log σ := by
  rw [shortRadialConstantPrimitive, Real.sq_sqrt hσ.le, Real.log_sqrt hσ.le]
  field_simp [hσ.ne']
  ring

/-- The potentially fractional time-linear contribution cancels at the actual
moving endpoint. It is not discarded by an angular or oddness argument. -/
theorem shortRadialTimePrimitive_sqrt {σ : ℝ} (hσ : 0 < σ) :
    shortRadialTimePrimitive σ (Real.sqrt σ) = 0 := by
  have hs : Real.sqrt σ ≠ 0 := (Real.sqrt_pos.mpr hσ).ne'
  have he : σ = Real.sqrt σ ^ 2 := (Real.sq_sqrt hσ.le).symm
  unfold shortRadialTimePrimitive
  generalize Real.sqrt σ = r at *
  rw [he]
  field_simp [hs]
  ring

theorem shortRadialTimeSquarePrimitive_sqrt {σ : ℝ} (hσ : 0 < σ) :
    shortRadialTimeSquarePrimitive σ (Real.sqrt σ) = -σ ^ 2 / 32 * Real.log σ := by
  have hs4 : Real.sqrt σ ^ 4 = σ ^ 2 := by
    rw [show Real.sqrt σ ^ 4 = (Real.sqrt σ ^ 2) ^ 2 by ring, Real.sq_sqrt hσ.le]
  rw [shortRadialTimeSquarePrimitive, hs4, Real.log_sqrt hσ.le]
  field_simp [hσ.ne']
  ring

private theorem positive_on_short_interval {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) {v : ℝ} (hv : v ∈ uIcc (Real.sqrt σ) δ) : 0 < v := by
  rw [uIcc_of_le (Real.sqrt_le_iff.mpr ⟨hδ.le, hs⟩)] at hv
  exact (Real.sqrt_pos.mpr hσ).trans_le hv.1

theorem shortRadialConstant_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) :
    shortRadialConstant δ σ = ∫ v in (Real.sqrt σ)..δ,
      (v - σ / v) ^ 2 / (8 * v) := by
  have hv := fun (v : ℝ) hv => (positive_on_short_interval hδ hσ hs hv : 0 < v)
  have hc : ContinuousOn (fun v : ℝ => (v - σ / v) ^ 2 / (8 * v))
      (uIcc (Real.sqrt σ) δ) := by
    exact ((continuousOn_id.sub (continuousOn_const.div continuousOn_id
      (fun v h => (hv v h).ne'))).pow 2).div (continuousOn_const.mul continuousOn_id)
        (fun v h => mul_ne_zero (by norm_num) (hv v h).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v h => hasDerivAt_shortRadialConstantPrimitive σ (hv v h)) hc.intervalIntegrable,
    shortRadialConstantPrimitive_sqrt hσ, shortRadialConstant, if_pos ⟨hσ.le, hs⟩,
    shortRadialConstantPrimitive]
  ring

theorem shortRadialTime_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) :
    shortRadialTime δ σ = ∫ v in (Real.sqrt σ)..δ,
      ((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2) := by
  have hv := fun (v : ℝ) hv => (positive_on_short_interval hδ hσ hs hv : 0 < v)
  have hdiv : ContinuousOn (fun v : ℝ => σ / v) (uIcc (Real.sqrt σ) δ) :=
    continuousOn_const.div continuousOn_id (fun v h => (hv v h).ne')
  have hc : ContinuousOn (fun v : ℝ => ((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2))
      (uIcc (Real.sqrt σ) δ) :=
    (((continuousOn_id.sub hdiv).pow 2).div (continuousOn_const.mul continuousOn_id)
      (fun v h => mul_ne_zero (by norm_num) (hv v h).ne')).mul
        ((continuousOn_id.add hdiv).div_const 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v h => hasDerivAt_shortRadialTimePrimitive σ (hv v h)) hc.intervalIntegrable,
    shortRadialTimePrimitive_sqrt hσ, shortRadialTime, if_pos ⟨hσ.le, hs⟩,
    shortRadialTimePrimitive]
  ring

theorem shortRadialTimeSquare_eq_integral {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hs : σ ≤ δ ^ 2) :
    shortRadialTimeSquare δ σ = ∫ v in (Real.sqrt σ)..δ,
      ((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2) ^ 2 := by
  have hv := fun (v : ℝ) hv => (positive_on_short_interval hδ hσ hs hv : 0 < v)
  have hdiv : ContinuousOn (fun v : ℝ => σ / v) (uIcc (Real.sqrt σ) δ) :=
    continuousOn_const.div continuousOn_id (fun v h => (hv v h).ne')
  have hc : ContinuousOn
      (fun v : ℝ => ((v - σ / v) ^ 2 / (8 * v)) * ((v + σ / v) / 2) ^ 2)
      (uIcc (Real.sqrt σ) δ) :=
    (((continuousOn_id.sub hdiv).pow 2).div (continuousOn_const.mul continuousOn_id)
      (fun v h => mul_ne_zero (by norm_num) (hv v h).ne')).mul
        (((continuousOn_id.add hdiv).div_const 2).pow 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v h => hasDerivAt_shortRadialTimeSquarePrimitive σ (hv v h)) hc.intervalIntegrable,
    shortRadialTimeSquarePrimitive_sqrt hσ, shortRadialTimeSquare, if_pos ⟨hσ.le, hs⟩,
    shortRadialTimeSquarePrimitive]
  ring

/-- A cross-check using the exact proper-time identity, including empty support. -/
theorem shortRadialTimeSquare_eq_radial_add (δ σ : ℝ) :
    shortRadialTimeSquare δ σ = shortRadialQuadratic δ σ + σ * shortRadialConstant δ σ := by
  unfold shortRadialTimeSquare shortRadialQuadratic shortRadialConstant
  split_ifs <;> ring

private theorem scaled_log_one_expand {k : ℝ} (hk : k ≠ 0) (z : ℝ) :
    (k⁻¹ * z) * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2) =
      k⁻¹ * (z * Real.log z * bdgKernel (z ^ 2)) -
        (k⁻¹ * Real.log k) * (z * bdgKernel (z ^ 2)) := by
  by_cases hz : z = 0
  · simp [hz]
  rw [Real.log_mul (inv_ne_zero hk) hz, Real.log_inv]
  ring

theorem integrableOn_bdgKernel_transverse_scaled_log_one (k : ℝ) (hk : 0 < k) :
    IntegrableOn (fun s : ℝ => s * Real.log s * bdgKernel ((k * s) ^ 2)) (Ioi 0) := by
  have hi : IntegrableOn (fun z : ℝ =>
      (k⁻¹ * z) * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2)) (Ioi 0) := by
    simp_rw [scaled_log_one_expand hk.ne']
    have hi₁ : IntegrableOn (fun z : ℝ => z * bdgKernel (z ^ 2)) (Ioi 0) := by
      simpa using integrableOn_bdgKernel_transverse_moment 1
    exact (integrableOn_bdgKernel_transverse_log_one.const_mul k⁻¹).sub
      (hi₁.const_mul (k⁻¹ * Real.log k))
  have hs := (integrableOn_Ioi_comp_mul_left_iff
    (fun z : ℝ => (k⁻¹ * z) * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2)) 0 hk).2
      (by simpa using hi)
  simpa only [inv_mul_cancel_left₀ hk.ne'] using hs

theorem integral_bdgKernel_transverse_scaled_log_one (k : ℝ) (hk : 0 < k) :
    (∫ s : ℝ in Ioi 0, s * Real.log s * bdgKernel ((k * s) ^ 2)) = k⁻¹ ^ 2 / 12 := by
  have hs := integral_comp_mul_left_Ioi
    (fun z : ℝ => (k⁻¹ * z) * Real.log (k⁻¹ * z) * bdgKernel (z ^ 2)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hs
  rw [hs]
  simp_rw [scaled_log_one_expand hk.ne']
  have hi : IntegrableOn (fun z : ℝ => z * bdgKernel (z ^ 2)) (Ioi 0) := by
    simpa using integrableOn_bdgKernel_transverse_moment 1
  rw [integral_sub (integrableOn_bdgKernel_transverse_log_one.const_mul k⁻¹)
    (hi.const_mul (k⁻¹ * Real.log k)), integral_const_mul, integral_const_mul,
    integral_bdgKernel_transverse_log_one, integral_bdgKernel_transverse_one]
  ring

/-- The full constant-mode model. It is not the compactly supported actual
short density: its tail must still be controlled before transferring a limit. -/
def shortRadialConstantModel (δ σ : ℝ) : ℝ :=
  δ ^ 2 / 16 + (-Real.log δ / 4) * σ + (-1 / (16 * δ ^ 2)) * σ ^ 2 +
    (1 / 8) * (σ * Real.log σ)

/-- Exact response of the uncut model with all polynomial moments cancelled. -/
theorem shortRadialConstantModel_response (δ : ℝ) {c ρ : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ s : ℝ in Ioi 0, shortRadialConstantModel δ s * bdgKernel (c * ρ * s ^ 2)) =
      1 / (96 * c * ρ) := by
  let k := Real.sqrt (c * ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have he (s : ℝ) : c * ρ * s ^ 2 = (k * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he]
  have hexpand (s : ℝ) : shortRadialConstantModel δ s * bdgKernel ((k * s) ^ 2) =
      (δ ^ 2 / 16 + (-Real.log δ / 4) * s + (-1 / (16 * δ ^ 2)) * s ^ 2) *
        bdgKernel ((k * s) ^ 2) + (1 / 8) * (s * Real.log s * bdgKernel ((k * s) ^ 2)) := by
    unfold shortRadialConstantModel
    ring
  simp_rw [hexpand]
  rw [integral_add (integrableOn_bdgKernel_transverse_scaled_quadratic
    (δ ^ 2 / 16) (-Real.log δ / 4) (-1 / (16 * δ ^ 2)) k hk)
      ((integrableOn_bdgKernel_transverse_scaled_log_one k hk).const_mul (1 / 8)),
    integral_bdgKernel_transverse_scaled_quadratic _ _ _ k hk, integral_const_mul,
    integral_bdgKernel_transverse_scaled_log_one k hk, zero_add]
  rw [inv_pow, show k ^ 2 = c * ρ from Real.sq_sqrt (mul_pos hc hρ).le]
  field_simp
  ring

/-- The constant volume logarithm cancels the original point term exactly for
this uncut model at every positive density. This is not a geometric limit. -/
theorem shortRadialConstantModel_point_cancellation (δ V : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ * (V - ρ * (4 * Real.pi * V) *
      ∫ s : ℝ in Ioi 0, shortRadialConstantModel δ s *
        bdgKernel ((Real.pi / 24) * ρ * s ^ 2)) = 0 := by
  rw [shortRadialConstantModel_response δ (by positivity) hρ]
  field_simp [Real.pi_ne_zero, hρ.ne']
  ring

private theorem abs_mul_log_bound {s : ℝ} (hs : 0 < s) :
    |s * Real.log s| ≤ 1 + s ^ 2 := by
  have hlo : -1 ≤ s * Real.log s := by
    have h := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log hs.le) hs.le
    simpa [mul_neg, mul_inv_cancel₀ hs.ne'] using h
  have hhi : s * Real.log s ≤ s ^ 2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left (Real.log_le_self hs.le) hs.le
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg s], by linarith⟩

/-- This controls the omitted uncut-model tail too, not only the density near
zero. Constants depend on the fixed positive cutoff. -/
theorem shortRadialConstant_model_cubic_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ σ, 0 < σ →
      ‖shortRadialConstant δ σ - shortRadialConstantModel δ σ‖ ≤ C * σ ^ 3 := by
  let a := δ ^ 2 / 16
  let b := -Real.log δ / 4
  let d := -1 / (16 * δ ^ 2)
  let C := (|a| + 1 / 8) / (δ ^ 2) ^ 3 + |b| / (δ ^ 2) ^ 2 +
    (|d| + 1 / 8) / (δ ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, fun σ hσ => ?_⟩
  by_cases hs : σ ≤ δ ^ 2
  · have he : shortRadialConstant δ σ - shortRadialConstantModel δ σ = 0 := by
      rw [shortRadialConstant, if_pos ⟨hσ.le, hs⟩, shortRadialConstantModel]
      ring
    rw [he, norm_zero]
    exact mul_nonneg hC (pow_nonneg hσ.le _)
  · rw [shortRadialConstant, if_neg (by simp [hs]), zero_sub, norm_neg, Real.norm_eq_abs]
    have hb : |shortRadialConstantModel δ σ| ≤
        (|a| + 1 / 8) + |b| * σ + (|d| + 1 / 8) * σ ^ 2 := by
      calc
        _ ≤ |a + b * σ + d * σ ^ 2| + |(1 / 8) * (σ * Real.log σ)| := abs_add _ _
        _ ≤ (|a| + |b * σ| + |d * σ ^ 2|) + |(1 / 8) * (σ * Real.log σ)| := by
          gcongr
          exact (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
        _ = |a| + |b| * σ + |d| * σ ^ 2 + (1 / 8) * |σ * Real.log σ| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hσ, abs_of_nonneg (sq_nonneg σ)]
          norm_num
        _ ≤ |a| + |b| * σ + |d| * σ ^ 2 + (1 / 8) * (1 + σ ^ 2) := by
          gcongr
          exact abs_mul_log_bound hσ
        _ = _ := by ring
    apply hb.trans
    have hn : 0 ≤ (|a| + 1 / 8) + |b| * σ + (|d| + 1 / 8) * σ ^ 2 := by positivity
    simpa only [abs_of_nonneg hn, abs_of_nonneg (by positivity : 0 ≤ |a| + 1 / 8),
      abs_of_nonneg (abs_nonneg b), abs_of_nonneg (by positivity : 0 ≤ |d| + 1 / 8)] using
      ShortCutoffPolynomial.quadratic_bound (sq_pos_of_pos hδ) (le_of_not_ge hs)
        (|a| + 1 / 8) |b| (|d| + 1 / 8)

theorem measurable_shortRadialConstant (δ : ℝ) : Measurable (shortRadialConstant δ) := by
  unfold shortRadialConstant
  apply Measurable.ite (measurableSet_Icc (a := 0) (b := δ ^ 2)) <;> fun_prop

theorem integrableOn_shortRadialConstantModel (δ : ℝ) {c ρ : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => shortRadialConstantModel δ s * bdgKernel (c * ρ * s ^ 2))
      (Ioi 0) := by
  let k := Real.sqrt (c * ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have he (s : ℝ) : c * ρ * s ^ 2 = (k * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hc hρ).le]
  simp_rw [he]
  have hi := (integrableOn_bdgKernel_transverse_scaled_quadratic
    (δ ^ 2 / 16) (-Real.log δ / 4) (-1 / (16 * δ ^ 2)) k hk).add
      ((integrableOn_bdgKernel_transverse_scaled_log_one k hk).const_mul (1 / 8))
  apply hi.congr
  exact Eventually.of_forall fun s => by dsimp [shortRadialConstantModel]; ring

theorem integrableOn_shortRadialConstant {δ c ρ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => shortRadialConstant δ s * bdgKernel (c * ρ * s ^ 2))
      (Ioi 0) := by
  obtain ⟨C, hC⟩ := shortRadialConstant_model_cubic_bound hδ
  have hm : Measurable (fun s => shortRadialConstant δ s - shortRadialConstantModel δ s) :=
    (measurable_shortRadialConstant δ).sub (by unfold shortRadialConstantModel; fun_prop)
  have hi := integrableOn_bdgKernel_mul_cubic_bound _ hm C hC hc hρ
  apply (hi.add (integrableOn_shortRadialConstantModel δ hc hρ)).congr
  exact Eventually.of_forall fun s => by dsimp; ring

/-- Actual constant-mode response after point subtraction, at every fixed
positive cutoff. The sharp-cutoff/model tail is included in the proof. -/
theorem shortRadialConstant_point_limit {δ : ℝ} (hδ : 0 < δ) (V : ℝ) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (V - ρ * (4 * Real.pi * V) * ∫ s : ℝ in Ioi 0,
        shortRadialConstant δ s * bdgKernel ((Real.pi / 24) * ρ * s ^ 2)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := shortRadialConstant_model_cubic_bound hδ
  have hmeas : Measurable (fun s => shortRadialConstant δ s - shortRadialConstantModel δ s) :=
    (measurable_shortRadialConstant δ).sub (by unfold shortRadialConstantModel; fun_prop)
  have hc : 0 < Real.pi / 24 := by positivity
  have hl := (bdgKernel_cubic_cancellation _ hmeas C hC (Real.pi / 24) hc).const_mul
    (-(4 / Real.sqrt 6) * (4 * Real.pi * V))
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hiM := integrableOn_shortRadialConstantModel δ hc hρ
  have hiA := integrableOn_shortRadialConstant hδ hc hρ
  simp_rw [sub_mul]
  rw [integral_sub hiA hiM, shortRadialConstantModel_response δ hc hρ]
  field_simp [Real.pi_ne_zero, hρ.ne']
  ring

theorem shortRadialTime_eq_polynomial (δ : ℝ) :
    shortRadialTime δ = ShortCutoffPolynomial.density δ
      (δ ^ 3 / 48) (-δ / 16) (1 / (16 * δ)) (-1 / (48 * δ ^ 3)) 0 := by
  funext σ
  unfold shortRadialTime ShortCutoffPolynomial.density
  split_ifs <;> ring

theorem integrableOn_shortRadialTime {δ c ρ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => shortRadialTime δ σ * bdgKernel (c * ρ * σ ^ 2))
      (Ioi 0) := by
  rw [shortRadialTime_eq_polynomial]
  exact ShortCutoffPolynomial.integrable_density hδ hc hρ _ _ _ _ _

/-- The linear basis is a truncated polynomial only AFTER the moving-endpoint
calculation. Its normalized response vanishes, including the cutoff tail. -/
theorem shortRadialTime_limit {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
      shortRadialTime δ σ * bdgKernel (c * ρ * σ ^ 2)) atTop (𝓝 0) := by
  rw [shortRadialTime_eq_polynomial]
  exact ShortCutoffPolynomial.normalized_limit hδ hc _ _ _ _ _

/-- Cancel the second logarithm algebraically, not by dropping the time-square
term. The remaining truncated polynomial has zero normalized limit. -/
theorem shortRadialTimeSquare_add_third_radial (δ σ : ℝ) :
    shortRadialTimeSquare δ σ + (1 / 3) * shortRadialQuadratic δ σ =
      ShortCutoffPolynomial.density δ (δ ^ 4 / 96) (-δ ^ 2 / 48) 0
        (1 / (48 * δ ^ 2)) (-1 / (96 * δ ^ 4)) σ := by
  unfold shortRadialTimeSquare shortRadialQuadratic ShortCutoffPolynomial.density
  split_ifs <;> ring

theorem integrableOn_shortRadialTimeSquare {δ c ρ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => shortRadialTimeSquare δ σ * bdgKernel (c * ρ * σ ^ 2))
      (Ioi 0) := by
  have hiP := ShortCutoffPolynomial.integrable_density hδ hc hρ
    (δ ^ 4 / 96) (-δ ^ 2 / 48) 0 (1 / (48 * δ ^ 2)) (-1 / (96 * δ ^ 4))
  have hiR := (integrableOn_shortRadialQuadratic hδ hc hρ).const_mul (1 / 3)
  apply (hiP.sub hiR).congr
  exact Eventually.of_forall fun σ => by
    dsimp only [Pi.sub_apply]
    rw [← shortRadialTimeSquare_add_third_radial]
    ring

/-- The independent time-square signed response has the opposite sign and one
third the magnitude of the radial-square response. -/
theorem bdg_shortRadialTimeSquare_action_limit {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * (Real.sqrt ρ * ρ *
      ∫ σ : ℝ in Ioi 0, shortRadialTimeSquare δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))) atTop (𝓝 (1 / (2 * Real.pi))) := by
  have hc : 0 < Real.pi / 24 := by positivity
  have hl := ((ShortCutoffPolynomial.normalized_limit hδ hc
    (δ ^ 4 / 96) (-δ ^ 2 / 48) 0 (1 / (48 * δ ^ 2)) (-1 / (96 * δ ^ 4))).const_mul
      (-(4 / Real.sqrt 6))).sub ((bdg_shortRadialQuadratic_action_limit hδ).const_mul (1 / 3))
  have hval : -(4 / Real.sqrt 6) * 0 - (1 / 3) * (-3 / (2 * Real.pi)) =
      1 / (2 * Real.pi) := by ring
  rw [hval] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hiT := integrableOn_shortRadialTimeSquare hδ hc hρ
  have hiR := (integrableOn_shortRadialQuadratic hδ hc hρ).const_mul (1 / 3)
  have he (σ : ℝ) : ShortCutoffPolynomial.density δ (δ ^ 4 / 96) (-δ ^ 2 / 48) 0
        (1 / (48 * δ ^ 2)) (-1 / (96 * δ ^ 4)) σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) =
      shortRadialTimeSquare δ σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2) +
        (1 / 3) * (shortRadialQuadratic δ σ * bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) := by
    rw [← shortRadialTimeSquare_add_third_radial]
    ring
  simp_rw [he]
  rw [integral_add hiT hiR, integral_const_mul]
  ring

end BoundaryDraft
