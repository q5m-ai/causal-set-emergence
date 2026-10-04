import BoundaryDraft.Pilot3NullCoordinates
import BoundaryDraft.Pilot3CubicBounds
import BoundaryDraft.TruncatedAffineJet
import BoundaryDraft.DimensionCancellation

/-!
# Three-dimensional short null remainder cancellation

At a fixed positive long coordinate `v`, the second proper-time derivative is
bounded by `T / v`. This is not an integrable bound down to zero. The truncated
fibre's affine residual, normalized by the three-halves power, is instead
bounded by `3 * T`, including fibres that have already closed. Pointwise
quadratic control and dominated convergence give the sufficient affine
little-o, without differentiating a moving square-root endpoint or claiming
a uniform quadratic residual for the averaged density.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace Pilot3ShortRemainder

abbrev point := pilot3NullPoint
abbrev jacobian := pilot3NullJacobian

def direction (ω : Pilot3Circle) (v : ℝ) : Space :=
  (1 / (2 * v), (-(1 / (2 * v))) • ω.val)

def jacobianFirst (v : ℝ) : ℝ := -(1 / (4 * v ^ 2))

def along (R : Space → ℝ) (ω : Pilot3Circle) (v σ : ℝ) : ℝ := R (point ω v σ)
def alongFirst (R : Space → ℝ) (ω : Pilot3Circle) (v σ : ℝ) : ℝ :=
  fderiv ℝ R (point ω v σ) (direction ω v)
def alongSecond (R : Space → ℝ) (ω : Pilot3Circle) (v σ : ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ R) (point ω v σ) (direction ω v) (direction ω v)

def fibre (R : Space → ℝ) (ω : Pilot3Circle) (v σ : ℝ) : ℝ :=
  jacobian v σ * along R ω v σ

def first (R : Space → ℝ) (ω : Pilot3Circle) (v σ : ℝ) : ℝ :=
  jacobianFirst v * along R ω v σ + jacobian v σ * alongFirst R ω v σ

def second (R : Space → ℝ) (ω : Pilot3Circle) (v σ : ℝ) : ℝ :=
  2 * jacobianFirst v * alongFirst R ω v σ + jacobian v σ * alongSecond R ω v σ

theorem hasDerivAt_point (ω : Pilot3Circle) (v σ : ℝ) :
    HasDerivAt (point ω v) (direction ω v) σ := by
  have ht := ((hasDerivAt_const σ v).add ((hasDerivAt_id σ).div_const v)).div_const 2
  have hr := (((hasDerivAt_const σ v).sub ((hasDerivAt_id σ).div_const v)).div_const 2).smul_const ω.val
  convert ht.prodMk hr using 1
  apply Prod.ext
  · dsimp only [direction]
    ring
  · change (-(1 / (2 * v))) • ω.val = ((0 - 1 / v) / 2) • ω.val
    congr 1
    ring

theorem norm_direction (ω : Pilot3Circle) {v : ℝ} (hv : 0 < v) :
    ‖direction ω v‖ = 1 / (2 * v) := by
  simp only [direction, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_neg,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, max_self]
  exact abs_of_pos (by positivity)

theorem hasDerivAt_jacobian (v σ : ℝ) :
    HasDerivAt (jacobian v) (jacobianFirst v) σ := by
  convert (((hasDerivAt_const σ 1).sub ((hasDerivAt_id σ).div_const (v ^ 2))).div_const 4) using 1
  dsimp only [jacobianFirst, id_eq]
  ring

theorem hasDerivAt_along {R : Space → ℝ} (ω : Pilot3Circle) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ)) :
    HasDerivAt (along R ω v) (alongFirst R ω v σ) σ :=
  hR.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_point ω v σ)

theorem hasDerivAt_alongFirst {R : Space → ℝ} (ω : Pilot3Circle) (v σ : ℝ)
    (hR : DifferentiableAt ℝ (fderiv ℝ R) (point ω v σ)) :
    HasDerivAt (alongFirst R ω v) (alongSecond R ω v σ) σ := by
  have hd := (hR.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_point ω v σ)).clm_apply
    (hasDerivAt_const σ (direction ω v))
  simpa only [alongFirst, alongSecond, Function.comp_def, map_zero, zero_add, add_zero] using hd

theorem hasDerivAt_fibre {R : Space → ℝ} (ω : Pilot3Circle) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ)) :
    HasDerivAt (fibre R ω v) (first R ω v σ) σ :=
  (hasDerivAt_jacobian v σ).mul (hasDerivAt_along ω v σ hR)

theorem hasDerivAt_first {R : Space → ℝ} (ω : Pilot3Circle) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ))
    (hR' : DifferentiableAt ℝ (fderiv ℝ R) (point ω v σ)) :
    HasDerivAt (first R ω v) (second R ω v σ) σ := by
  convert ((hasDerivAt_along ω v σ hR).const_mul (jacobianFirst v)).add
    ((hasDerivAt_jacobian v σ).mul (hasDerivAt_alongFirst ω v σ hR')) using 1
  dsimp only [second]
  ring

theorem jacobian_bounds {v σ : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    |jacobian v σ| ≤ 1 / 4 ∧ |jacobianFirst v| = 1 / (4 * v ^ 2) := by
  obtain ⟨hj₀, hj₁⟩ := pilot3NullJacobian_bounds hv hσ
  refine ⟨by rwa [abs_of_nonneg hj₀], ?_⟩
  rw [jacobianFirst, abs_neg, abs_of_pos (by positivity : 0 < 1 / (4 * v ^ 2))]

theorem along_bounds {R : Space → ℝ} (ω : Pilot3Circle) {v σ T : ℝ} (hv : 0 < v)
    (h₀ : ‖R (point ω v σ)‖ ≤ T * v ^ 3)
    (h₁ : ‖fderiv ℝ R (point ω v σ)‖ ≤ T * v ^ 2)
    (h₂ : ‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ ≤ T * v) :
    |along R ω v σ| ≤ T * v ^ 3 ∧ |alongFirst R ω v σ| ≤ T * v / 2 ∧
      |alongSecond R ω v σ| ≤ T / (4 * v) := by
  refine ⟨h₀, ?_, ?_⟩
  · change ‖fderiv ℝ R (point ω v σ) (direction ω v)‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ R (point ω v σ)‖ * ‖direction ω v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (T * v ^ 2) * (1 / (2 * v)) := by rw [norm_direction ω hv]; gcongr
      _ = T * v / 2 := by field_simp; ring
  · change ‖fderiv ℝ (fderiv ℝ R) (point ω v σ) (direction ω v) (direction ω v)‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ R) (point ω v σ) (direction ω v)‖ * ‖direction ω v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ * ‖direction ω v‖) * ‖direction ω v‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (T * v * (1 / (2 * v))) * (1 / (2 * v)) := by rw [norm_direction ω hv]; gcongr
      _ = T / (4 * v) := by field_simp; ring

/-- Unlike the four-dimensional Jacobian, the second derivative has a genuine
inverse-`v` bound. It is not asserted to be uniformly integrable. -/
theorem fibre_bounds {R : Space → ℝ} (ω : Pilot3Circle) {v σ T : ℝ}
    (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) (hT : 0 ≤ T)
    (h₀ : ‖R (point ω v σ)‖ ≤ T * v ^ 3)
    (h₁ : ‖fderiv ℝ R (point ω v σ)‖ ≤ T * v ^ 2)
    (h₂ : ‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ ≤ T * v) :
    |fibre R ω v σ| ≤ T * v ^ 3 ∧ |first R ω v σ| ≤ T * v ∧
      |second R ω v σ| ≤ T / v := by
  obtain ⟨ha, ha₁, ha₂⟩ := along_bounds ω hv h₀ h₁ h₂
  obtain ⟨hj, hj₁⟩ := jacobian_bounds hv hσ
  refine ⟨?_, ?_, ?_⟩
  · rw [fibre, abs_mul]
    calc
      _ ≤ (1 / 4) * (T * v ^ 3) := by gcongr
      _ ≤ T * v ^ 3 := by nlinarith [mul_nonneg hT (pow_nonneg hv.le 3)]
  · rw [first]
    calc
      _ ≤ |jacobianFirst v| * |along R ω v σ| + |jacobian v σ| * |alongFirst R ω v σ| := by
        simpa only [abs_mul] using abs_add (jacobianFirst v * along R ω v σ)
          (jacobian v σ * alongFirst R ω v σ)
      _ ≤ (1 / (4 * v ^ 2)) * (T * v ^ 3) + (1 / 4) * (T * v / 2) := by rw [hj₁]; gcongr
      _ = (3 / 8) * T * v := by field_simp; ring
      _ ≤ T * v := by nlinarith [mul_nonneg hT hv.le]
  · rw [second]
    calc
      _ ≤ 2 * |jacobianFirst v| * |alongFirst R ω v σ| + |jacobian v σ| * |alongSecond R ω v σ| := by
        simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          abs_add (2 * jacobianFirst v * alongFirst R ω v σ) (jacobian v σ * alongSecond R ω v σ)
      _ ≤ 2 * (1 / (4 * v ^ 2)) * (T * v / 2) + (1 / 4) * (T / (4 * v)) := by rw [hj₁]; gcongr
      _ = (5 / 16) * (T / v) := by field_simp; ring
      _ ≤ T / v := by nlinarith [div_nonneg hT hv.le]

namespace CubicBounds

variable {R : Space → ℝ} {δ T : ℝ} (h : CubicBounds R δ T)
include h

omit h in
theorem point_mem (ω : Pilot3Circle) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) : point ω v σ ∈ Metric.ball (0 : Space) δ := by
  simpa only [Metric.mem_ball, dist_zero_right] using
    (pilot3NullPoint_norm_le ω hv.1 hσ).trans_lt hv.2

theorem point_bounds (ω : Pilot3Circle) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖R (point ω v σ)‖ ≤ T * v ^ 3 ∧
    ‖fderiv ℝ R (point ω v σ)‖ ≤ T * v ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ ≤ T * v := by
  have hp := point_mem ω hv hσ
  have hn := pilot3NullPoint_norm_le ω hv.1 hσ
  have hT := h.nonneg
  refine ⟨(h.value _ hp).trans ?_, (h.first _ hp).trans ?_, (h.second _ hp).trans ?_⟩ <;> gcongr

theorem fibre_deriv (ω : Pilot3Circle) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    HasDerivAt (fibre R ω v) (Pilot3ShortRemainder.first R ω v σ) σ :=
  hasDerivAt_fibre ω v σ ((h.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
    (point_mem ω hv hσ))).differentiableAt (by norm_num))

theorem first_deriv (ω : Pilot3Circle) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    HasDerivAt (Pilot3ShortRemainder.first R ω v) (Pilot3ShortRemainder.second R ω v σ) σ := by
  have hs := h.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds (point_mem ω hv hσ))
  exact hasDerivAt_first ω v σ (hs.differentiableAt (by norm_num))
    ((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem bounds (ω : Pilot3Circle) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    |fibre R ω v σ| ≤ T * v ^ 3 ∧ |Pilot3ShortRemainder.first R ω v σ| ≤ T * v ∧
      |Pilot3ShortRemainder.second R ω v σ| ≤ T / v := by
  obtain ⟨h₀, h₁, h₂⟩ := h.point_bounds ω hv hσ
  exact fibre_bounds ω hv.1 hσ h.nonneg h₀ h₁ h₂

theorem right_affine_jet (ω : Pilot3Circle) {v : ℝ} (hv : v ∈ Ioo 0 δ) :
    (fun σ => TruncatedAffineJet.truncate (fibre R ω v) (v ^ 2) σ -
      (fibre R ω v 0 + Pilot3ShortRemainder.first R ω v 0 * σ)) =o[𝓝[>] 0]
        (fun σ => σ ^ (3 / 2 : ℝ)) :=
  TruncatedAffineJet.right_affine_jet (sq_pos_of_pos hv.1) (div_nonneg h.nonneg hv.1.le)
    (fun _ hσ => h.fibre_deriv ω hv hσ) (fun _ hσ => h.first_deriv ω hv hσ)
    (fun _ hσ => (h.bounds ω hv hσ).2.2)

/-- The compensating square root of the cutoff removes the inverse-`v`
singularity from the normalized residual, even for closed fibres. -/
theorem normalized_remainder_bound (ω : Pilot3Circle) {v σ : ℝ}
    (hv : v ∈ Ioo 0 δ) (hσ : 0 < σ) :
    |TruncatedAffineJet.truncate (fibre R ω v) (v ^ 2) σ -
      (fibre R ω v 0 + Pilot3ShortRemainder.first R ω v 0 * σ)| / σ ^ (3 / 2 : ℝ) ≤
        3 * T := by
  obtain ⟨h₀, h₁, _⟩ := h.bounds ω hv ⟨le_rfl, sq_nonneg v⟩
  have he₀ : T / v * (v ^ 2) ^ 2 = T * v ^ 3 := by field_simp [hv.1.ne']; ring
  have he₁ : T / v * v ^ 2 = T * v := by field_simp [hv.1.ne']; ring
  have hb := TruncatedAffineJet.normalized_remainder_bound
    (sq_pos_of_pos hv.1) (div_nonneg h.nonneg hv.1.le) hσ
    (fun _ hσ => h.fibre_deriv ω hv hσ) (fun _ hσ => h.first_deriv ω hv hσ)
    (fun _ hσ => (h.bounds ω hv hσ).2.2) (he₀.symm ▸ h₀) (he₁.symm ▸ h₁)
  rw [Real.sqrt_sq hv.1.le] at hb
  convert hb using 1
  field_simp [hv.1.ne']

end CubicBounds

/-- The fixed finite parameter domain includes all positive long coordinates,
with no common lower cutoff. -/
abbrev Parameter (δ : ℝ) := Pilot3Circle × Ioo (0 : ℝ) δ

def lengthMeasure (δ : ℝ) : Measure (Ioo (0 : ℝ) δ) := volume.comap Subtype.val

instance finite_lengthMeasure (δ : ℝ) : IsFiniteMeasure (lengthMeasure δ) := by
  constructor
  rw [lengthMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply,
    Set.image_univ, Subtype.range_coe]
  exact measure_Ioo_lt_top

def parameterMeasure (δ : ℝ) : Measure (Parameter δ) := pilot3CircleMeasure.prod (lengthMeasure δ)

instance finite_parameterMeasure (δ : ℝ) : IsFiniteMeasure (parameterMeasure δ) :=
  inferInstanceAs (IsFiniteMeasure (pilot3CircleMeasure.prod (lengthMeasure δ)))

def parameterFibre (R : Space → ℝ) (δ : ℝ) (p : Parameter δ) (σ : ℝ) : ℝ :=
  TruncatedAffineJet.truncate (fibre R p.1 p.2.val) (p.2.val ^ 2) σ

/-- The actual truncated remainder density, expressed on a fixed product
space. `density_eq_iterated` identifies the full-circle/long-coordinate integral. -/
def density (R : Space → ℝ) (δ σ : ℝ) : ℝ :=
  ∫ p, parameterFibre R δ p σ ∂parameterMeasure δ

theorem measurable_parameterFibre {R : Space → ℝ} (hR : Measurable R) (δ : ℝ) :
    Measurable (fun p : ℝ × Parameter δ => parameterFibre R δ p.2 p.1) := by
  unfold parameterFibre TruncatedAffineJet.truncate fibre along jacobian point
    pilot3NullJacobian pilot3NullPoint
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop

theorem measurable_density {R : Space → ℝ} (hR : Measurable R) (δ : ℝ) :
    Measurable (density R δ) :=
  (measurable_parameterFibre hR δ).stronglyMeasurable.integral_prod_right'.measurable

namespace CubicBounds

variable {R : Space → ℝ} {δ T : ℝ} (h : CubicBounds R δ T)
include h

theorem parameterFibre_bound (p : Parameter δ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖parameterFibre R δ p σ‖ ≤ T * δ ^ 3 := by
  unfold parameterFibre TruncatedAffineJet.truncate
  split_ifs with hs
  · exact (h.bounds p.1 p.2.property ⟨hσ, hs⟩).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.2.property.1.le p.2.property.2.le 3) h.nonneg)
  · rw [norm_zero]
    exact mul_nonneg h.nonneg (pow_nonneg (le_of_lt (p.2.property.1.trans p.2.property.2)) 3)

theorem density_bound {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖density R δ σ‖ ≤ T * δ ^ 3 * (parameterMeasure δ).real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun p => h.parameterFibre_bound p hσ)

theorem integrable_parameterFibre (hR : Measurable R) {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (fun p => parameterFibre R δ p σ) (parameterMeasure δ) := by
  apply (integrable_const (T * δ ^ 3)).mono'
    (((measurable_parameterFibre hR δ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun p => h.parameterFibre_bound p hσ

/-- Absolute integrability is established before this signed Fubini identity. -/
theorem density_eq_iterated (hR : Measurable R) {σ : ℝ} (hσ : 0 ≤ σ) :
    density R δ σ = ∫ ω, (∫ v in Ioo (0 : ℝ) δ,
      if σ ≤ v ^ 2 then pilot3NullJacobian v σ * R (pilot3NullPoint ω v σ) else 0)
        ∂pilot3CircleMeasure := by
  rw [density, parameterMeasure, integral_prod _ (h.integrable_parameterFibre hR hσ)]
  apply integral_congr_ae
  filter_upwards with ω
  exact integral_subtype_comap measurableSet_Ioo
    (fun v => if σ ≤ v ^ 2 then jacobian v σ * R (point ω v σ) else 0)

/-- A sufficient affine jet of real order three-halves for the actual density.
There is deliberately no claim of an averaged quadratic bound. -/
theorem density_right_affine_jet (hR : Measurable R) :
    ∃ b₀ b₁ : ℝ, (fun σ => density R δ σ - (b₀ + b₁ * σ)) =o[𝓝[>] 0]
      (fun σ => σ ^ (3 / 2 : ℝ)) := by
  let F := fun (p : Parameter δ) σ => fibre R p.1 p.2.val σ
  let F' := fun (p : Parameter δ) σ => Pilot3ShortRemainder.first R p.1 p.2.val σ
  let F'' := fun (p : Parameter δ) σ => Pilot3ShortRemainder.second R p.1 p.2.val σ
  let q := fun p : Parameter δ => p.2.val ^ 2
  let B := fun p : Parameter δ => T / p.2.val
  have hq (p : Parameter δ) : 0 < q p := sq_pos_of_pos p.2.property.1
  have hm (σ : ℝ) (_hσ : σ ∈ Ioc 0 1) :
      Measurable (fun p => TruncatedAffineJet.truncate (F p) (q p) σ) :=
    (measurable_parameterFibre hR δ).comp (measurable_const.prodMk measurable_id)
  have hd (p : Parameter δ) (σ : ℝ) (hσ : σ ∈ Icc 0 (q p)) :
      HasDerivAt (F p) (F' p σ) σ := h.fibre_deriv p.1 p.2.property hσ
  have hd' (p : Parameter δ) (σ : ℝ) (hσ : σ ∈ Icc 0 (q p)) :
      HasDerivAt (F' p) (F'' p σ) σ := h.first_deriv p.1 p.2.property hσ
  obtain ⟨hm₀, hm₁⟩ := TruncatedAffineJet.measurable_coefficients F F' F'' q hq hm hd hd'
  have hi₀ : Integrable (fun p => F p 0) (parameterMeasure δ) := by
    apply (integrable_const (T * δ ^ 3)).mono' hm₀.aestronglyMeasurable
    filter_upwards with p
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.2.property.1.le p.2.property.2.le 3) h.nonneg)
  have hi₁ : Integrable (fun p => F' p 0) (parameterMeasure δ) := by
    apply (integrable_const (T * δ)).mono' hm₁.aestronglyMeasurable
    filter_upwards with p
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).2.1.trans
      (mul_le_mul_of_nonneg_left p.2.property.2.le h.nonneg)
  refine ⟨∫ p, F p 0 ∂parameterMeasure δ, ∫ p, F' p 0 ∂parameterMeasure δ, ?_⟩
  apply TruncatedAffineJet.averaged_right_affine_jet F F' F'' q B hq
  · exact fun p => div_nonneg h.nonneg p.2.property.1.le
  · have he : (fun p => B p * Real.sqrt (q p)) = fun _ : Parameter δ => T := by
      funext p
      dsimp only [B, q]
      rw [Real.sqrt_sq p.2.property.1.le, div_mul_cancel₀ _ p.2.property.1.ne']
    rw [he]
    exact integrable_const T
  · exact hm
  · exact hd
  · exact hd'
  · exact fun p _ hσ => (h.bounds p.1 p.2.property hσ).2.2
  · intro p
    have he : B p * q p ^ 2 = T * p.2.val ^ 3 := by
      dsimp [B, q]
      field_simp [p.2.property.1.ne']
      ring
    rw [he]
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).1
  · intro p
    have he : B p * q p = T * p.2.val := by
      dsimp [B, q]
      field_simp [p.2.property.1.ne']
      ring
    rw [he]
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).2.1
  · exact hi₀
  · exact hi₁

/-- Absolute integrability at every positive density, before any signed
splitting of the short action. Only measurability and the finite density bound
are used here, not its asymptotic jet. -/
theorem integrableOn_density_mul_kernel (hR : Measurable R) {c ρ : ℝ}
    (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => density R δ σ *
      dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) (Ioi 0) := by
  exact integrableOn_dimensionKernel_density_mul_bounded 3 (by norm_num)
    (density R δ) (measurable_density hR δ)
    (T * δ ^ 3 * (parameterMeasure δ).real univ) (fun _ hs => h.density_bound hs.le)
    c ρ hc hρ

/-- Kernel-first order and the unchanged interval coefficient, matching the
actual short-action density formula. -/
theorem integrableOn_actionKernel_mul_density (hR : Measurable R) {ρ : ℝ}
    (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ =>
      dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)) *
        density R δ σ) (Ioi 0) := by
  simpa only [mul_comm] using h.integrableOn_density_mul_kernel hR
    (dimensionIntervalCoefficient_pos 3 (by norm_num)) hρ

/-- Signed cancellation with the full three-dimensional density scaling.
The two vanishing integer moments are used before any absolute estimate. -/
theorem normalized_density_limit (hR : Measurable R) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (5 / 3 : ℝ) * ∫ σ : ℝ in Ioi 0,
      density R δ σ * dimensionKernel 3 (c * ρ * σ ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
  obtain ⟨b₀, b₁, hj⟩ := h.density_right_affine_jet hR
  let b : ℕ → ℝ := fun n => if n = 0 then b₀ else b₁
  have he (σ : ℝ) : dimensionJet 3 b σ = b₀ + b₁ * σ := by
    norm_num [dimensionJet, dimensionFactorCount, Finset.sum_range_succ, b]
  have hj' : (fun σ => density R δ σ - dimensionJet 3 b σ) =o[𝓝[>] 0]
      (fun σ => σ ^ ((3 : ℝ) / 2)) := by simpa only [he] using hj
  have hl := dimensionKernel_transverse_cancellation 3 (by norm_num)
    (density R δ) (measurable_density hR δ)
    (T * δ ^ 3 * (parameterMeasure δ).real univ) (fun _ hs => h.density_bound hs.le) b hj' c hc
  norm_num at hl ⊢
  exact hl

/-- The actual pair coefficient and action's minus sign preserve the zero
limit; the interval coefficient is the unchanged dimension-indexed one. -/
theorem normalized_action_remainder_limit (hR : Measurable R) :
    Tendsto (fun ρ : ℝ => -dimensionPairCoefficient 3 * ρ ^ (5 / 3 : ℝ) *
      ∫ σ : ℝ in Ioi 0, density R δ σ *
        dimensionKernel 3 (dimensionIntervalCoefficient 3 * ρ * σ ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
  have hl := (h.normalized_density_limit hR
    (dimensionIntervalCoefficient_pos 3 (by norm_num))).const_mul (-dimensionPairCoefficient 3)
  simpa only [mul_zero, mul_assoc] using hl

end CubicBounds
end Pilot3ShortRemainder
end BoundaryDraft
