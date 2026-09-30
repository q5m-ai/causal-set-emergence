import BoundaryDraft.ShortDisplacementCoordinates
import BoundaryDraft.TruncatedQuadraticJet
import BoundaryDraft.NullTransverseCancellation

/-!
# Nearly-null control of a cubic displacement remainder

Primitive displacement derivative bounds are transported to the actual null
coordinates. The second proper-time derivative is bounded even as the long
coordinate approaches zero. This supplies the domination needed for the
truncated-fibre argument; a mere cubic bound on values would not suffice.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ShortNullRemainder

abbrev Space := ℝ × OverlapSpace

def point (ω : OverlapSphere) (v σ : ℝ) : Space :=
  ((v + σ / v) / 2, ((v - σ / v) / 2) • ω.val)

def direction (ω : OverlapSphere) (v : ℝ) : Space :=
  (1 / (2 * v), (-(1 / (2 * v))) • ω.val)

def jacobian (v σ : ℝ) : ℝ := (v - σ / v) ^ 2 / (8 * v)
def jacobianFirst (v σ : ℝ) : ℝ := -(v - σ / v) / (4 * v ^ 2)
def jacobianSecond (v : ℝ) : ℝ := 1 / (4 * v ^ 3)

def along (R : Space → ℝ) (ω : OverlapSphere) (v σ : ℝ) : ℝ := R (point ω v σ)
def alongFirst (R : Space → ℝ) (ω : OverlapSphere) (v σ : ℝ) : ℝ :=
  fderiv ℝ R (point ω v σ) (direction ω v)
def alongSecond (R : Space → ℝ) (ω : OverlapSphere) (v σ : ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ R) (point ω v σ) (direction ω v) (direction ω v)

def fibre (R : Space → ℝ) (ω : OverlapSphere) (v σ : ℝ) : ℝ :=
  jacobian v σ * along R ω v σ

def first (R : Space → ℝ) (ω : OverlapSphere) (v σ : ℝ) : ℝ :=
  jacobianFirst v σ * along R ω v σ + jacobian v σ * alongFirst R ω v σ

def second (R : Space → ℝ) (ω : OverlapSphere) (v σ : ℝ) : ℝ :=
  jacobianSecond v * along R ω v σ +
    2 * jacobianFirst v σ * alongFirst R ω v σ + jacobian v σ * alongSecond R ω v σ

theorem hasDerivAt_point (ω : OverlapSphere) (v σ : ℝ) :
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

theorem norm_direction (ω : OverlapSphere) {v : ℝ} (hv : 0 < v) :
    ‖direction ω v‖ = 1 / (2 * v) := by
  simp only [direction, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_neg,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, max_self]
  exact abs_of_pos (by positivity)

theorem norm_point_le (ω : OverlapSphere) {v σ : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖point ω v σ‖ ≤ v := by
  have hquot : 0 ≤ σ / v := div_nonneg hσ.1 hv.le
  have hquotv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith only [hσ.2])
  simp only [point, Prod.norm_def, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ω.property, mul_one, max_le_iff]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem hasDerivAt_jacobian (v σ : ℝ) :
    HasDerivAt (jacobian v) (jacobianFirst v σ) σ := by
  convert ((((hasDerivAt_const σ v).sub ((hasDerivAt_id σ).div_const v)).pow 2).div_const
    (8 * v)) using 1
  dsimp only [jacobianFirst, id_eq]
  ring

theorem hasDerivAt_jacobianFirst (v σ : ℝ) :
    HasDerivAt (jacobianFirst v) (jacobianSecond v) σ := by
  convert (((hasDerivAt_const σ v).sub ((hasDerivAt_id σ).div_const v)).neg.div_const
    (4 * v ^ 2)) using 1
  dsimp only [jacobianSecond]
  ring

theorem hasDerivAt_along {R : Space → ℝ} (ω : OverlapSphere) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ)) :
    HasDerivAt (along R ω v) (alongFirst R ω v σ) σ :=
  hR.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_point ω v σ)

theorem hasDerivAt_alongFirst {R : Space → ℝ} (ω : OverlapSphere) (v σ : ℝ)
    (hR : DifferentiableAt ℝ (fderiv ℝ R) (point ω v σ)) :
    HasDerivAt (alongFirst R ω v) (alongSecond R ω v σ) σ := by
  have hd := (hR.hasFDerivAt.comp_hasDerivAt σ (hasDerivAt_point ω v σ)).clm_apply
    (hasDerivAt_const σ (direction ω v))
  simpa only [alongFirst, alongSecond, Function.comp_def, map_zero, zero_add, add_zero] using hd

theorem hasDerivAt_fibre {R : Space → ℝ} (ω : OverlapSphere) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ)) :
    HasDerivAt (fibre R ω v) (first R ω v σ) σ :=
  (hasDerivAt_jacobian v σ).mul (hasDerivAt_along ω v σ hR)

theorem hasDerivAt_first {R : Space → ℝ} (ω : OverlapSphere) (v σ : ℝ)
    (hR : DifferentiableAt ℝ R (point ω v σ))
    (hR' : DifferentiableAt ℝ (fderiv ℝ R) (point ω v σ)) :
    HasDerivAt (first R ω v) (second R ω v σ) σ := by
  convert ((hasDerivAt_jacobianFirst v σ).mul (hasDerivAt_along ω v σ hR)).add
    ((hasDerivAt_jacobian v σ).mul (hasDerivAt_alongFirst ω v σ hR')) using 1
  dsimp only [second]
  ring

/-- No division by zero is used in the Jacobian estimates. -/
theorem jacobian_bounds {v σ : ℝ} (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) :
    |jacobian v σ| ≤ v / 8 ∧ |jacobianFirst v σ| ≤ 1 / (4 * v) ∧
      |jacobianSecond v| = 1 / (4 * v ^ 3) := by
  have hquot : 0 ≤ σ / v := div_nonneg hσ.1 hv.le
  have hquotv : σ / v ≤ v := (div_le_iff₀ hv).mpr (by nlinarith only [hσ.2])
  have hdiff : 0 ≤ v - σ / v := sub_nonneg.mpr hquotv
  refine ⟨?_, ?_, ?_⟩
  · rw [jacobian, abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
    apply (div_le_iff₀ (by positivity : 0 < 8 * v)).mpr
    nlinarith [mul_nonneg hdiff hquot]
  · rw [jacobianFirst, abs_div, abs_neg, abs_of_nonneg hdiff,
      abs_of_pos (by positivity : 0 < 4 * v ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < 4 * v ^ 2)).mpr
    calc
      v - σ / v ≤ v := by linarith
      _ = 1 / (4 * v) * (4 * v ^ 2) := by field_simp; ring
  · rw [jacobianSecond, abs_of_pos (by positivity : 0 < 1 / (4 * v ^ 3))]

/-- The inverse long-coordinate factors are accounted for in both derivatives. -/
theorem along_bounds {R : Space → ℝ} (ω : OverlapSphere) {v σ T : ℝ} (hv : 0 < v)
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

/-- The actual Jacobian cancels the apparent singularities in the second
proper-time derivative. The estimates remain uniform down to positive `v=0`. -/
theorem fibre_bounds {R : Space → ℝ} (ω : OverlapSphere) {v σ T : ℝ}
    (hv : 0 < v) (hσ : σ ∈ Icc 0 (v ^ 2)) (hT : 0 ≤ T)
    (h₀ : ‖R (point ω v σ)‖ ≤ T * v ^ 3)
    (h₁ : ‖fderiv ℝ R (point ω v σ)‖ ≤ T * v ^ 2)
    (h₂ : ‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ ≤ T * v) :
    |fibre R ω v σ| ≤ T * v ^ 4 ∧ |first R ω v σ| ≤ T * v ^ 2 ∧
      |second R ω v σ| ≤ T := by
  obtain ⟨ha, ha₁, ha₂⟩ := along_bounds ω hv h₀ h₁ h₂
  obtain ⟨hj, hj₁, hj₂⟩ := jacobian_bounds hv hσ
  refine ⟨?_, ?_, ?_⟩
  · rw [fibre, abs_mul]
    calc
      _ ≤ (v / 8) * (T * v ^ 3) := by gcongr
      _ ≤ T * v ^ 4 := by nlinarith [mul_nonneg hT (pow_nonneg hv.le 4)]
  · rw [first]
    calc
      _ ≤ |jacobianFirst v σ| * |along R ω v σ| + |jacobian v σ| * |alongFirst R ω v σ| := by
        simpa only [abs_mul] using abs_add (jacobianFirst v σ * along R ω v σ)
          (jacobian v σ * alongFirst R ω v σ)
      _ ≤ (1 / (4 * v)) * (T * v ^ 3) + (v / 8) * (T * v / 2) := by gcongr
      _ = (5 / 16) * T * v ^ 2 := by field_simp; ring
      _ ≤ T * v ^ 2 := by nlinarith [mul_nonneg hT (sq_nonneg v)]
  · rw [second]
    calc
      _ ≤ |jacobianSecond v| * |along R ω v σ| +
          2 * |jacobianFirst v σ| * |alongFirst R ω v σ| + |jacobian v σ| * |alongSecond R ω v σ| := by
        have hb := (abs_add (jacobianSecond v * along R ω v σ +
          2 * jacobianFirst v σ * alongFirst R ω v σ) (jacobian v σ * alongSecond R ω v σ)).trans
            (add_le_add_right (abs_add (jacobianSecond v * along R ω v σ)
              (2 * jacobianFirst v σ * alongFirst R ω v σ)) _)
        simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hb
      _ ≤ (1 / (4 * v ^ 3)) * (T * v ^ 3) +
          2 * (1 / (4 * v)) * (T * v / 2) + (v / 8) * (T / (4 * v)) := by rw [hj₂]; gcongr
      _ = (17 / 32) * T := by field_simp; ring
      _ ≤ T := by linarith

/-- Analytic input to be derived from the geometric overlap extension. These
are primitive differential bounds, not a density jet or an assumed action limit. -/
structure CubicBounds (R : Space → ℝ) (δ T : ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 R (Metric.ball 0 δ)
  nonneg : 0 ≤ T
  value : ∀ z ∈ Metric.ball 0 δ, ‖R z‖ ≤ T * ‖z‖ ^ 3
  first : ∀ z ∈ Metric.ball 0 δ, ‖fderiv ℝ R z‖ ≤ T * ‖z‖ ^ 2
  second : ∀ z ∈ Metric.ball 0 δ, ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ T * ‖z‖

namespace CubicBounds

variable {R : Space → ℝ} {δ T : ℝ} (h : CubicBounds R δ T)
include h

omit h in
theorem point_mem (ω : OverlapSphere) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) : point ω v σ ∈ Metric.ball (0 : Space) δ := by
  simpa only [Metric.mem_ball, dist_zero_right] using (norm_point_le ω hv.1 hσ).trans_lt hv.2

theorem point_bounds (ω : OverlapSphere) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    ‖R (point ω v σ)‖ ≤ T * v ^ 3 ∧
    ‖fderiv ℝ R (point ω v σ)‖ ≤ T * v ^ 2 ∧
    ‖fderiv ℝ (fderiv ℝ R) (point ω v σ)‖ ≤ T * v := by
  have hp := point_mem ω hv hσ
  have hn := norm_point_le ω hv.1 hσ
  have hT := h.nonneg
  refine ⟨(h.value _ hp).trans ?_, (h.first _ hp).trans ?_, (h.second _ hp).trans ?_⟩ <;> gcongr

theorem fibre_deriv (ω : OverlapSphere) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    HasDerivAt (fibre R ω v) (ShortNullRemainder.first R ω v σ) σ :=
  hasDerivAt_fibre ω v σ ((h.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds
    (point_mem ω hv hσ))).differentiableAt (by norm_num))

theorem first_deriv (ω : OverlapSphere) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    HasDerivAt (ShortNullRemainder.first R ω v) (ShortNullRemainder.second R ω v σ) σ := by
  have hs := h.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds (point_mem ω hv hσ))
  exact hasDerivAt_first ω v σ (hs.differentiableAt (by norm_num))
    ((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem bounds (ω : OverlapSphere) {v σ : ℝ} (hv : v ∈ Ioo 0 δ)
    (hσ : σ ∈ Icc 0 (v ^ 2)) :
    |fibre R ω v σ| ≤ T * v ^ 4 ∧ |ShortNullRemainder.first R ω v σ| ≤ T * v ^ 2 ∧
      |ShortNullRemainder.second R ω v σ| ≤ T := by
  obtain ⟨h₀, h₁, h₂⟩ := h.point_bounds ω hv hσ
  exact fibre_bounds ω hv.1 hσ h.nonneg h₀ h₁ h₂

theorem right_quadratic_jet (ω : OverlapSphere) {v : ℝ} (hv : v ∈ Ioo 0 δ) :
    (fun σ => TruncatedQuadraticJet.truncate (fibre R ω v) (v ^ 2) σ -
      (fibre R ω v 0 + ShortNullRemainder.first R ω v 0 * σ +
        ShortNullRemainder.second R ω v 0 / 2 * σ ^ 2)) =o[𝓝[>] 0] (fun σ => σ ^ 2) :=
  TruncatedQuadraticJet.right_quadratic_jet (sq_pos_of_pos hv.1)
    (fun _ hσ => h.fibre_deriv ω hv hσ) (h.first_deriv ω hv ⟨le_rfl, sq_nonneg v⟩)

theorem normalized_remainder_bound (ω : OverlapSphere) {v σ : ℝ}
    (hv : v ∈ Ioo 0 δ) (hσ : 0 < σ) :
    |TruncatedQuadraticJet.truncate (fibre R ω v) (v ^ 2) σ -
      (fibre R ω v 0 + ShortNullRemainder.first R ω v 0 * σ +
        ShortNullRemainder.second R ω v 0 / 2 * σ ^ 2)| / σ ^ 2 ≤ 3 * T := by
  obtain ⟨h₀, h₁, _⟩ := h.bounds ω hv ⟨le_rfl, sq_nonneg v⟩
  apply TruncatedQuadraticJet.normalized_remainder_bound (sq_pos_of_pos hv.1) h.nonneg hσ
    (fun _ hσ => h.fibre_deriv ω hv hσ) (fun _ hσ => h.first_deriv ω hv hσ)
    (fun _ hσ => (h.bounds ω hv hσ).2.2)
  · simpa only [← pow_mul] using h₀
  · exact h₁

end CubicBounds

/-- Fixed finite parameters; the moving lower endpoint is retained by the
indicator in `parameterFibre`, not by deleting a neighborhood of `v=0`. -/
abbrev Parameter (δ : ℝ) := OverlapSphere × Ioo (0 : ℝ) δ

def lengthMeasure (δ : ℝ) : Measure (Ioo (0 : ℝ) δ) := volume.comap Subtype.val

instance finite_lengthMeasure (δ : ℝ) : IsFiniteMeasure (lengthMeasure δ) := by
  constructor
  rw [lengthMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply,
    Set.image_univ, Subtype.range_coe]
  exact measure_Ioo_lt_top

def parameterMeasure (δ : ℝ) : Measure (Parameter δ) := overlapSphereMeasure.prod (lengthMeasure δ)

instance finite_parameterMeasure (δ : ℝ) : IsFiniteMeasure (parameterMeasure δ) :=
  inferInstanceAs (IsFiniteMeasure (overlapSphereMeasure.prod (lengthMeasure δ)))

def parameterFibre (R : Space → ℝ) (δ : ℝ) (p : Parameter δ) (σ : ℝ) : ℝ :=
  TruncatedQuadraticJet.truncate (fibre R p.1 p.2.val) (p.2.val ^ 2) σ

def density (R : Space → ℝ) (δ σ : ℝ) : ℝ :=
  ∫ p, parameterFibre R δ p σ ∂parameterMeasure δ

theorem measurable_parameterFibre {R : Space → ℝ} (hR : Measurable R) (δ : ℝ) :
    Measurable (fun p : ℝ × Parameter δ => parameterFibre R δ p.2 p.1) := by
  unfold parameterFibre TruncatedQuadraticJet.truncate fibre along jacobian point
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop

theorem measurable_density {R : Space → ℝ} (hR : Measurable R) (δ : ℝ) :
    Measurable (density R δ) :=
  (measurable_parameterFibre hR δ).stronglyMeasurable.integral_prod_right'.measurable

namespace CubicBounds

variable {R : Space → ℝ} {δ T : ℝ} (h : CubicBounds R δ T)
include h

theorem parameterFibre_bound (p : Parameter δ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖parameterFibre R δ p σ‖ ≤ T * δ ^ 4 := by
  unfold parameterFibre TruncatedQuadraticJet.truncate
  split_ifs with hs
  · exact (h.bounds p.1 p.2.property ⟨hσ, hs⟩).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.2.property.1.le p.2.property.2.le 4) h.nonneg)
  · rw [norm_zero]
    exact mul_nonneg h.nonneg (pow_nonneg (le_of_lt (p.2.property.1.trans p.2.property.2)) 4)

theorem density_bound {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖density R δ σ‖ ≤ T * δ ^ 4 * (parameterMeasure δ).real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun p => h.parameterFibre_bound p hσ)

theorem integrable_parameterFibre (hR : Measurable R) {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (fun p => parameterFibre R δ p σ) (parameterMeasure δ) := by
  apply (integrable_const (T * δ ^ 4)).mono'
    (((measurable_parameterFibre hR δ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun p => h.parameterFibre_bound p hσ

/-- The averaged density has a right quadratic jet with no common lower bound
on the positive fibre cutoffs. -/
theorem density_right_quadratic_jet (hR : Measurable R) :
    ∃ b₀ b₁ b₂ : ℝ, (fun σ => density R δ σ - (b₀ + b₁ * σ + b₂ * σ ^ 2)) =o[𝓝[>] 0]
      (fun σ => σ ^ 2) := by
  let F := fun (p : Parameter δ) σ => fibre R p.1 p.2.val σ
  let F' := fun (p : Parameter δ) σ => ShortNullRemainder.first R p.1 p.2.val σ
  let F'' := fun (p : Parameter δ) σ => ShortNullRemainder.second R p.1 p.2.val σ
  let q := fun p : Parameter δ => p.2.val ^ 2
  refine ⟨∫ p, F p 0 ∂parameterMeasure δ, ∫ p, F' p 0 ∂parameterMeasure δ,
    ∫ p, F'' p 0 / 2 ∂parameterMeasure δ, ?_⟩
  apply TruncatedQuadraticJet.averaged_right_quadratic_jet F F' F'' q (fun _ => T) (Q := δ ^ 2)
  · intro p
    exact ⟨sq_pos_of_pos p.2.property.1,
      pow_le_pow_left₀ p.2.property.1.le p.2.property.2.le 2⟩
  · exact fun _ => h.nonneg
  · exact integrable_const T
  · intro σ _
    exact (measurable_parameterFibre hR δ).comp (measurable_const.prodMk measurable_id)
  · exact fun p _ hσ => h.fibre_deriv p.1 p.2.property hσ
  · exact fun p _ hσ => h.first_deriv p.1 p.2.property hσ
  · exact fun p _ hσ => (h.bounds p.1 p.2.property hσ).2.2
  · intro p
    dsimp only [F, q]
    simpa only [← pow_mul] using (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).1
  · exact fun p => (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).2.1

/-- Identification with the actual angular/long-coordinate remainder integral,
with absolute integrability supplied before Fubini. -/
theorem density_eq_iterated (hR : Measurable R) {σ : ℝ} (hσ : 0 ≤ σ) :
    density R δ σ = ∫ ω, (∫ v in Ioo (0 : ℝ) δ,
      if σ ≤ v ^ 2 then jacobian v σ * R (point ω v σ) else 0) ∂overlapSphereMeasure := by
  rw [density, parameterMeasure, integral_prod _ (h.integrable_parameterFibre hR hσ)]
  apply integral_congr_ae
  filter_upwards with ω
  exact integral_subtype_comap measurableSet_Ioo
    (fun v => if σ ≤ v ^ 2 then jacobian v σ * R (point ω v σ) else 0)

/-- The normalized nearly-null remainder vanishes. The geometric producer of
`CubicBounds` is a separate obligation; it is not part of admissibility. -/
theorem normalized_density_limit (hR : Measurable R) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => Real.sqrt ρ * ρ * ∫ σ : ℝ in Ioi 0,
      density R δ σ * bdgKernel (c * ρ * σ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨b₀, b₁, b₂, hj⟩ := h.density_right_quadratic_jet hR
  have hl := bdgKernel_transverse_cancellation (density R δ) (measurable_density hR δ)
    (T * δ ^ 4 * (parameterMeasure δ).real univ) (fun _ hs => h.density_bound hs.le)
    b₀ b₁ b₂ hj c hc
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have he : ρ ^ (3 / 2 : ℝ) = Real.sqrt ρ ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  rw [he]
  congr 1
  nlinarith only [congrArg (fun t : ℝ => Real.sqrt ρ * t) (Real.sq_sqrt hρ.le)]

end CubicBounds
end ShortNullRemainder
end BoundaryDraft
