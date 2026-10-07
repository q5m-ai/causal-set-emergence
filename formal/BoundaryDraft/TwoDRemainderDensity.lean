import BoundaryDraft.TwoDShortRemainder

/-! # Actual signed 2D remainder density: finite fibres, Fubini and an affine right jet -/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace TwoDShortRemainder

/-- The fixed finite parameter domain includes all positive long coordinates,
with no common lower cutoff. -/
abbrev Parameter (δ : ℝ) := TwoDDirection × Ioo (0 : ℝ) δ

def lengthMeasure (δ : ℝ) : Measure (Ioo (0 : ℝ) δ) := volume.comap Subtype.val

instance finite_lengthMeasure (δ : ℝ) : IsFiniteMeasure (lengthMeasure δ) := by
  constructor
  rw [lengthMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply,
    Set.image_univ, Subtype.range_coe]
  exact measure_Ioo_lt_top

def parameterMeasure (δ : ℝ) : Measure (Parameter δ) := twoDDirectionMeasure.prod (lengthMeasure δ)

instance finite_parameterMeasure (δ : ℝ) : IsFiniteMeasure (parameterMeasure δ) :=
  inferInstanceAs (IsFiniteMeasure (twoDDirectionMeasure.prod (lengthMeasure δ)))

def parameterFibre (R : Space → ℝ) (δ : ℝ) (p : Parameter δ) (σ : ℝ) : ℝ :=
  TruncatedAffineJet.truncate (fibre R p.1 p.2.val) (p.2.val ^ 2) σ

/-- The actual truncated remainder density, expressed on a fixed product
space. `density_eq_iterated` identifies the two-direction/long-coordinate integral. -/
def density (R : Space → ℝ) (δ σ : ℝ) : ℝ :=
  ∫ p, parameterFibre R δ p σ ∂parameterMeasure δ

theorem measurable_parameterFibre {R : Space → ℝ} (hR : Measurable R) (δ : ℝ) :
    Measurable (fun p : ℝ × Parameter δ => parameterFibre R δ p.2 p.1) := by
  unfold parameterFibre TruncatedAffineJet.truncate fibre twoDNullJacobian point
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop

theorem measurable_density {R : Space → ℝ} (hR : Measurable R) (δ : ℝ) :
    Measurable (density R δ) :=
  (measurable_parameterFibre hR δ).stronglyMeasurable.integral_prod_right'.measurable

namespace CubicBounds

variable {R : Space → ℝ} {δ T : ℝ} (h : CubicBounds R δ T)
include h

theorem parameterFibre_bound (p : Parameter δ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖parameterFibre R δ p σ‖ ≤ T * δ ^ 2 := by
  unfold parameterFibre TruncatedAffineJet.truncate
  split_ifs with hs
  · exact (h.bounds p.1 p.2.property ⟨hσ, hs⟩).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.2.property.1.le p.2.property.2.le 2) h.nonneg)
  · rw [norm_zero]
    exact mul_nonneg h.nonneg (pow_nonneg (le_of_lt (p.2.property.1.trans p.2.property.2)) 2)

theorem density_bound {σ : ℝ} (hσ : 0 ≤ σ) :
    ‖density R δ σ‖ ≤ T * δ ^ 2 * (parameterMeasure δ).real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun p => h.parameterFibre_bound p hσ)

theorem integrable_parameterFibre (hR : Measurable R) {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (fun p => parameterFibre R δ p σ) (parameterMeasure δ) := by
  apply (integrable_const (T * δ ^ 2)).mono'
    (((measurable_parameterFibre hR δ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun p => h.parameterFibre_bound p hσ

/-- Absolute integrability is established before this signed Fubini identity. -/
theorem density_eq_iterated (hR : Measurable R) {σ : ℝ} (hσ : 0 ≤ σ) :
    density R δ σ = ∫ ω, (∫ v in Ioo (0 : ℝ) δ,
      if σ ≤ v ^ 2 then twoDNullJacobian σ v * R (point ω v σ) else 0)
        ∂twoDDirectionMeasure := by
  rw [density, parameterMeasure, integral_prod _ (h.integrable_parameterFibre hR hσ)]
  apply integral_congr_ae
  filter_upwards with ω
  exact integral_subtype_comap measurableSet_Ioo
    (fun v => if σ ≤ v ^ 2 then twoDNullJacobian σ v * R (point ω v σ) else 0)

/-- First-order affine little-o, derived using the cutoff-compensated
inverse-square bound. No finite original-overlap fibre at sigma zero is asserted. -/
theorem density_right_affine_jet (hR : Measurable R) :
    ∃ b₀ b₁ : ℝ, (fun σ => density R δ σ - (b₀ + b₁ * σ)) =o[𝓝[>] 0]
      (fun σ => σ) := by
  let F := fun (p : Parameter δ) σ => fibre R p.1 p.2.val σ
  let F' := fun (p : Parameter δ) σ => TwoDShortRemainder.first R p.1 p.2.val σ
  let F'' := fun (p : Parameter δ) σ => TwoDShortRemainder.second R p.1 p.2.val σ
  let q := fun p : Parameter δ => p.2.val ^ 2
  let B := fun p : Parameter δ => T / p.2.val ^ 2
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
    apply (integrable_const (T * δ ^ 2)).mono' hm₀.aestronglyMeasurable
    filter_upwards with p
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).1.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.2.property.1.le p.2.property.2.le 2) h.nonneg)
  have hi₁ : Integrable (fun p => F' p 0) (parameterMeasure δ) := by
    apply (integrable_const T).mono' hm₁.aestronglyMeasurable
    filter_upwards with p
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).2.1
  refine ⟨∫ p, F p 0 ∂parameterMeasure δ, ∫ p, F' p 0 ∂parameterMeasure δ, ?_⟩
  apply TruncatedLinearJet.averaged_right_linear_jet F F' F'' q B hq
  · exact fun p => div_nonneg h.nonneg (sq_nonneg _)
  · have he : (fun p => B p * q p) = fun _ : Parameter δ => T := by
      funext p
      dsimp only [B, q]
      exact div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos p.2.property.1))
    rw [he]
    exact integrable_const T
  · exact hm
  · exact hd
  · exact hd'
  · exact fun p _ hσ => (h.bounds p.1 p.2.property hσ).2.2
  · intro p
    have he : B p * q p ^ 2 = T * p.2.val ^ 2 := by
      dsimp [B, q]
      field_simp [p.2.property.1.ne']
      ring
    rw [he]
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).1
  · intro p
    have he : B p * q p = T := by
      dsimp [B, q]
      field_simp [p.2.property.1.ne']
    rw [he]
    exact (h.bounds p.1 p.2.property ⟨le_rfl, sq_nonneg _⟩).2.1
  · exact hi₀
  · exact hi₁

end CubicBounds
end TwoDShortRemainder
end BoundaryDraft
