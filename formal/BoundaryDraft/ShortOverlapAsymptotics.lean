import BoundaryDraft.ShortOverlapDensity
import BoundaryDraft.ShortNullRemainder
import BoundaryDraft.ShortRadialQuadraticLimit
import BoundaryDraft.ShortRadialIntegral

/-!
# From an angular overlap expansion to the short-density response

This is a conditional analytic intermediate theorem. Its angular input concerns
the actual translated overlaps of two bounded measurable regions. The producer
of that expansion and of the primitive cubic remainder bounds is separate.
Neither an overlap expansion nor a limit is added to admissibility.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
namespace ShortOverlapAsymptotics

/-- The sole angular expansion input. In particular, it is not a hypothesis
about the averaged proper-time density or its limiting action. -/
def AngularExpansion (M N : Set Spacetime) (δ : ℝ)
    (R : ShortNullRemainder.Space → ℝ) (C : ℝ) : Prop :=
  ∀ σ : ℝ, 0 < σ → ∀ v ∈ Ioo (0 : ℝ) δ, σ ≤ v ^ 2 →
    (∫ ω : OverlapSphere,
      (translatedOverlap M (properTimeDisplacement ω ![σ,v]) -
        translatedOverlap N (properTimeDisplacement ω ![σ,v])) -
          R (ShortNullRemainder.point ω v σ) ∂overlapSphereMeasure) =
      C * ((v - σ / v) / 2) ^ 2

/-- The truncated real remainder fibre on the same ambient product used by
the overlap density. No positive neighborhood of the null endpoint is deleted. -/
def remainderFibre (R : ShortNullRemainder.Space → ℝ) (σ : ℝ)
    (ω : OverlapSphere) (v : ℝ) : ℝ :=
  if σ ≤ v ^ 2 then ShortNullRemainder.jacobian v σ *
    R (ShortNullRemainder.point ω v σ) else 0

theorem measurable_remainderFibre {R : ShortNullRemainder.Space → ℝ}
    (hR : Measurable R) (σ : ℝ) :
    Measurable (fun p : OverlapSphere × ℝ => remainderFibre R σ p.1 p.2) := by
  unfold remainderFibre ShortNullRemainder.jacobian ShortNullRemainder.point
  apply Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) <;> fun_prop

theorem remainderFibre_bound {R : ShortNullRemainder.Space → ℝ} {δ T : ℝ}
    (h : ShortNullRemainder.CubicBounds R δ T) {σ : ℝ} (hσ : 0 ≤ σ)
    (ω : OverlapSphere) (v : ℝ) (hv : v ∈ Ioo 0 δ) :
    ‖remainderFibre R σ ω v‖ ≤ T * δ ^ 4 := by
  change ‖ShortNullRemainder.parameterFibre R δ (ω, ⟨v, hv⟩) σ‖ ≤ _
  exact h.parameterFibre_bound _ hσ

/-- Joint absolute integrability before any signed Fubini or subtraction. -/
theorem integrable_remainderFibre {R : ShortNullRemainder.Space → ℝ} {δ T : ℝ}
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Integrable (fun p : OverlapSphere × ℝ => remainderFibre R σ p.1 p.2)
      (overlapSphereMeasure.prod (volume.restrict (Ioo 0 δ))) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) δ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hv : ∀ᵐ p : OverlapSphere × ℝ
      ∂overlapSphereMeasure.prod (volume.restrict (Ioo 0 δ)), p.2 ∈ Ioo 0 δ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
      (Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioo)
  apply (integrable_const (T * δ ^ 4)).mono'
    (measurable_remainderFibre hR σ).aestronglyMeasurable
  filter_upwards [hv] with p hp
  exact remainderFibre_bound h hσ p.1 p.2 hp

private theorem measurable_angular_overlap {M : Set Spacetime} (hm : MeasurableSet M)
    (σ v : ℝ) :
    Measurable (fun ω : OverlapSphere => translatedOverlap M (properTimeDisplacement ω ![σ,v])) :=
  (measurable_translatedOverlap hm).comp
    (measurable_properTimeDisplacement.comp
      (measurable_id.prodMk (measurable_const (a := (![σ,v] : Plane)))))

/-- Every angular overlap integral in the expansion is a genuine finite
integral, not just the default value of a nonintegrable function. -/
theorem integrable_angular_overlap {M : Set Spacetime} (hm : MeasurableSet M)
    (hb : Bornology.IsBounded M) (σ v : ℝ) :
    Integrable (fun ω : OverlapSphere => translatedOverlap M (properTimeDisplacement ω ![σ,v]))
      overlapSphereMeasure := by
  apply (integrable_const (volume.real M)).mono'
    (measurable_angular_overlap hm σ v).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (translatedOverlap_nonneg M _)]
    exact translatedOverlap_le_volume hm hb _

/-- The unweighted angular remainder also has a finite integral at every
parameter where the expansion is used. -/
theorem integrable_angular_remainder {R : ShortNullRemainder.Space → ℝ} {δ T : ℝ}
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    {σ v : ℝ} (hσ : σ ∈ Icc 0 (v ^ 2)) (hv : v ∈ Ioo 0 δ) :
    Integrable (fun ω : OverlapSphere => R (ShortNullRemainder.point ω v σ)) overlapSphereMeasure := by
  apply (integrable_const (T * v ^ 3)).mono'
    ((hR.comp (by unfold ShortNullRemainder.point; fun_prop)).aestronglyMeasurable)
  exact Eventually.of_forall fun ω => (h.point_bounds ω hv hσ).1

theorem integrable_angular_residual {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    {R : ShortNullRemainder.Space → ℝ} {δ T : ℝ}
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    {σ v : ℝ} (hσ : σ ∈ Icc 0 (v ^ 2)) (hv : v ∈ Ioo 0 δ) :
    Integrable (fun ω : OverlapSphere =>
      (translatedOverlap M (properTimeDisplacement ω ![σ,v]) -
        translatedOverlap N (properTimeDisplacement ω ![σ,v])) -
          R (ShortNullRemainder.point ω v σ)) overlapSphereMeasure :=
  ((integrable_angular_overlap hm hb σ v).sub (integrable_angular_overlap hn hnb σ v)).sub
    (integrable_angular_remainder h hR hσ hv)

/-- The density difference is reduced to the radial-square integral by the
actual angular input. All three product integrands are proved integrable
before subtracting and swapping the angular and long-coordinate integrals. -/
theorem density_decomposition_fibre {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    {R : ShortNullRemainder.Space → ℝ} {δ T C : ℝ}
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    (ha : AngularExpansion M N δ R C) {σ : ℝ} (hσ : 0 < σ) :
    shortOverlapDensity M δ σ - shortOverlapDensity N δ σ =
      C * (∫ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then
        ShortNullRemainder.jacobian v σ * ((v - σ / v) / 2) ^ 2 else 0) +
          ShortNullRemainder.density R δ σ := by
  let μ := overlapSphereMeasure.prod (volume.restrict (Ioo (0 : ℝ) δ))
  let F : OverlapSphere × ℝ → ℝ := fun p =>
    shortOverlapFibre M σ p.1 p.2 - shortOverlapFibre N σ p.1 p.2 - remainderFibre R σ p.1 p.2
  have hiM := integrable_shortOverlapFibre hm hb δ hσ.le
  have hiN := integrable_shortOverlapFibre hn hnb δ hσ.le
  have hiR := integrable_remainderFibre h hR hσ.le
  have hiF : Integrable F μ := (hiM.sub hiN).sub hiR
  have hdM : shortOverlapDensity M δ σ = ∫ p, shortOverlapFibre M σ p.1 p.2 ∂μ :=
    (shortOverlapDensity_eq_average hm hb δ hσ.le).trans (integral_prod _ hiM).symm
  have hdN : shortOverlapDensity N δ σ = ∫ p, shortOverlapFibre N σ p.1 p.2 ∂μ :=
    (shortOverlapDensity_eq_average hn hnb δ hσ.le).trans (integral_prod _ hiN).symm
  have hdR : ShortNullRemainder.density R δ σ = ∫ p, remainderFibre R σ p.1 p.2 ∂μ :=
    (h.density_eq_iterated hR hσ.le).trans (integral_prod _ hiR).symm
  have he : shortOverlapDensity M δ σ - shortOverlapDensity N δ σ -
      ShortNullRemainder.density R δ σ =
      C * (∫ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then
        ShortNullRemainder.jacobian v σ * ((v - σ / v) / 2) ^ 2 else 0) := by
    calc
      _ = ∫ p, F p ∂μ := by
        rw [hdM, hdN, hdR]
        have he₁ := integral_sub (hiM.sub hiN) hiR
        have he₂ := integral_sub hiM hiN
        simp only [Pi.sub_apply] at he₁ he₂
        rw [he₂] at he₁
        exact he₁.symm
      _ = ∫ v in Ioo (0 : ℝ) δ, ∫ ω, F (ω, v) ∂overlapSphereMeasure :=
        integral_prod_symm _ hiF
      _ = C * (∫ v in Ioo (0 : ℝ) δ, if σ ≤ v ^ 2 then
          ShortNullRemainder.jacobian v σ * ((v - σ / v) / 2) ^ 2 else 0) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro v hv
        by_cases hs : σ ≤ v ^ 2
        · have hpoint (ω : OverlapSphere) : F (ω, v) = ShortNullRemainder.jacobian v σ *
              ((translatedOverlap M (properTimeDisplacement ω ![σ,v]) -
                translatedOverlap N (properTimeDisplacement ω ![σ,v])) -
                  R (ShortNullRemainder.point ω v σ)) := by
            dsimp only [F, shortOverlapFibre, remainderFibre]
            rw [if_pos hs, if_pos hs, if_pos hs]
            dsimp only [ShortNullRemainder.jacobian]
            ring
          simp_rw [hpoint]
          rw [integral_const_mul, ha σ hσ v hv hs, if_pos hs]
          ring
        · have hpoint (ω : OverlapSphere) : F (ω, v) = 0 := by
            simp [F, shortOverlapFibre, remainderFibre, hs]
          simp only [hpoint, integral_zero, if_neg hs, mul_zero]
  linarith

/-- Pointwise decomposition into the actual fixed-cutoff radial response and
the actual cubic-remainder density. The angular input is used only at positive
proper-time square and within the unchanged proper-time domain. -/
theorem density_decomposition {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    {R : ShortNullRemainder.Space → ℝ} {δ T C : ℝ} (hδ : 0 < δ)
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    (ha : AngularExpansion M N δ R C) {σ : ℝ} (hσ : 0 < σ) :
    shortOverlapDensity M δ σ - shortOverlapDensity N δ σ =
      C * shortRadialQuadratic δ σ + ShortNullRemainder.density R δ σ := by
  have hr := shortRadialQuadratic_eq_integral_fibre hδ hσ
  simpa only [ShortNullRemainder.jacobian, ← hr] using
    density_decomposition_fibre hm hb hn hnb h hR ha hσ

/-- Kernel integrability of the remainder follows from its derived uniform
density bound and the full absolutely integrable signed BDG kernel. -/
theorem integrableOn_remainder_density_kernel {R : ShortNullRemainder.Space → ℝ} {δ T : ℝ}
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    IntegrableOn (fun σ : ℝ => ShortNullRemainder.density R δ σ *
      bdgKernel (c * ρ * σ ^ 2)) (Ioi 0) :=
  integrableOn_bdgKernel_density_mul_bounded (ShortNullRemainder.density R δ)
    (ShortNullRemainder.measurable_density hR δ)
    (T * δ ^ 4 * (ShortNullRemainder.parameterMeasure δ).real univ)
    (fun _ hσ => h.density_bound hσ.le) c ρ hc hρ

/-- The actual difference density is integrable against any continuous test
kernel before using the angular expansion. -/
theorem integrableOn_density_difference_weight {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    (δ : ℝ) (w : ℝ → ℝ) (hw : Continuous w) :
    IntegrableOn (fun σ : ℝ => (shortOverlapDensity M δ σ - shortOverlapDensity N δ σ) * w σ)
      (Ioi 0) := by
  have hi := ((integrable_shortOverlapDensity_weight hm hb δ w hw).sub
    (integrable_shortOverlapDensity_weight hn hnb δ w hw)).restrict (s := Ioi 0)
  apply hi.congr
  exact Eventually.of_forall fun σ => by dsimp only [Pi.sub_apply]; ring

/-- Exact finite-density splitting of the signed kernel integral. The
radial and remainder terms are proved absolutely integrable before applying
linearity, and the original density difference is integrable independently. -/
theorem integral_density_decomposition {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    {R : ShortNullRemainder.Space → ℝ} {δ T C : ℝ} (hδ : 0 < δ)
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    (ha : AngularExpansion M N δ R C) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) :
    (∫ σ : ℝ in Ioi 0, (shortOverlapDensity M δ σ - shortOverlapDensity N δ σ) *
      bdgKernel (c * ρ * σ ^ 2)) =
      C * (∫ σ : ℝ in Ioi 0, shortRadialQuadratic δ σ * bdgKernel (c * ρ * σ ^ 2)) +
        ∫ σ : ℝ in Ioi 0, ShortNullRemainder.density R δ σ * bdgKernel (c * ρ * σ ^ 2) := by
  have hiQ := integrableOn_shortRadialQuadratic hδ hc hρ
  have hiR := integrableOn_remainder_density_kernel h hR hc hρ
  calc
    _ = ∫ σ : ℝ in Ioi 0,
        C * (shortRadialQuadratic δ σ * bdgKernel (c * ρ * σ ^ 2)) +
          ShortNullRemainder.density R δ σ * bdgKernel (c * ρ * σ ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro σ hσ
      dsimp only
      rw [density_decomposition hm hb hn hnb hδ h hR ha hσ]
      ring
    _ = _ := by rw [integral_add (hiQ.const_mul C) hiR, integral_const_mul]

/-- The physical signed BDG normalization of an actual angular overlap
expansion. This is conditional analytic gluing, not a claim that the expansion
has been derived for every admissible geometry. -/
theorem bdg_action_limit {M N : Set Spacetime}
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M)
    (hn : MeasurableSet N) (hnb : Bornology.IsBounded N)
    {R : ShortNullRemainder.Space → ℝ} {δ T C : ℝ} (hδ : 0 < δ)
    (h : ShortNullRemainder.CubicBounds R δ T) (hR : Measurable R)
    (ha : AngularExpansion M N δ R C) :
    Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * Real.sqrt ρ * ρ *
      ∫ σ : ℝ in Ioi 0, (shortOverlapDensity M δ σ - shortOverlapDensity N δ σ) *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2)) atTop (𝓝 ((-3 / (2 * Real.pi)) * C)) := by
  have hc : 0 < Real.pi / 24 := by positivity
  have hr : Tendsto (fun ρ : ℝ => -(4 / Real.sqrt 6) * (Real.sqrt ρ * ρ *
      ∫ σ : ℝ in Ioi 0, ShortNullRemainder.density R δ σ *
        bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (h.normalized_density_limit hR hc).const_mul (-(4 / Real.sqrt 6))
  have hl := ((bdg_shortRadialQuadratic_action_limit hδ).mul_const C).add hr
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  rw [integral_density_decomposition hm hb hn hnb hδ h hR ha hc hρ]
  ring

end ShortOverlapAsymptotics
end BoundaryDraft
