import BoundaryDraft.SpacetimeIntegration
import BoundaryDraft.GaussianCancellation

/-!
# Explicit ellipsoid volumes and signed spatial integration

Diagonal scaling is justified in the original product Lebesgue measure by
its determinant. The Euclidean three-ball and the checked radial integral
then give the volume profile and integration formula. The height substitution
is differentiated in the polynomial direction, never through a square root
at the critical height.
-/

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section
namespace BoundaryDraft

private def axisNormalize (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) : Spatial ≃ᵐ Spatial where
  toFun x i := x i / b i
  invFun x i := b i * x i
  left_inv x := by ext i; exact mul_div_cancel₀ (x i) (ne_of_gt (hb i))
  right_inv x := by ext i; exact mul_div_cancel_left₀ (x i) (ne_of_gt (hb i))
  measurable_toFun := by change Measurable (fun x : Spatial => fun i => x i / b i); fun_prop
  measurable_invFun := by change Measurable (fun x : Spatial => fun i => b i * x i); fun_prop

private theorem axisNormalize_map (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    Measure.map (axisNormalize b hb) volume = ENNReal.ofReal (∏ i, b i) • volume := by
  have hp : 0 < ∏ i, b i := Finset.prod_pos fun i _ => hb i
  have hm : (Matrix.diagonal (fun i => (b i)⁻¹)).det ≠ 0 := by
    simpa only [Matrix.det_diagonal, Finset.prod_inv_distrib] using inv_ne_zero hp.ne'
  have he : (axisNormalize b hb : Spatial → Spatial) =
      Matrix.toLin' (Matrix.diagonal (fun i => (b i)⁻¹)) := by
    ext x i
    simp [axisNormalize, Matrix.diagonal_toLin', div_eq_mul_inv, mul_comm]
  rw [he, Real.map_matrix_volume_pi_eq_smul_volume_pi hm]
  simp only [Matrix.det_diagonal, Finset.prod_inv_distrib, inv_inv, abs_of_pos hp]

/-- The axis Jacobian is the product of the positive axes, proved from the
Lebesgue transformation law for a diagonal matrix. No integrability is
needed for this change-of-variables identity for total Bochner integrals. -/
theorem integral_ellipsoid_axis_scaling (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : Spatial → ℝ) :
    (∫ x : Spatial, f (fun i => x i / b i)) = (∏ i, b i) * ∫ x : Spatial, f x := by
  change (∫ x : Spatial, f (axisNormalize b hb x)) = _
  rw [← integral_map_equiv, axisNormalize_map, integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt (Finset.prod_pos fun i _ => hb i)), smul_eq_mul]

private theorem measurableSet_spatial_sq_lt (R : ℝ) :
    MeasurableSet {x : Spatial | ∑ i : Fin 3, x i ^ 2 < R ^ 2} := by
  apply isOpen_lt ?_ continuous_const |>.measurableSet
  fun_prop

private theorem spatial_sq_eq_norm (x : EuclideanSpace ℝ (Fin 3)) :
    (∑ i : Fin 3, ((WithLp.equiv 2 _) x) i ^ 2) = ‖x‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]

/-- Euclidean radial volume in the spatial coordinate-product measure. -/
theorem volume_spatial_sq_lt (R : ℝ) (hR : 0 ≤ R) :
    volume {x : Spatial | ∑ i : Fin 3, x i ^ 2 < R ^ 2} =
      ENNReal.ofReal (4 * Real.pi / 3 * R ^ 3) := by
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).measure_preimage
    (measurableSet_spatial_sq_lt R).nullMeasurableSet]
  have he : (WithLp.equiv 2 (Fin 3 → ℝ)) ⁻¹'
      {x : Spatial | ∑ i : Fin 3, x i ^ 2 < R ^ 2} = Metric.ball 0 R := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, spatial_sq_eq_norm, Metric.mem_ball, dist_zero_right]
    exact sq_lt_sq₀ (norm_nonneg _) hR
  rw [he, EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hR,
    ← ENNReal.ofReal_mul (pow_nonneg hR 3)]
  congr 1
  ring

private theorem spatial_sq_boundary_null (R : ℝ) (hR : 0 ≤ R) :
    volume {x : Spatial | ∑ i : Fin 3, x i ^ 2 = R ^ 2} = 0 := by
  have hm : MeasurableSet {x : Spatial | ∑ i : Fin 3, x i ^ 2 = R ^ 2} := by
    apply isClosed_eq ?_ continuous_const |>.measurableSet
    fun_prop
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).measure_preimage hm.nullMeasurableSet]
  have he : (WithLp.equiv 2 (Fin 3 → ℝ)) ⁻¹'
      {x : Spatial | ∑ i : Fin 3, x i ^ 2 = R ^ 2} = Metric.sphere 0 R := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, spatial_sq_eq_norm, Metric.mem_sphere, dist_zero_right]
    exact sq_eq_sq₀ (norm_nonneg _) hR
  rw [he, Measure.addHaar_sphere]

private theorem spatial_sq_lt_ae_le (R : ℝ) (hR : 0 ≤ R) :
    {x : Spatial | ∑ i : Fin 3, x i ^ 2 < R ^ 2} =ᶠ[ae volume]
      {x : Spatial | ∑ i : Fin 3, x i ^ 2 ≤ R ^ 2} := by
  apply ae_iff.mpr
  apply measure_mono_null _ (spatial_sq_boundary_null R hR)
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  by_contra hn
  exact hx (propext (lt_iff_le_and_ne.trans (and_iff_left hn)))

/-- Above the maximum height even the critical level has an empty strict
superlevel set. This is a set equality, not merely an almost-everywhere claim. -/
theorem ellipsoid_superlevel_empty (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 ≤ a)
    (s : ℝ) (hs : a ≤ s) : {x | s < ellipsoidProfile a b x} = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro x hx
  exact (not_lt_of_ge ((ellipsoidProfile_le a b ha x).trans hs)) hx

/-- Explicit superlevel volume, including both endpoints `s = 0` and `s = a`.
The cube of the square root is `(1-s/a)^(3/2)` on this interval. -/
theorem volume_ellipsoid_superlevel (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (s : ℝ) (hs : s ∈ Icc 0 a) :
    volume {x | s < ellipsoidProfile a b x} =
      ENNReal.ofReal ((4 * Real.pi / 3) * (∏ i, b i) * Real.sqrt (1 - s / a) ^ 3) := by
  have hr : 0 ≤ 1 - s / a := sub_nonneg.mpr ((div_le_one ha).mpr hs.2)
  have he : {x | s < ellipsoidProfile a b x} = (axisNormalize b hb) ⁻¹'
      {x : Spatial | ∑ i : Fin 3, x i ^ 2 < Real.sqrt (1 - s / a) ^ 2} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, Real.sq_sqrt hr]
    change s < a * (1 - ∑ i, (x i / b i) ^ 2) ↔ ∑ i, (x i / b i) ^ 2 < 1 - s / a
    rw [mul_comm a, ← div_lt_iff₀ ha]
    constructor <;> intro h <;> linarith
  rw [he, ← (axisNormalize b hb).map_apply, axisNormalize_map, Measure.smul_apply,
    smul_eq_mul, volume_spatial_sq_lt _ (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (le_of_lt (Finset.prod_pos fun i _ => hb i))]
  congr 1
  ring

/-- Every continuous height integrand is absolutely integrable over the
positive ellipsoid, by domination on its explicit compact coordinate box.
In particular this applies to each signed `planeKernel ρ`. -/
theorem integrableOn_ellipsoid_profile (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (f : ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn (fun x => f (ellipsoidProfile a b x)) {x | 0 < ellipsoidProfile a b x} :=
  (hf.comp (continuous_ellipsoidProfile a b)).integrableOn_Icc.mono_set
    (ellipsoid_positive_subset_box a b ha hb)

/-- The square-root weighted height integrand is absolutely integrable,
including its zero endpoint at the interior critical height `a`. -/
theorem intervalIntegrable_ellipsoid_weight (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable (fun s => Real.sqrt (1 - s / a) * f s) volume 0 a :=
  (by fun_prop : Continuous (fun s => Real.sqrt (1 - s / a) * f s)).intervalIntegrable 0 a

/-- Exact signed integration formula in the actual spatial measure. The class
of globally continuous real integrands includes every concrete plane kernel;
no positivity or differentiability of the integrand is required. -/
theorem integral_ellipsoid_profile (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in {x | 0 < ellipsoidProfile a b x}, f (ellipsoidProfile a b x)) =
      (2 * Real.pi * (∏ i, b i) / a) *
        ∫ s in (0 : ℝ)..a, Real.sqrt (1 - s / a) * f s := by
  let F : Spatial → ℝ := {x : Spatial | ∑ i : Fin 3, x i ^ 2 < 1 ^ 2}.indicator
    (fun x => f (a * (1 - ∑ i : Fin 3, x i ^ 2)))
  have he (x : Spatial) :
      {x | 0 < ellipsoidProfile a b x}.indicator (fun x => f (ellipsoidProfile a b x)) x =
        F (fun i => x i / b i) := by
    simp only [F, Set.indicator, mem_setOf_eq, one_pow, ellipsoidProfile_pos_iff a b ha]
    rfl
  rw [← integral_indicator (measurableSet_ellipsoid_positive a b)]
  simp_rw [he]
  rw [integral_ellipsoid_axis_scaling b hb]
  dsimp only [F]
  rw [integral_indicator (measurableSet_spatial_sq_lt 1),
    setIntegral_congr_set (spatial_sq_lt_ae_le 1 zero_le_one),
    integral_spatial_radial 1 zero_le_one (fun q => f (a * (1 - q))),
    integral_sq_comp_one_sub_sq (fun t => f (a * t)) (hf.comp (continuous_const.mul continuous_id))]
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (fun s => Real.sqrt (1 - s / a) * f s) (a := 0) (b := 1) a
  simp only [smul_eq_mul, mul_zero, mul_one, mul_div_cancel_left₀ _ ha.ne'] at hscale
  rw [← hscale]
  field_simp
  ring

end BoundaryDraft
