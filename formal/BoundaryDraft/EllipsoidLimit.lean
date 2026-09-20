import BoundaryDraft.EllipsoidIntegration
import BoundaryDraft.KernelHalfLine

/-!
# The deterministic continuum limit for ellipsoidal graph caps

The global weight is constant below zero, agrees with the exact square-root
height density on `[0,a]`, and vanishes above `a`. It is bounded and continuous,
not globally C¹. This lets the checked signed-rescaling theorem control the
whole ellipsoid, including the critical point, without discarding a tail.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology Interval

noncomputable section
namespace BoundaryDraft

/-- Bounded continuous extension of the ellipsoid height density. Real square
root is zero on nonpositive arguments; `max 0 s` makes the left extension
constant rather than unbounded. -/
def ellipsoidWeight (a : ℝ) (b : Fin 3 → ℝ) (s : ℝ) : ℝ :=
  (2 * Real.pi * (∏ i, b i) / a) * Real.sqrt (1 - max 0 s / a)

theorem continuous_ellipsoidWeight (a : ℝ) (b : Fin 3 → ℝ) :
    Continuous (ellipsoidWeight a b) := by
  unfold ellipsoidWeight
  fun_prop

theorem ellipsoidWeight_of_nonneg (a : ℝ) (b : Fin 3 → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    ellipsoidWeight a b s = (2 * Real.pi * (∏ i, b i) / a) * Real.sqrt (1 - s / a) := by
  rw [ellipsoidWeight, max_eq_right hs]

@[simp] theorem ellipsoidWeight_zero (a : ℝ) (b : Fin 3 → ℝ) :
    ellipsoidWeight a b 0 = 2 * Real.pi * (∏ i, b i) / a := by
  simp [ellipsoidWeight]

/-- The extension is zero at and above the critical height. -/
theorem ellipsoidWeight_of_ge (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (s : ℝ) (hs : a ≤ s) : ellipsoidWeight a b s = 0 := by
  rw [ellipsoidWeight_of_nonneg a b s (ha.le.trans hs),
    Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr ((le_div_iff₀ ha).mpr (by simpa using hs))), mul_zero]

/-- Uniform bound on the entire real line, not just a regular boundary collar. -/
theorem norm_ellipsoidWeight_le (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (s : ℝ) :
    ‖ellipsoidWeight a b s‖ ≤ |2 * Real.pi * (∏ i, b i) / a| := by
  rw [ellipsoidWeight, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (Real.sqrt_le_one.mpr (sub_le_self _ (div_nonneg (le_max_left _ _) ha.le)))

/-- The extended height integral is absolutely integrable for every
continuous signed integrand, in particular `planeKernel ρ`. Compactness handles
`[0,a]`; above `a` the integrand is identically zero. -/
theorem integrableOn_ellipsoid_weight_mul (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (f : ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn (fun s => f s * ellipsoidWeight a b s) (Ioi (0 : ℝ)) := by
  have hc : IntegrableOn (fun s => f s * ellipsoidWeight a b s) (Ioc 0 a) :=
    ((hf.mul (continuous_ellipsoidWeight a b)).intervalIntegrable 0 a).1
  have ht : IntegrableOn (fun s => f s * ellipsoidWeight a b s) (Ioi a) := by
    refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro s hs
    dsimp only
    rw [ellipsoidWeight_of_ge a b ha s hs.le, mul_zero]
  simpa only [Ioc_union_Ioi_eq_Ioi ha.le] using hc.union ht

/-- Extending the exact signed integral to the half-line adds only zeros.
There is no omitted moving-domain or interior remainder term. -/
theorem integral_ellipsoid_profile_eq_halfLine (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in {x | 0 < ellipsoidProfile a b x}, f (ellipsoidProfile a b x)) =
      ∫ s in Ioi (0 : ℝ), f s * ellipsoidWeight a b s := by
  have hsupport : (∫ s in Ioi (0 : ℝ), f s * ellipsoidWeight a b s) =
      ∫ s in (0 : ℝ)..a, f s * ellipsoidWeight a b s := by
    rw [intervalIntegral.integral_of_le ha.le]
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro s hs
    have has : a ≤ s := by
      by_contra h
      exact hs.2 ⟨hs.1, le_of_not_ge h⟩
    rw [ellipsoidWeight_of_ge a b ha s has, mul_zero]
  rw [hsupport, integral_ellipsoid_profile a b ha hb f hf, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (show s ∈ Icc (0 : ℝ) a by simpa [uIcc_of_le ha.le] using hs).1
  dsimp only
  rw [ellipsoidWeight_of_nonneg a b s hs0]
  ring

/-- Absolute integrability of the full rescaled signed integrand, from the
proved kernel integrability and the actual global weight bound. -/
theorem integrableOn_ellipsoid_rescaled (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (ε : ℝ) :
    IntegrableOn (fun u => planeKernel 1 u * ellipsoidWeight a b (ε * u)) (Ioi (0 : ℝ)) := by
  apply (integrableOn_planeKernel.norm.const_mul |2 * Real.pi * (∏ i, b i) / a|).mono'
    ((continuous_planeKernel 1).mul
      ((continuous_ellipsoidWeight a b).comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    simp only [norm_mul, Function.comp_apply, id_eq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (norm_ellipsoidWeight_le a b ha (ε * u)) (norm_nonneg (planeKernel 1 u))

/-- Exact positive-density identity with a fixed half-line domain and the
original signed kernel. It reuses the checked four-dimensional graph reduction. -/
theorem ellipsoid_continuumMean_eq_rescaled (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (graphCapRegion (ellipsoidProfile a b)) =
      ∫ u in Ioi (0 : ℝ), planeKernel 1 u *
        ellipsoidWeight a b ((Real.sqrt (Real.sqrt ρ))⁻¹ * u) := by
  have hb0 : ∀ i, 0 < b i := fun i => lt_trans (by linarith) (hb i)
  rw [ellipsoid_graphReduction a b ha hb ρ hρ,
    integral_ellipsoid_profile_eq_halfLine a b ha hb0 _ (continuous_planeKernel ρ)]
  let k := Real.sqrt (Real.sqrt ρ)
  have hk : 0 < k := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hρ)
  have hscale := integral_comp_mul_left_Ioi
    (fun u => planeKernel 1 u * ellipsoidWeight a b (k⁻¹ * u)) 0 hk
  simp only [mul_zero, smul_eq_mul, inv_mul_cancel_left₀ hk.ne'] at hscale
  have he : (∫ s in Ioi (0 : ℝ), planeKernel ρ s * ellipsoidWeight a b s) =
      k * ∫ s in Ioi (0 : ℝ), planeKernel 1 (k * s) * ellipsoidWeight a b s := by
    simp_rw [planeKernel_density_scaling ρ _ hρ, mul_assoc]
    exact integral_const_mul _ _
  rw [he, hscale, mul_inv_cancel_left₀ hk.ne']

/-- The density-to-width limit, proved using continuity of square root at zero
and the reciprocal limit. Positivity is needed only in the finite-density
identity, and holds eventually as density tends to infinity. -/
theorem tendsto_density_width :
    Tendsto (fun ρ : ℝ => (Real.sqrt (Real.sqrt ρ))⁻¹) atTop (𝓝 0) := by
  simpa only [Real.sqrt_inv, Real.sqrt_zero] using
    (tendsto_inv_atTop_zero : Tendsto (fun ρ : ℝ => ρ⁻¹) atTop (𝓝 0)).sqrt.sqrt

/-- Proof of the existing, unchanged deterministic four-dimensional target.
This says nothing about Poisson expectations, Lorentzian joint angles,
arbitrary graph caps, or the separate null-cap target. -/
theorem ellipsoidLimitGoal : EllipsoidLimitGoal := by
  intro a b ha hb
  have h := (planeKernel_rescaling_limit (ellipsoidWeight a b)
    (continuous_ellipsoidWeight a b) |2 * Real.pi * (∏ i, b i) / a|
    (norm_ellipsoidWeight_le a b ha)).comp tendsto_density_width
  rw [ellipsoidWeight_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (ellipsoid_continuumMean_eq_rescaled a b ha hb ρ hρ).symm

end BoundaryDraft
