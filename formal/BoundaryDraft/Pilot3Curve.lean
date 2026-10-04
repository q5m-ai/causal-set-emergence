import BoundaryDraft.Pilot3Surface
import BoundaryDraft.HausdorffGraph

/-!
# One-dimensional graph geometry in the pilot's spatial plane

The normalization is diameter-Hausdorff ONE-measure, whose line factor is
one. The existing dimension-free linear-approximation estimate is reused;
no two-area normalization or four-dimensional analytic coefficient is ported.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace BoundaryDraft

/-- Split spatial coordinates as a continuous linear equivalence, without
identifying the Euclidean norm with the product supremum norm. -/
def pilot3Coordinates : Pilot3Space ≃L[ℝ] ℝ × ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (x 0, x 1)
      invFun := fun p => (WithLp.equiv 2 _).symm ![p.1, p.2]
      left_inv := by intro x; ext i; fin_cases i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }

def pilot3Curve (g : ℝ → ℝ) (u : ℝ) : Pilot3Space := pilot3Coordinates.symm (g u, u)

def pilot3CurveLinear (L : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] Pilot3Space :=
  pilot3Coordinates.symm.toContinuousLinearMap.comp (L.prod (ContinuousLinearMap.id ℝ ℝ))

@[simp] theorem pilot3Curve_zero (g : ℝ → ℝ) (u : ℝ) : pilot3Curve g u 0 = g u := rfl
@[simp] theorem pilot3Curve_one (g : ℝ → ℝ) (u : ℝ) : pilot3Curve g u 1 = u := rfl

@[simp] theorem pilot3Curve_height_base (x : Pilot3Space) : pilot3Curve (fun _ => x 0) (x 1) = x :=
  pilot3Coordinates.symm_apply_apply x

theorem pilot3Coordinates_norm_sq (a b : ℝ) : ‖pilot3Coordinates.symm (a, b)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  change ‖((WithLp.equiv 2 _).symm ![a, b] : Pilot3Space)‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem continuous_pilot3Curve {g : ℝ → ℝ} (hg : Continuous g) : Continuous (pilot3Curve g) :=
  pilot3Coordinates.symm.continuous.comp (hg.prodMk continuous_id)

theorem continuous_measurableEmbedding_pilot3Curve {g : ℝ → ℝ} (hg : Continuous g) :
    MeasurableEmbedding (pilot3Curve g) := by
  apply (continuous_pilot3Curve hg).measurableEmbedding
  intro x y he
  exact congrArg (fun p : Pilot3Space => p 1) he

theorem pilot3CurveLinear_norm_sq (L : ℝ →L[ℝ] ℝ) (v : ℝ) :
    ‖pilot3CurveLinear L v‖ ^ 2 = (L v) ^ 2 + v ^ 2 := pilot3Coordinates_norm_sq _ _

theorem pilot3CurveLinear_noncontracting (L : ℝ →L[ℝ] ℝ) (v : ℝ) :
    ‖v‖ ≤ ‖pilot3CurveLinear L v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pilot3CurveLinear_norm_sq, Real.norm_eq_abs, sq_abs]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem pilot3CurveLinear_injective (L : ℝ →L[ℝ] ℝ) : Function.Injective (pilot3CurveLinear L) := by
  intro x y he
  exact congrArg (fun p : Pilot3Space => p 1) he

theorem hasStrictFDerivAt_pilot3Curve (g : ℝ → ℝ) (L : ℝ →L[ℝ] ℝ) (u : ℝ)
    (hg : HasStrictFDerivAt g L u) : HasStrictFDerivAt (pilot3Curve g) (pilot3CurveLinear L) u :=
  pilot3Coordinates.symm.hasStrictFDerivAt.comp u (hg.prodMk (hasStrictFDerivAt_id u))

/-- The actual speed of the scalar graph, not a supplied density. -/
def pilot3CurveJacobian (g : ℝ → ℝ) (u : ℝ) : ℝ := ‖pilot3CurveLinear (fderiv ℝ g u) 1‖

theorem pilot3CurveJacobian_pos (g : ℝ → ℝ) (u : ℝ) : 0 < pilot3CurveJacobian g u := by
  have hb := pilot3CurveLinear_noncontracting (fderiv ℝ g u) 1
  norm_num at hb
  exact zero_lt_one.trans_le hb

/-- Exact tangent-image measure, including arbitrary nonmeasurable subsets. -/
theorem pilot3_linear_image_measure (A : ℝ →L[ℝ] Pilot3Space) (s : Set ℝ) :
    (μH[1] : Measure Pilot3Space) (A '' s) = ENNReal.ofReal ‖A 1‖ * volume s := by
  have he : (A : ℝ → Pilot3Space) = fun t => t • A 1 := by
    funext t
    simpa only [smul_eq_mul, mul_one] using A.map_smul t (1 : ℝ)
  rw [he, pilot3_line_normalization]
  simp only [ENNReal.smul_def, smul_eq_mul, one_smul, ofReal_norm_eq_enorm, enorm_eq_nnnorm]

/-- One-dimensional Hausdorff distortion between two parameterizations. -/
theorem pilot3_hausdorff_image_le_of_dist_le {X Y Z : Type*} [Nonempty X]
    [MetricSpace Y] [MetricSpace Z] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Z] [BorelSpace Z]
    (f : X → Y) (g : X → Z) (s : Set X) (hg : InjOn g s) (K : ℝ≥0)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y)) :
    (μH[1] : Measure Y) (f '' s) ≤ (K : ℝ≥0∞) * (μH[1] : Measure Z) (g '' s) := by
  let T : Z → Y := fun z => f (Function.invFunOn g s z)
  have hT : LipschitzOnWith K T (g '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [T, hg.leftInvOn_invFunOn hx, hg.leftInvOn_invFunOn hy] using hfg x hx y hy
  have he : T '' (g '' s) = f '' s := by
    rw [← image_comp]
    apply image_congr
    intro x hx
    exact congrArg f (hg.leftInvOn_invFunOn hx)
  simpa only [he, ENNReal.rpow_one] using hT.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)

theorem pilot3_approximatesLinearOn_hausdorff_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (A : E →L[ℝ] F) (s : Set E) (ε : ℝ≥0) (hε : ε < 1)
    (hA : ∀ v, ‖v‖ ≤ ‖A v‖) (hf : ApproximatesLinearOn f A s ε) :
    ((1 - ε : ℝ≥0) : ℝ≥0∞) * (μH[1] : Measure F) (A '' s) ≤ μH[1] (f '' s) ∧
      μH[1] (f '' s) ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) * μH[1] (A '' s) := by
  have hpos : 0 < 1 - (ε : ℝ) := sub_pos.mpr hε
  have hAi : Function.Injective A := by
    intro x y he
    apply sub_eq_zero.mp
    apply norm_le_zero_iff.mp
    simpa only [map_sub, he, sub_self, norm_zero] using hA (x - y)
  have hfi : InjOn f s := by
    intro x hx y hy he
    have hn := (approximatesLinearOn_relative_bounds f A s ε hA hf x hx y hy).1
    rw [he, sub_self, norm_zero] at hn
    have hz : A x - A y = 0 := norm_le_zero_iff.mp
      ((mul_le_mul_left hpos).mp (by simpa only [mul_zero] using hn))
    exact hAi (sub_eq_zero.mp hz)
  have hupper := pilot3_hausdorff_image_le_of_dist_le f A s hAi.injOn (1 + ε) (by
    intro x hx y hy
    simpa only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one] using
      (approximatesLinearOn_relative_bounds f A s ε hA hf x hx y hy).2)
  have hlower := pilot3_hausdorff_image_le_of_dist_le A f s hfi (1 - ε)⁻¹ (by
    intro x hx y hy
    simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hε.le, NNReal.coe_one]
    apply (le_inv_mul_iff₀ hpos).mpr
    exact (approximatesLinearOn_relative_bounds f A s ε hA hf x hx y hy).1)
  refine ⟨?_, hupper⟩
  have hne : (1 - ε : ℝ≥0) ≠ 0 := ne_of_gt (tsub_pos_of_lt hε)
  have hm := mul_le_mul_left' hlower (((1 - ε : ℝ≥0) : ℝ≥0∞))
  simpa only [ENNReal.coe_inv hne, ← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hne) ENNReal.coe_ne_top, one_mul] using hm

/-- The canonical pullback of spatial one-measure along the graph. -/
def pilot3CurvePullback (g : ℝ → ℝ) : Measure ℝ := Measure.comap (pilot3Curve g) (μH[1] : Measure Pilot3Space)

theorem pilot3CurvePullback_apply {g : ℝ → ℝ} (hg : Continuous g) (s : Set ℝ) :
    pilot3CurvePullback g s = (μH[1] : Measure Pilot3Space) (pilot3Curve g '' s) :=
  (continuous_measurableEmbedding_pilot3Curve hg).comap_apply _ s

/-- Actual measure bounds on every subset of a small parameter interval. -/
theorem pilot3Curve_local_measure_bounds (g : ℝ → ℝ) (hg : Continuous g)
    (U : Set ℝ) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U) (a : ℝ) (ha : a ∈ U)
    (ε : ℝ≥0) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧ ∀ s ⊆ ball a r,
      ENNReal.ofReal ((1 - (ε : ℝ)) * pilot3CurveJacobian g a) * volume s ≤ pilot3CurvePullback g s ∧
      pilot3CurvePullback g s ≤ ENNReal.ofReal ((1 + (ε : ℝ)) * pilot3CurveJacobian g a) * volume s := by
  have hd := hasStrictFDerivAt_pilot3Curve g _ a
    ((hgU.contDiffAt (hU.mem_nhds ha)).hasStrictFDerivAt le_rfl)
  obtain ⟨V, hV, happrox⟩ := hd.approximates_deriv_on_nhds (Or.inr hε0)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds ha))
  refine ⟨r, hr, fun x hx => (hball hx).2, ?_⟩
  intro s hs
  have hb := pilot3_approximatesLinearOn_hausdorff_bounds _ _ s ε hε1
    (pilot3CurveLinear_noncontracting _) (happrox.mono_set (hs.trans (hball.trans inter_subset_left)))
  rw [pilot3_linear_image_measure] at hb
  rw [pilot3CurvePullback_apply hg]
  have hm : ENNReal.ofReal (1 - (ε : ℝ)) = ((1 - ε : ℝ≥0) : ℝ≥0∞) := by
    simpa only [NNReal.coe_sub hε1.le, NNReal.coe_one] using
      (show ENNReal.ofReal ((1 - ε : ℝ≥0) : ℝ) = ((1 - ε : ℝ≥0) : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  have hp : ENNReal.ofReal (1 + (ε : ℝ)) = ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
    simpa only [NNReal.coe_add, NNReal.coe_one] using
      (show ENNReal.ofReal ((1 + ε : ℝ≥0) : ℝ) = ((1 + ε : ℝ≥0) : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  simpa only [ENNReal.ofReal_mul (sub_nonneg.mpr (show (ε : ℝ) ≤ 1 from hε1.le)),
    ENNReal.ofReal_mul (show 0 ≤ 1 + (ε : ℝ) by positivity), hm, hp, mul_assoc, pilot3CurveJacobian] using hb

end BoundaryDraft
