import BoundaryDraft.GraphAngle
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Tangent-to-graph Hausdorff distortion

This implements the local bi-Lipschitz comparison in the graph-area proof
roadmap. The estimates compare actual Hausdorff measures of graph and tangent
images, for every subset of a sufficiently small ball. They do not assume an
area formula or a planar normalization. Both domain and ambient graph space
use Euclidean metrics, not the default coordinate/product supremum norms.
-/

open MeasureTheory Set Filter
open scoped Topology MeasureTheory ENNReal NNReal
noncomputable section
namespace BoundaryDraft

/-- Transfer a distance comparison between two parametrizations to their
Hausdorff image measures. No measurability of the parameter subset is needed. -/
theorem hausdorff_image_le_of_dist_le {X Y Z : Type*} [Nonempty X]
    [MetricSpace Y] [MetricSpace Z] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Z] [BorelSpace Z]
    (f : X → Y) (g : X → Z) (s : Set X) (hg : InjOn g s) (K : ℝ≥0)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y)) :
    (μH[2] : Measure Y) (f '' s) ≤ (K : ℝ≥0∞) ^ 2 * (μH[2] : Measure Z) (g '' s) := by
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
  have hb := hT.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [he, ENNReal.rpow_two] using hb

/-- Uniform linear approximation gives sharp relative norm bounds when the
linear map does not contract vectors, as is the case for a graph derivative. -/
theorem approximatesLinearOn_relative_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (A : E →L[ℝ] F) (s : Set E) (ε : ℝ≥0)
    (hA : ∀ v, ‖v‖ ≤ ‖A v‖) (hf : ApproximatesLinearOn f A s ε)
    (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
    (1 - (ε : ℝ)) * ‖A x - A y‖ ≤ ‖f x - f y‖ ∧
      ‖f x - f y‖ ≤ (1 + (ε : ℝ)) * ‖A x - A y‖ := by
  have he : ‖f x - f y - (A x - A y)‖ ≤ (ε : ℝ) * ‖A x - A y‖ := by
    simpa only [map_sub] using (hf x hx y hy).trans
      (mul_le_mul_of_nonneg_left (hA (x - y)) ε.coe_nonneg)
  have h1 := norm_le_insert (f x - f y) (A x - A y)
  have h2 := norm_le_insert (A x - A y) (f x - f y)
  rw [norm_sub_rev (A x - A y) (f x - f y)] at h2
  constructor <;> linarith

/-- Actual two-sided Hausdorff distortion, with the powers and inverse
cancellation justified also when the measures are infinite. -/
theorem approximatesLinearOn_hausdorff_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (A : E →L[ℝ] F) (s : Set E) (ε : ℝ≥0) (hε : ε < 1)
    (hA : ∀ v, ‖v‖ ≤ ‖A v‖) (hf : ApproximatesLinearOn f A s ε) :
    ((1 - ε : ℝ≥0) : ℝ≥0∞) ^ 2 * (μH[2] : Measure F) (A '' s) ≤ μH[2] (f '' s) ∧
      μH[2] (f '' s) ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2 * μH[2] (A '' s) := by
  have hε' : (ε : ℝ) < 1 := hε
  have hpos : 0 < 1 - (ε : ℝ) := sub_pos.mpr hε'
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
  have hupper := hausdorff_image_le_of_dist_le f A s hAi.injOn (1 + ε) (by
    intro x hx y hy
    simpa only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one] using
      (approximatesLinearOn_relative_bounds f A s ε hA hf x hx y hy).2)
  have hlower := hausdorff_image_le_of_dist_le A f s hfi (1 - ε)⁻¹ (by
    intro x hx y hy
    simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hε.le, NNReal.coe_one]
    apply (le_inv_mul_iff₀ hpos).mpr
    exact (approximatesLinearOn_relative_bounds f A s ε hA hf x hx y hy).1)
  refine ⟨?_, hupper⟩
  have hne : (1 - ε : ℝ≥0) ≠ 0 := ne_of_gt (tsub_pos_of_lt hε)
  have hmul := mul_le_mul_left' hlower (((1 - ε : ℝ≥0) : ℝ≥0∞) ^ 2)
  simpa only [ENNReal.coe_inv hne, ← ENNReal.inv_pow, ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hne))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top), one_mul] using hmul

abbrev SurfacePlane := EuclideanSpace ℝ (Fin 2)

/-- A scalar graph in Euclidean three-space, with the height coordinate first.
This is an isometric coordinate permutation of the usual `(x,g x)` convention. -/
def surfaceGraph (g : SurfacePlane → ℝ) (x : SurfacePlane) : JointSpace :=
  (WithLp.equiv 2 _).symm (Fin.cons (g x) x)

/-- The actual graph derivative, with Euclidean norms on both spaces. -/
def surfaceGraphDerivative (L : SurfacePlane →L[ℝ] ℝ) : SurfacePlane →L[ℝ] JointSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (L.finCons (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap)

theorem surfaceGraphDerivative_norm_sq (L : SurfacePlane →L[ℝ] ℝ) (v : SurfacePlane) :
    ‖surfaceGraphDerivative L v‖ ^ 2 = (L v) ^ 2 + ‖v‖ ^ 2 := by
  simp only [surfaceGraphDerivative, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  change (∑ i : Fin 3, ((Fin.cons (L v) (v : Fin 2 → ℝ) : Fin 3 → ℝ) i) ^ 2) = _
  rw [Fin.sum_univ_succ]
  rfl

theorem surfaceGraphDerivative_noncontracting (L : SurfacePlane →L[ℝ] ℝ) (v : SurfacePlane) :
    ‖v‖ ≤ ‖surfaceGraphDerivative L v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [surfaceGraphDerivative_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem hasStrictFDerivAt_surfaceGraph (g : SurfacePlane → ℝ) (L : SurfacePlane →L[ℝ] ℝ)
    (x : SurfacePlane) (hg : HasStrictFDerivAt g L x) :
    HasStrictFDerivAt (surfaceGraph g) (surfaceGraphDerivative L) x :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasStrictFDerivAt).comp x
    (hg.finCons (F' := fun _ : Fin 3 => ℝ)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).hasStrictFDerivAt)

/-- The local tangent-plane comparison, derived from local C¹ data.
It holds for every subset of the small ball, without a Borel-set premise or an
assumed planar area normalization. -/
theorem surfaceGraph_local_hausdorff_bounds (g : SurfacePlane → ℝ) (U : Set SurfacePlane)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (a : SurfacePlane) (ha : a ∈ U)
    (ε : ℝ≥0) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ U ∧ ∀ s ⊆ Metric.ball a r,
      ((1 - ε : ℝ≥0) : ℝ≥0∞) ^ 2 *
        μH[2] (surfaceGraphDerivative (fderiv ℝ g a) '' s) ≤ μH[2] (surfaceGraph g '' s) ∧
      μH[2] (surfaceGraph g '' s) ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ 2 *
        μH[2] (surfaceGraphDerivative (fderiv ℝ g a) '' s) := by
  have hd := hasStrictFDerivAt_surfaceGraph g _ a
    ((hg.contDiffAt (hU.mem_nhds ha)).hasStrictFDerivAt le_rfl)
  obtain ⟨V, hV, happrox⟩ := hd.approximates_deriv_on_nhds (Or.inr hε0)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds ha))
  refine ⟨r, hr, fun x hx => (hball hx).2, ?_⟩
  intro s hs
  exact approximatesLinearOn_hausdorff_bounds _ _ s ε hε1
    (surfaceGraphDerivative_noncontracting _) (happrox.mono_set (hs.trans (hball.trans inter_subset_left)))

end BoundaryDraft
