import BoundaryDraft.TwoFaceGeometry
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Controlled conformal geometry in the original four-dimensional coordinates

The metric has signature (+---) wherever Omega is positive. Its volume density
is Omega^4. Only a neighborhood of the fixed region's closure is geometrically
controlled; a globally measurable extension defines the ambient measure.
No expectation, curvature coefficient or asymptotic statement is a field.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace BoundaryDraft

/-- The actual conformally rescaled Minkowski bilinear form at a point. -/
def conformalMetric (Ω : Spacetime → ℝ) (p v w : Spacetime) : ℝ :=
  Ω p ^ 2 * minkowskiInner v w

/-- An invertible tangent scaling when Omega is positive identifies the form
with Minkowski's form, preserving its signature and nondegeneracy. -/
theorem conformalMetric_eq_scaled (Ω : Spacetime → ℝ) (p v w : Spacetime) :
    conformalMetric Ω p v w = minkowskiInner (Ω p • v) (Ω p • w) := by
  rw [minkowskiInner_smul_left, minkowskiInner_smul_right]
  unfold conformalMetric
  ring

/-- Positive conformal scaling preserves the causal tangent cones. -/
theorem conformalMetric_nonneg_iff {Ω : Spacetime → ℝ} {p : Spacetime}
    (hp : 0 < Ω p) (v : Spacetime) :
    0 ≤ conformalMetric Ω p v v ↔ 0 ≤ minkowskiInner v v := by
  exact mul_nonneg_iff_of_pos_left (sq_pos_of_pos hp)

/-- The fixed time orientation and closed coordinate causal relation agree
with the rescaled quadratic cone. No null points are removed. -/
theorem conformalMetric_causal_iff {Ω : Spacetime → ℝ} {p : Spacetime}
    (hp : 0 < Ω p) (x y : Spacetime) :
    (x 0 ≤ y 0 ∧ 0 ≤ conformalMetric Ω p (y - x) (y - x)) ↔ y ∈ causalFuture x := by
  rw [conformalMetric_nonneg_iff hp, ← intervalSq_eq_minkowski_sub]
  change (x 0 ≤ y 0 ∧ 0 ≤ (y 0 - x 0) ^ 2 - spatialSeparationSq x y) ↔ _
  simp only [sub_nonneg, causalFuture, mem_setOf_eq]

/-- Coordinate metric matrix; the volume density is derived from its determinant. -/
def conformalMetricMatrix (Ω : Spacetime → ℝ) (p : Spacetime) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then Ω p ^ 2 else -(Ω p ^ 2))

theorem conformalMetric_eq_matrix (Ω : Spacetime → ℝ) (p v w : Spacetime) :
    conformalMetric Ω p v w = v ⬝ᵥ (Matrix.mulVec (conformalMetricMatrix Ω p) w) := by
  simp [conformalMetric, conformalMetricMatrix, Matrix.mulVec_diagonal,
    dotProduct, minkowskiInner, Fin.sum_univ_succ]
  ring

theorem conformalMetricMatrix_det (Ω : Spacetime → ℝ) (p : Spacetime) :
    (conformalMetricMatrix Ω p).det = -(Ω p ^ 8) := by
  simp [conformalMetricMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem conformalMetric_volumeDensity (Ω : Spacetime → ℝ) (p : Spacetime) :
    Real.sqrt |(conformalMetricMatrix Ω p).det| = Ω p ^ 4 := by
  rw [conformalMetricMatrix_det, abs_neg, abs_of_nonneg (by positivity)]
  convert Real.sqrt_sq (show 0 ≤ Ω p ^ 4 by positivity) using 1
  ring

/-- Four-dimensional metric volume, not a flat proper-time interval formula. -/
def conformalVolume (Ω : Spacetime → ℝ) : Measure Spacetime :=
  volume.withDensity (fun p => ENNReal.ofReal (Ω p ^ 4))

/-- The isolated volume measure is independent of the ambient extension. -/
theorem conformalVolume_restrict_congr {M : Set Spacetime} (hm : MeasurableSet M)
    {Ω Ψ : Spacetime → ℝ} (he : EqOn Ω Ψ M) :
    (conformalVolume Ω).restrict M = (conformalVolume Ψ).restrict M := by
  rw [conformalVolume, conformalVolume, restrict_withDensity hm, restrict_withDensity hm]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hm] with p hp
  rw [he hp]

/-- Geometric assumptions on a fixed neighborhood, plus a measurable ambient
extension. No smoothness or positive lower bound is required outside it. -/
structure ControlledConformalFactor (Ω : Spacetime → ℝ) (M : Set Spacetime) : Prop where
  measurable : Measurable Ω
  control : ∃ U : Set Spacetime, IsOpen U ∧ closure M ⊆ U ∧ ContDiffOn ℝ ⊤ Ω U ∧
    ∃ m L : ℝ, 0 < m ∧ ∀ p ∈ U, m ≤ Ω p ∧ Ω p ≤ L

theorem conformalVolume_absolutelyContinuous (Ω : Spacetime → ℝ) :
    conformalVolume Ω ≪ volume := withDensity_absolutelyContinuous _ _

instance conformalVolume_noAtoms (Ω : Spacetime → ℝ) : NoAtoms (conformalVolume Ω) := by
  constructor
  intro x
  exact conformalVolume_absolutelyContinuous Ω (measure_singleton x)

/-- The supplied smooth neighborhood really contains every point to be sprinkled. -/
theorem ControlledConformalFactor.pos {Ω : Spacetime → ℝ} {M : Set Spacetime}
    (hΩ : ControlledConformalFactor Ω M) {p : Spacetime} (hp : p ∈ closure M) : 0 < Ω p := by
  obtain ⟨U, _, hU, _, m, L, hm, hb⟩ := hΩ.control
  exact hm.trans_le (hb p (hU hp)).1

theorem ControlledConformalFactor.smoothAt {Ω : Spacetime → ℝ} {M : Set Spacetime}
    (hΩ : ControlledConformalFactor Ω M) {p : Spacetime} (hp : p ∈ closure M) :
    ContDiffAt ℝ ⊤ Ω p := by
  obtain ⟨U, ho, hU, hs, _⟩ := hΩ.control
  exact hs.contDiffAt (ho.mem_nhds (hU hp))

/-- Explicit domination of volume on the region; finite mass is a conclusion. -/
theorem ControlledConformalFactor.volume_bound {Ω : Spacetime → ℝ} {M : Set Spacetime}
    (hΩ : ControlledConformalFactor Ω M) (hM : MeasurableSet M) :
    ∃ L : ℝ, conformalVolume Ω M ≤ ENNReal.ofReal (L ^ 4) * volume M := by
  obtain ⟨U, _, hU, _, m, L, hm, hb⟩ := hΩ.control
  refine ⟨L, ?_⟩
  rw [conformalVolume, withDensity_apply _ hM, ← setLIntegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hM] with p hp
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (hm.le.trans (hb p (hU (subset_closure hp))).1)
    (hb p (hU (subset_closure hp))).2 4

theorem ControlledConformalFactor.finite_volume {Ω : Spacetime → ℝ} {M : Set Spacetime}
    (hΩ : ControlledConformalFactor Ω M) (hm : MeasurableSet M) (hb : Bornology.IsBounded M) :
    conformalVolume Ω M < ∞ := by
  obtain ⟨L, hL⟩ := hΩ.volume_bound hm
  exact hL.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.measure_lt_top)

theorem ControlledConformalFactor.isFiniteMeasure_restrict {Ω : Spacetime → ℝ}
    {M : Set Spacetime} (hΩ : ControlledConformalFactor Ω M)
    (hm : MeasurableSet M) (hb : Bornology.IsBounded M) :
    IsFiniteMeasure ((conformalVolume Ω).restrict M) :=
  ⟨by simpa using hΩ.finite_volume hm hb⟩

/-- Endpoint removal preserves curved volume, including null-related pairs. -/
theorem conformalVolume_exclusive (Ω : Spacetime → ℝ) (x y : Spacetime) :
    conformalVolume Ω (causalIntervalInterior x y) = conformalVolume Ω (causalInterval x y) :=
  measure_diff_null (((Set.finite_singleton y).insert x).measure_zero (conformalVolume Ω))

/-- Ambient/restricted compatibility is derived, only for endpoints in a
causally convex region. The isolated definition does not need this hypothesis. -/
theorem conformalVolume_restrict_interval {M : Set Spacetime} (hM : CausallyConvex M)
    (Ω : Spacetime → ℝ) {x y : Spacetime} (hx : x ∈ M) (hy : y ∈ M) :
    (conformalVolume Ω).restrict M (causalIntervalInterior x y) =
      conformalVolume Ω (causalInterval x y) := by
  rw [Measure.restrict_apply (measurableSet_causalIntervalInterior x y),
    inter_eq_left.mpr (fun _ hz => hM x hx y hy hz.1), conformalVolume_exclusive]

@[simp] theorem conformalVolume_const (c : ℝ) :
    conformalVolume (fun _ => c) = ENNReal.ofReal (c ^ 4) • volume :=
  withDensity_const _

@[simp] theorem conformalVolume_one : conformalVolume (fun _ => 1) = volume := by
  simp

theorem controlledConformalFactor_const (M : Set Spacetime) {c : ℝ} (hc : 0 < c) :
    ControlledConformalFactor (fun _ => c) M := by
  refine ⟨measurable_const, univ, isOpen_univ, subset_univ _, contDiffOn_const, c, c, hc, ?_⟩
  exact fun _ _ => ⟨le_rfl, le_rfl⟩

end BoundaryDraft
