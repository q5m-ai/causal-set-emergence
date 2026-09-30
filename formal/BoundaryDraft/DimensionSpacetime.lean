import BoundaryDraft.DimensionGeometry
import BoundaryDraft.DimensionMellin
import BoundaryDraft.DimensionReduction
import BoundaryDraft.DimensionActionConstants
import BoundaryDraft.DimensionSlice
import BoundaryDraft.DimensionNormalizedKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Actual dimension-indexed weighted bilocal graph-cap reduction

The observable is defined on pairs of spacetime points with canonical product
Lebesgue measure. Only the first endpoint is weighted. Complete causal futures,
compact absolute domination, spatial polar integration and vertical Fubini
connect it to a finite-height scalar reduction. No slice moment, mass, or limit
is built into the action definition. Point and pair coefficients are independent.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The actual pair kernel, with independent positive interval coefficient. -/
def dimensionBilocalKernel (n : ℕ) (c ρ : ℝ) (x y : DimensionSpacetime n) : ℝ :=
  dimensionKernel (n + 1) (c * ρ * dimensionIntervalSq x y ^ (((n + 1 : ℕ) : ℝ) / 2))

/-- A genuine first-endpoint-weighted bilocal observable. The partner set is
ALL of `M ∩ dimensionCausalFuture x`, not the support of the source weight. -/
def dimensionWeightedAction (n : ℕ) (a β c ρ : ℝ) (M : Set (DimensionSpacetime n))
    (w : DimensionSpacetime n → ℝ) : ℝ :=
  ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) *
    (a * (∫ x in M, w x) - β * ρ * ∫ x in M,
      w x * ∫ y in M ∩ dimensionCausalFuture x, dimensionBilocalKernel n c ρ x y)

theorem continuous_dimensionBilocalKernel (n : ℕ) (c ρ : ℝ) :
    Continuous (fun p : DimensionSpacetime n × DimensionSpacetime n =>
      dimensionBilocalKernel n c ρ p.1 p.2) := by
  unfold dimensionBilocalKernel
  exact (continuous_dimensionKernel (n + 1)).comp
    (continuous_const.mul (continuous_dimensionIntervalSq.rpow_const (fun _ => Or.inr (by positivity))))

/-- Compact domination of the actual causal pair integral precedes Fubini. -/
theorem integrableOn_dimensionWeighted_bilocal {n : ℕ} {M : Set (DimensionSpacetime n)}
    (hb : Bornology.IsBounded M) (c ρ : ℝ) (w : DimensionSpacetime n → ℝ)
    (hw : Continuous w) :
    IntegrableOn (fun p : DimensionSpacetime n × DimensionSpacetime n =>
      w p.1 * dimensionBilocalKernel n c ρ p.1 p.2)
      {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ dimensionCausalFuture p.1} := by
  have hc := (hw.comp continuous_fst).mul (continuous_dimensionBilocalKernel n c ρ)
  exact (hc.continuousOn.integrableOn_compact
    (hb.isCompact_closure.prod hb.isCompact_closure)).mono_set
      (fun _ hp => ⟨subset_closure hp.1, subset_closure hp.2.1⟩)

/-- Sphere area obtained from the actual Euclidean volume, not stipulated. -/
def dimensionRadialFactor (n : ℕ) : ℝ :=
  (n : ℝ) * (volume : Measure (DimensionSpatial n)).real (Metric.ball 0 1)

/-- Radial integration for the canonical Euclidean volume in every positive
spatial dimension, including the two radial directions when `n = 1`. -/
theorem integral_dimensionSpatial_radial (n : ℕ) (hn : 0 < n)
    (H : ℝ) (hH : 0 ≤ H) (f : ℝ → ℝ) :
    (∫ x : DimensionSpatial n in Metric.closedBall 0 H, f ‖x‖) =
      dimensionRadialFactor n * ∫ r in (0 : ℝ)..H, r ^ (n - 1) * f r := by
  letI : NeZero n := ⟨hn.ne'⟩
  rw [← integral_indicator measurableSet_closedBall]
  have he (x : DimensionSpatial n) :
      (Metric.closedBall 0 H).indicator (fun x => f ‖x‖) x =
        (Icc 0 H).indicator f ‖x‖ := by
    simp only [indicator, Metric.mem_closedBall, dist_zero_right, mem_Icc, norm_nonneg,
      true_and]
  simp_rw [he]
  rw [integral_fun_norm_addHaar]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  have hr : (∫ r : ℝ in Ioi 0, r ^ (n - 1) * (Icc 0 H).indicator f r) =
      ∫ r in (0 : ℝ)..H, r ^ (n - 1) * f r := by
    simp_rw [← indicator_mul_right (Icc 0 H) (fun r => r ^ (n - 1)) f]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hset : Icc 0 H ∩ Ioi (0 : ℝ) = Ioc 0 H := by
      ext r
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
    rw [hset, intervalIntegral.integral_of_le hH]
  rw [hr, dimensionRadialFactor]
  ring

/-- An actual spatial slice of the pair kernel at a fixed future time. -/
def dimensionSpatialSlice (n : ℕ) (c ρ t : ℝ) : ℝ :=
  ∫ x : DimensionSpatial n in Metric.closedBall 0 t,
    dimensionBilocalKernel n c ρ 0 (t, x)

/-- Its radial representative, extended by oriented integration at negative
heights. Only nonnegative heights are used in the physical reduction. -/
def dimensionRadialSlice (n : ℕ) (c ρ t : ℝ) : ℝ :=
  dimensionRadialFactor n * ∫ r in (0 : ℝ)..t, r ^ (n - 1) *
    dimensionKernel (n + 1) (c * ρ * (t ^ 2 - r ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))

theorem dimensionSpatialSlice_eq_radial (n : ℕ) (hn : 0 < n)
    (c ρ t : ℝ) (ht : 0 ≤ t) :
    dimensionSpatialSlice n c ρ t = dimensionRadialSlice n c ρ t := by
  simpa [dimensionSpatialSlice, dimensionBilocalKernel, dimensionIntervalSq,
    dimensionRadialSlice] using integral_dimensionSpatial_radial n hn t ht
      (fun r => dimensionKernel (n + 1)
        (c * ρ * (t ^ 2 - r ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2)))

theorem continuous_dimensionRadialSlice (n : ℕ) (c ρ : ℝ) :
    Continuous (dimensionRadialSlice n c ρ) := by
  unfold dimensionRadialSlice
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_id
  exact (continuous_snd.pow _).mul ((continuous_dimensionKernel (n + 1)).comp
    (continuous_const.mul (((continuous_fst.pow 2).sub (continuous_snd.pow 2)).rpow_const
      (fun _ => Or.inr (by positivity)))))

/-- The full truncated future cone, including null displacements and the vertex. -/
def dimensionTruncatedCone (n : ℕ) (H : ℝ) : Set (DimensionSpacetime n) :=
  {p | p ∈ dimensionCausalFuture 0 ∧ p.1 < H}

theorem measurableSet_dimensionTruncatedCone (n : ℕ) (H : ℝ) :
    MeasurableSet (dimensionTruncatedCone n H) :=
  (measurableSet_dimensionCausalFuture 0).inter
    (isOpen_lt continuous_fst continuous_const).measurableSet

/-- The cone integral is defined in spacetime, independently of its radial formula. -/
def dimensionConeIntegral (n : ℕ) (c ρ H : ℝ) : ℝ :=
  ∫ p in dimensionTruncatedCone n H, dimensionBilocalKernel n c ρ 0 p

theorem integrableOn_dimensionConeKernel (n : ℕ) (c ρ H : ℝ) :
    IntegrableOn (dimensionBilocalKernel n c ρ 0) (dimensionTruncatedCone n H) := by
  have hc : Continuous (dimensionBilocalKernel n c ρ 0) :=
    Continuous.uncurry_left (f := dimensionBilocalKernel n c ρ) 0
      (continuous_dimensionBilocalKernel n c ρ)
  apply (hc.continuousOn.integrableOn_compact
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) H)).prod
      (isCompact_closedBall (0 : DimensionSpatial n) H))).mono_set
  intro p hp
  have hs : ‖p.2‖ ≤ p.1 := by simpa [dimensionCausalFuture] using hp.1
  exact ⟨⟨(norm_nonneg _).trans hs, hp.2.le⟩,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hs.trans hp.2.le⟩

/-- Absolute product Fubini and polar integration compute the actual cone. -/
theorem dimensionConeIntegral_eq_radial (n : ℕ) (hn : 0 < n)
    (c ρ H : ℝ) (hH : 0 ≤ H) :
    dimensionConeIntegral n c ρ H = ∫ t in (0 : ℝ)..H, dimensionRadialSlice n c ρ t := by
  have hi := (integrable_indicator_iff (measurableSet_dimensionTruncatedCone n H)).mpr
    (integrableOn_dimensionConeKernel n c ρ H)
  rw [Measure.volume_eq_prod] at hi
  rw [dimensionConeIntegral, ← integral_indicator (measurableSet_dimensionTruncatedCone n H),
    Measure.volume_eq_prod, integral_prod _ hi]
  have he (t : ℝ) : (∫ x : DimensionSpatial n,
      (dimensionTruncatedCone n H).indicator (dimensionBilocalKernel n c ρ 0) (t, x)) =
      (Ico 0 H).indicator (dimensionRadialSlice n c ρ) t := by
    by_cases ht : t ∈ Ico 0 H
    · have he' (x : DimensionSpatial n) :
          (dimensionTruncatedCone n H).indicator (dimensionBilocalKernel n c ρ 0) (t, x) =
          (Metric.closedBall 0 t).indicator (fun x => dimensionBilocalKernel n c ρ 0 (t, x)) x := by
        simp [indicator, dimensionTruncatedCone, dimensionCausalFuture, ht.2,
          Metric.mem_closedBall, dist_zero_right]
      simp_rw [he']
      rw [indicator_of_mem ht, integral_indicator measurableSet_closedBall]
      exact dimensionSpatialSlice_eq_radial n hn c ρ t ht.1
    · rw [indicator_of_not_mem ht]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun x => by
        apply indicator_of_not_mem
        intro hp
        have hs : ‖x‖ ≤ t := by simpa [dimensionCausalFuture] using hp.1
        exact ht ⟨(norm_nonneg _).trans hs, hp.2⟩
  simp_rw [he]
  rw [integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hH]

/-- Every future-point integral is absolutely integrable on an actual cap. -/
theorem integrableOn_dimensionGraphCap_future {n : ℕ} (h : DimensionSpatial n → ℝ)
    (hh : DimensionGraphCapData h) (c ρ : ℝ) (x : DimensionSpacetime n) :
    IntegrableOn (dimensionBilocalKernel n c ρ x) (dimensionGraphCap h ∩ dimensionCausalFuture x) :=
  (hh.integrableOn_cap _ ((continuous_dimensionBilocalKernel n c ρ).comp
    (continuous_const.prodMk continuous_id))).mono_set inter_subset_left

/-- Translate the complete set of future partners; the source weight does not
restrict this set. No diagonal, null sector or cross-patch pair is discarded. -/
theorem dimensionGraphCap_future_integral {n : ℕ} (h : DimensionSpatial n → ℝ)
    (hh : DimensionGraphCapData h) (c ρ : ℝ) (x : DimensionSpacetime n)
    (hx : x ∈ dimensionGraphCap h) :
    (∫ y in dimensionGraphCap h ∩ dimensionCausalFuture x,
      dimensionBilocalKernel n c ρ x y) = dimensionConeIntegral n c ρ (-x.1) := by
  letI : (volume : Measure (DimensionSpacetime n)).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  rw [hh.complete_future x hx]
  have hm : MeasurableSet {y | y ∈ dimensionCausalFuture x ∧ y.1 < 0} :=
    (measurableSet_dimensionCausalFuture x).inter
      (isOpen_lt continuous_fst continuous_const).measurableSet
  rw [← integral_indicator hm, ← integral_add_left_eq_self _ x, dimensionConeIntegral,
    ← integral_indicator (measurableSet_dimensionTruncatedCone n (-x.1))]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    have ht : x.1 + p.1 < 0 ↔ p.1 < -x.1 := by constructor <;> intro ht <;> linarith
    simp [indicator, dimensionTruncatedCone, dimensionCausalFuture, dimensionBilocalKernel,
      dimensionIntervalSq, ht]

/-- Weighted vertical Fubini, with the same spatial source weight at every
height. Absolute integrability is derived from the compact cap. -/
theorem integral_dimensionGraphCap_weighted_depth {n : ℕ}
    (h : DimensionSpatial n → ℝ) (hh : DimensionGraphCapData h)
    (w : DimensionSpatial n → ℝ) (hw : Continuous w) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in dimensionGraphCap h, w p.2 * f (-p.1)) =
      ∫ x in {x | 0 < h x}, w x * ∫ t in (0 : ℝ)..h x, f t := by
  have hc : Continuous (fun p : DimensionSpacetime n => w p.2 * f (-p.1)) :=
    (hw.comp continuous_snd).mul (hf.comp continuous_fst.neg)
  have hi := (integrable_indicator_iff hh.measurableSet_cap).mpr (hh.integrableOn_cap _ hc)
  rw [Measure.volume_eq_prod] at hi
  rw [← integral_indicator hh.measurableSet_cap, Measure.volume_eq_prod,
    integral_prod_symm _ hi, ← integral_indicator hh.measurableSet_positive]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have he (t : ℝ) : (dimensionGraphCap h).indicator
        (fun p => w p.2 * f (-p.1)) (t, x) =
        (Ioo (-h x) 0).indicator (fun t => w x * f (-t)) t := by
      simp [indicator, dimensionGraphCap]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo, integral_const_mul]
    by_cases hx : 0 < h x
    · rw [indicator_of_mem (show x ∈ {x | 0 < h x} from hx),
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : -h x ≤ 0)]
      congr 1
      simpa only [neg_zero, neg_neg] using
        (intervalIntegral.integral_comp_neg (a := -h x) (b := 0) f)
    · rw [indicator_of_not_mem (show x ∉ {x | 0 < h x} from hx),
        Ioo_eq_empty_of_le (by linarith : (0 : ℝ) ≤ -h x), setIntegral_empty, mul_zero]

/-- Integrating the complete cone primitive gives the usual triangular weight.
This follows from finite-interval integration by parts, not from an assumed
interchange of divergent integrals. -/
theorem integral_dimensionConePrimitive (F : ℝ → ℝ) (hF : Continuous F) (H : ℝ) :
    (∫ s in (0 : ℝ)..H, ∫ t in (0 : ℝ)..s, F t) =
      ∫ t in (0 : ℝ)..H, (H - t) * F t := by
  let P : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, F t
  have hP : Continuous P := intervalIntegral.continuous_primitive hF.intervalIntegrable 0
  have hd (t : ℝ) : HasDerivAt P (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hP0 : P 0 = 0 := intervalIntegral.integral_same
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => H - t) (u' := fun _ => (-1 : ℝ))
    (v := P) (v' := F) (continuous_const.sub continuous_id).continuousOn hP.continuousOn
    (fun t _ => (hasDerivAt_id t).const_sub H) (fun t _ => hd t)
    (continuous_const.intervalIntegrable 0 H) (hF.intervalIntegrable 0 H)
  simp only [sub_self, zero_mul, hP0, mul_zero, zero_sub, neg_one_mul,
    intervalIntegral.integral_neg, neg_neg] at hi
  exact hi.symm

/-- The finite physical vertical kernel, with no moment normalization assumed. -/
def dimensionVerticalKernel (n : ℕ) (a β c ρ H : ℝ) : ℝ :=
  ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) *
    verticalActionReduction a (β * ρ) (dimensionRadialSlice n c ρ) H

theorem dimensionVerticalKernel_one (n : ℕ) (a β c : ℝ) :
    dimensionVerticalKernel n a β c 1 =
      verticalActionReduction a β (dimensionRadialSlice n c 1) := by
  ext H
  simp only [dimensionVerticalKernel, Real.one_rpow, one_mul, mul_one]

private theorem integral_dimensionActionDensity (n : ℕ) (a β c ρ H : ℝ) (hH : 0 ≤ H) :
    (∫ s in (0 : ℝ)..H, ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) *
      (a - β * ρ * ∫ t in (0 : ℝ)..s, dimensionRadialSlice n c ρ t)) =
      dimensionVerticalKernel n a β c ρ H := by
  have hF := continuous_dimensionRadialSlice n c ρ
  have hQ := intervalIntegral.continuous_primitive (μ := volume) hF.intervalIntegrable 0
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 H)
      ((continuous_const.mul hQ).intervalIntegrable 0 H),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_dimensionConePrimitive _ hF H, intervalIntegral.integral_of_le hH]
  simp only [dimensionVerticalKernel, verticalActionReduction, sub_zero, smul_eq_mul]
  ring

/-- Finite-density reduction of the ACTUAL first-endpoint-weighted bilocal
action in dimension `n+1`. All partners are retained. The point/pair constants
and interval coefficient are independent; no mass, slice moment, or limit
hypothesis is used. In particular this holds for every positive `c` and `ρ`. -/
theorem dimensionWeighted_graphCap_reduction (n : ℕ) (hn : 0 < n)
    (h : DimensionSpatial n → ℝ) (hh : DimensionGraphCapData h)
    (w : DimensionSpatial n → ℝ) (hw : Continuous w) (a β c ρ : ℝ) :
    dimensionWeightedAction n a β c ρ (dimensionGraphCap h) (fun p => w p.2) =
      ∫ x in {x | 0 < h x}, w x * dimensionVerticalKernel n a β c ρ (h x) := by
  let Q : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, dimensionRadialSlice n c ρ t
  have hQ : Continuous Q := intervalIntegral.continuous_primitive
    (continuous_dimensionRadialSlice n c ρ).intervalIntegrable 0
  have hi1 := hh.integrableOn_cap (fun p => w p.2) (hw.comp continuous_snd)
  have hiQ := hh.integrableOn_cap (fun p => w p.2 * Q (-p.1))
    ((hw.comp continuous_snd).mul (hQ.comp continuous_fst.neg))
  have hinner : (∫ x in dimensionGraphCap h, w x.2 *
      ∫ y in dimensionGraphCap h ∩ dimensionCausalFuture x,
        dimensionBilocalKernel n c ρ x y) =
      ∫ x in dimensionGraphCap h, w x.2 * Q (-x.1) := by
    apply setIntegral_congr_fun hh.measurableSet_cap
    intro x hx
    dsimp only
    rw [dimensionGraphCap_future_integral h hh c ρ x hx,
      dimensionConeIntegral_eq_radial n hn c ρ (-x.1) (neg_nonneg.mpr hx.2.le)]
  let L : ℝ → ℝ := fun s => ρ ^ (2 / ((n + 1 : ℕ) : ℝ)) * (a - β * ρ * Q s)
  have hL : Continuous L := continuous_const.mul
    (continuous_const.sub (continuous_const.mul hQ))
  calc
    _ = ∫ p in dimensionGraphCap h, w p.2 * L (-p.1) := by
      unfold dimensionWeightedAction
      dsimp only
      rw [hinner, ← integral_const_mul, ← integral_const_mul,
        ← integral_sub (hi1.const_mul a) (hiQ.const_mul (β * ρ)), ← integral_const_mul]
      apply setIntegral_congr_fun hh.measurableSet_cap
      intro p _
      dsimp [L]
      ring
    _ = ∫ x in {x | 0 < h x}, w x * ∫ t in (0 : ℝ)..h x, L t :=
      integral_dimensionGraphCap_weighted_depth h hh w hw L hL
    _ = _ := by
      apply setIntegral_congr_fun hh.measurableSet_positive
      intro x hx
      dsimp only [L, Q]
      rw [integral_dimensionActionDensity n a β c ρ (h x) hx.le]

/-- Radial scaling keeps the real half-dimensional power, including odd
spacetime dimensions. This is a substitution in the actual radial integral. -/
theorem dimensionRadialSlice_scale (n : ℕ) (hn : 0 < n) (c k t : ℝ)
    (hk : 0 < k) (ht : 0 ≤ t) :
    dimensionRadialSlice n c 1 (k * t) = k ^ n * dimensionRadialSlice n c (k ^ (n + 1)) t := by
  have hp : (k ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2) = k ^ (n + 1) := by
    rw [← Real.rpow_natCast k 2, ← Real.rpow_mul hk.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (((n + 1 : ℕ) : ℝ) / 2) = ((n + 1 : ℕ) : ℝ) by ring,
      Real.rpow_natCast]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := t)
    (fun r => r ^ (n - 1) * dimensionKernel (n + 1)
      (c * ((k * t) ^ 2 - r ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))) k
  simp only [smul_eq_mul, mul_zero] at hs
  have he : (∫ r in (0 : ℝ)..t, (k * r) ^ (n - 1) * dimensionKernel (n + 1)
      (c * ((k * t) ^ 2 - (k * r) ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))) =
      k ^ (n - 1) * ∫ r in (0 : ℝ)..t, r ^ (n - 1) * dimensionKernel (n + 1)
        (c * k ^ (n + 1) * (t ^ 2 - r ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht] at hr
    have hσ : 0 ≤ t ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
    dsimp only
    rw [show (k * t) ^ 2 - (k * r) ^ 2 = k ^ 2 * (t ^ 2 - r ^ 2) by ring,
      Real.mul_rpow (sq_nonneg k) hσ, hp, mul_pow]
    simp only [mul_assoc]
  unfold dimensionRadialSlice
  simp only [mul_one]
  rw [← hs, he]
  have hn' : k * k ^ (n - 1) = k ^ n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  calc
    _ = (k * k ^ (n - 1)) * (dimensionRadialFactor n *
        ∫ r in (0 : ℝ)..t, r ^ (n - 1) * dimensionKernel (n + 1)
          (c * k ^ (n + 1) * (t ^ 2 - r ^ 2) ^ (((n + 1 : ℕ) : ℝ) / 2))) := by ring
    _ = _ := by rw [hn']

private theorem dimensionConvolution_scale (n : ℕ) (hn : 0 < n) (c k H : ℝ)
    (hk : 0 < k) (hH : 0 ≤ H) :
    (∫ t in (0 : ℝ)..k * H, (k * H - t) * dimensionRadialSlice n c 1 t) =
      k ^ (n + 2) * ∫ t in (0 : ℝ)..H,
        (H - t) * dimensionRadialSlice n c (k ^ (n + 1)) t := by
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := H) (fun t => (k * H - t) * dimensionRadialSlice n c 1 t) k
  simp only [smul_eq_mul, mul_zero] at hs
  rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hH] at ht
  dsimp only
  rw [dimensionRadialSlice_scale n hn c k t hk ht.1,
    show n + 2 = n + 1 + 1 by omega, pow_succ, pow_succ]
  ring

/-- Positive-density scaling is derived from the finite physical reduction,
not postulated as a property of a scalar kernel. -/
theorem dimensionVerticalKernel_scale (n : ℕ) (hn : 0 < n) (a β c k H : ℝ)
    (hk : 0 < k) (hH : 0 ≤ H) :
    dimensionVerticalKernel n a β c (k ^ (n + 1)) H =
      k * dimensionVerticalKernel n a β c 1 (k * H) := by
  have hd : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (k ^ (n + 1)) ^ (2 / ((n + 1 : ℕ) : ℝ)) = k ^ 2 := by
    rw [← Real.rpow_natCast k (n + 1), ← Real.rpow_mul hk.le]
    rw [mul_div_cancel₀ 2 hd, Real.rpow_two]
  unfold dimensionVerticalKernel verticalActionReduction
  rw [hp, Real.one_rpow, one_mul, mul_one,
    ← intervalIntegral.integral_of_le hH,
    ← intervalIntegral.integral_of_le (mul_nonneg hk.le hH),
    dimensionConvolution_scale n hn c k H hk hH]
  rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
  ring

/-- The isotropic density scale is `ρ^(1/d)`, unlike the transverse scale
`ρ^(2/d)` of the long-null cancellation theorem. -/
theorem dimensionVerticalKernel_density_scaling (n : ℕ) (hn : 0 < n)
    (a β c ρ H : ℝ) (hρ : 0 < ρ) (hH : 0 ≤ H) :
    dimensionVerticalKernel n a β c ρ H =
      ρ ^ (1 / ((n + 1 : ℕ) : ℝ)) * dimensionVerticalKernel n a β c 1
        (ρ ^ (1 / ((n + 1 : ℕ) : ℝ)) * H) := by
  have hd : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (ρ ^ (1 / ((n + 1 : ℕ) : ℝ))) ^ (n + 1) = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le, one_div_mul_cancel hd, Real.rpow_one]
  simpa only [hp] using dimensionVerticalKernel_scale n hn a β c
    (ρ ^ (1 / ((n + 1 : ℕ) : ℝ))) H (Real.rpow_pos_of_pos hρ _) hH

theorem continuous_dimensionVerticalKernel (n : ℕ) (a β c ρ : ℝ) :
    Continuous (dimensionVerticalKernel n a β c ρ) := by
  have he (H : ℝ) : (∫ t in Ioc 0 H, (H - t) * dimensionRadialSlice n c ρ t) =
      ∫ t in (0 : ℝ)..max 0 H, (H - t) * dimensionRadialSlice n c ρ t := by
    rw [intervalIntegral.integral_of_le (le_max_left _ _)]
    by_cases hH : 0 ≤ H
    · rw [max_eq_right hH]
    · rw [max_eq_left (le_of_not_ge hH), Ioc_self, setIntegral_empty,
        Ioc_eq_empty_of_le (le_of_not_ge hH), setIntegral_empty]
  unfold dimensionVerticalKernel verticalActionReduction
  simp_rw [he]
  apply continuous_const.mul
  apply (continuous_const.mul continuous_id).sub
  apply continuous_const.mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    ((continuous_fst.sub continuous_snd).mul
      ((continuous_dimensionRadialSlice n c ρ).comp continuous_snd))
    (continuous_const.max continuous_id)

private def dimensionEuclideanEquiv (n : ℕ) : DimensionSpatial n ≃ᵐ (Fin n → ℝ) :=
  { WithLp.equiv 2 _ with
    measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin n => ℝ)).measurable
    measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin n => ℝ)).measurable }

/-- Orthonormal normal/tangential coordinates; the tangent dimension may be zero. -/
def dimensionSpatialCons {m : ℕ} (r : ℝ) (z : Fin m → ℝ) : DimensionSpatial (m + 1) :=
  (WithLp.equiv 2 _).symm (Fin.cons r z)

private theorem continuous_dimensionSpatialCons (m : ℕ) :
    Continuous (fun p : ℝ × (Fin m → ℝ) => dimensionSpatialCons p.1 p.2) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin (m + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  exact Fin.cases continuous_fst (fun j => (continuous_apply j).comp continuous_snd) i

/-- Fubini in independently specified orthonormal spatial coordinates. -/
theorem integral_dimensionSpatial_first (m : ℕ) (f : DimensionSpatial (m + 1) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ r : ℝ, ∫ z : Fin m → ℝ, f (dimensionSpatialCons r z) := by
  let E := dimensionEuclideanEquiv (m + 1)
  have hE : MeasurePreserving E.symm := PiLp.volume_preserving_equiv_symm _
  have hi := (hE.integrable_comp_emb E.symm.measurableEmbedding).mpr hf
  rw [← hE.integral_comp' f]
  let T : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have hT : MeasurePreserving T :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _
  have hi' := (hT.integrable_comp_emb T.measurableEmbedding).mpr hi
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi'
  rw [← hT.integral_comp' (fun z => f (E.symm z)), Measure.volume_eq_prod, integral_prod _ hi']
  simp [T, E, dimensionEuclideanEquiv, dimensionSpatialCons,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

/-- An explicit bounded tent regulator. Its artificial faces are not discarded
from the partner region. -/
def dimensionWedgeRegulator (m : ℕ) (κ H : ℝ) (x : DimensionSpatial (m + 1)) : ℝ :=
  min (κ * x 0) (H - κ * ‖x‖)

theorem dimensionWedgeRegulator_data (m : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (H : ℝ) :
    DimensionGraphCapData (dimensionWedgeRegulator m κ H) := by
  constructor
  · apply isBounded_iff_forall_norm_le.2
    refine ⟨H / κ, fun x hx => ?_⟩
    have hh : 0 < H - κ * ‖x‖ := (lt_min_iff.mp hx).2
    apply (le_div_iff₀ hκ).2
    nlinarith
  · refine ⟨κ, hκ.le, hκ1, fun x y => ?_⟩
    have hcoord : |x 0 - y 0| ≤ ‖y - x‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs, norm_sub_rev] using
        PiLp.norm_apply_le (x - y) (0 : Fin (m + 1))
    have hfirst : |κ * x 0 - κ * y 0| ≤ κ * ‖y - x‖ := by
      rw [← mul_sub, abs_mul, abs_of_pos hκ]
      exact mul_le_mul_of_nonneg_left hcoord hκ.le
    have hsecond : |(H - κ * ‖x‖) - (H - κ * ‖y‖)| ≤ κ * ‖y - x‖ := by
      rw [show (H - κ * ‖x‖) - (H - κ * ‖y‖) = -(κ * (‖x‖ - ‖y‖)) by ring,
        abs_neg, abs_mul, abs_of_pos hκ]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le x y) hκ.le
    have hp := (abs_min_sub_min_le_max (κ * x 0) (H - κ * ‖x‖)
      (κ * y 0) (H - κ * ‖y‖)).trans (max_le hfirst hsecond)
    have hm : |max 0 (dimensionWedgeRegulator m κ H x) -
        max 0 (dimensionWedgeRegulator m κ H y)| ≤
        |dimensionWedgeRegulator m κ H x - dimensionWedgeRegulator m κ H y| := by
      simpa only [max_comm] using abs_max_sub_max_le_abs
        (dimensionWedgeRegulator m κ H x) (dimensionWedgeRegulator m κ H y) 0
    exact hm.trans hp

theorem dimensionWedgeRegulator_eq_affine (m : ℕ) {κ H R : ℝ} (hκ : 0 ≤ κ)
    (hH : 2 * κ * R ≤ H) {x : DimensionSpatial (m + 1)} (hx : ‖x‖ ≤ R) :
    dimensionWedgeRegulator m κ H x = κ * x 0 := by
  apply min_eq_left
  have hcoord : x 0 ≤ R := (le_abs_self _).trans ((PiLp.norm_apply_le x 0).trans hx)
  have h1 := mul_le_mul_of_nonneg_left hcoord hκ
  have h2 := mul_le_mul_of_nonneg_left hx hκ
  linarith

/-- Tangential source integration, without a preassigned angle coefficient. -/
def dimensionTangentialProfile (m : ℕ) (w : DimensionSpatial (m + 1) → ℝ) (r : ℝ) : ℝ :=
  ∫ z : Fin m → ℝ, w (dimensionSpatialCons r z)

private theorem dimension_norm_tail_le (m : ℕ) (r : ℝ) (z : Fin m → ℝ) :
    ‖z‖ ≤ ‖dimensionSpatialCons r z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  simpa [dimensionSpatialCons] using
    PiLp.norm_apply_le (dimensionSpatialCons r z) i.succ

theorem dimensionTangentialProfile_eq_compact (m : ℕ) (w : DimensionSpatial (m + 1) → ℝ)
    (R : ℝ) (hsource : ∀ x, R < ‖x‖ → w x = 0) (r : ℝ) :
    dimensionTangentialProfile m w r =
      ∫ z in Metric.closedBall (0 : Fin m → ℝ) R, w (dimensionSpatialCons r z) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hsource _ ((by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz :
    R < ‖z‖).trans_le (dimension_norm_tail_le m r z))

theorem continuous_dimensionTangentialProfile (m : ℕ) (w : DimensionSpatial (m + 1) → ℝ)
    (hw : Continuous w) (R : ℝ) (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    Continuous (dimensionTangentialProfile m w) := by
  simp_rw [show dimensionTangentialProfile m w = fun r =>
      ∫ z in Metric.closedBall (0 : Fin m → ℝ) R, w (dimensionSpatialCons r z) from
    funext (dimensionTangentialProfile_eq_compact m w R hsource)]
  apply continuous_parametric_integral_of_continuous _ (isCompact_closedBall 0 R)
  exact hw.comp (continuous_dimensionSpatialCons m)

theorem hasCompactSupport_dimensionTangentialProfile (m : ℕ)
    (w : DimensionSpatial (m + 1) → ℝ) (R : ℝ) (hsource : ∀ x, R < ‖x‖ → w x = 0) :
    HasCompactSupport (dimensionTangentialProfile m w) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R)
  intro r hr
  have hr' : R < ‖r‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hr
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun z => hsource _ (hr'.trans_le (by
    simpa [dimensionSpatialCons] using PiLp.norm_apply_le (dimensionSpatialCons r z) 0))

/-- Actual regulated action to a scalar normal profile. The regulator and source
support are geometric hypotheses; the second endpoint remains unrestricted
inside the entire cap throughout the proof. -/
theorem dimensionWeighted_wedgeRegulator_eq_profile (m : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (m + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ : ℝ) :
    dimensionWeightedAction (m + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator m κ H)) (fun p => w p.2) =
      ∫ r : ℝ in Ioi 0, dimensionTangentialProfile m w r *
        dimensionVerticalKernel (m + 1) a β c ρ (κ * r) := by
  have hs : HasCompactSupport w := HasCompactSupport.intro (isCompact_closedBall 0 R)
    (fun x hx => hsource x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
  have hcoord : Continuous (fun x : DimensionSpatial (m + 1) => x 0) :=
    (continuous_apply 0).comp (PiLp.continuous_equiv 2 _)
  have hc : Continuous (fun x : DimensionSpatial (m + 1) =>
      w x * dimensionVerticalKernel (m + 1) a β c ρ (κ * x 0)) :=
    hw.mul ((continuous_dimensionVerticalKernel (m + 1) a β c ρ).comp
      (continuous_const.mul hcoord))
  have hi := hc.integrable_of_hasCompactSupport (μ := volume) hs.mul_right
  have hm : MeasurableSet {x : DimensionSpatial (m + 1) | 0 < x 0} :=
    (isOpen_lt continuous_const hcoord).measurableSet
  rw [dimensionWeighted_graphCap_reduction (m + 1) (by omega) _
    (dimensionWedgeRegulator_data m hκ hκ1 H) w hw a β c ρ,
    ← integral_indicator (dimensionWedgeRegulator_data m hκ hκ1 H).measurableSet_positive]
  have he : {x | 0 < dimensionWedgeRegulator m κ H x}.indicator
      (fun x => w x * dimensionVerticalKernel (m + 1) a β c ρ (dimensionWedgeRegulator m κ H x)) =
      {x : DimensionSpatial (m + 1) | 0 < x 0}.indicator
        (fun x => w x * dimensionVerticalKernel (m + 1) a β c ρ (κ * x 0)) := by
    ext x
    by_cases hx : ‖x‖ ≤ R
    · simp only [indicator, mem_setOf_eq, dimensionWedgeRegulator_eq_affine m hκ.le hH hx,
        mul_pos_iff_of_pos_left hκ]
    · simp [indicator, hsource x (lt_of_not_ge hx)]
  rw [he, integral_dimensionSpatial_first m _ (hi.indicator hm)]
  have hf (r : ℝ) : (∫ z : Fin m → ℝ,
      {x : DimensionSpatial (m + 1) | 0 < x 0}.indicator
        (fun x => w x * dimensionVerticalKernel (m + 1) a β c ρ (κ * x 0))
          (dimensionSpatialCons r z)) =
      (Ioi (0 : ℝ)).indicator (fun r => dimensionTangentialProfile m w r *
        dimensionVerticalKernel (m + 1) a β c ρ (κ * r)) r := by
    by_cases hr : 0 < r
    · simp [indicator, hr, dimensionSpatialCons, dimensionTangentialProfile, integral_mul_const]
    · simp [indicator, hr, dimensionSpatialCons]
  simp_rw [hf]
  rw [integral_indicator measurableSet_Ioi]

/-- The radial factor has precisely the independently specified sphere area. -/
theorem dimensionRadialFactor_eq_sphere (n : ℕ) (hn : 0 < n) :
    dimensionRadialFactor n = dimensionSphereArea (n + 1) := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hg : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hvol : (volume : Measure (DimensionSpatial n)).real (Metric.ball 0 1) =
      Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
    simp only [Measure.real, EuclideanSpace.volume_ball, Fintype.card_fin,
      ENNReal.ofReal_one, one_pow, one_mul]
    exact ENNReal.toReal_ofReal (div_nonneg (by positivity) hg.le)
  have hp : Real.sqrt Real.pi ^ n = Real.pi ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [dimensionRadialFactor, hvol, hp, Real.Gamma_add_one (by positivity : (n : ℝ) / 2 ≠ 0)]
  simp only [dimensionSphereArea, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  field_simp
  ring

/-- Squared-radius substitution for any continuous kernel profile. The
singular exponent `-1/2` at spatial dimension one is integrable. The zero-radius
endpoint is removed only as a Lebesgue-null point, not by assuming continuity
of that singular integrand there. -/
theorem integral_dimensionRadial_sigma (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ r in (0 : ℝ)..t, r ^ (n - 1) * f (t ^ 2 - r ^ 2)) =
      (1 / 2 : ℝ) * ∫ σ in Ioc 0 (t ^ 2),
        (t ^ 2 - σ) ^ (((n : ℝ) - 2) / 2) * f σ := by
  let α : ℝ := ((n : ℝ) - 2) / 2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα : -1 < α := by dsimp [α]; linarith
  let g : ℝ → ℝ := fun u => u ^ α * f (t ^ 2 - u)
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ α) volume 0 (t ^ 2) :=
    intervalIntegral.intervalIntegrable_rpow' hα
  have hgi : IntegrableOn g (Icc 0 (t ^ 2)) := by
    rw [← uIcc_of_le (sq_nonneg t), ← intervalIntegrable_iff']
    exact hpow.mul_continuousOn (hf.comp (continuous_const.sub continuous_id)).continuousOn
  have hrpow (r : ℝ) (hr : 0 < r) : r * (r ^ 2) ^ α = r ^ (n - 1) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    calc
      _ = r ^ (1 : ℝ) * r ^ ((2 : ℝ) * α) := by rw [Real.rpow_one]; rfl
      _ = r ^ (1 + 2 * α) := (Real.rpow_add hr _ _).symm
      _ = _ := by
        rw [show 1 + 2 * α = ((n - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub hn, Nat.cast_one]; dsimp [α]; ring, Real.rpow_natCast]
  have he (r : ℝ) (hr : 0 < r) : g (r ^ 2) * (2 * r) =
      2 * (r ^ (n - 1) * f (t ^ 2 - r ^ 2)) := by
    dsimp [g]
    calc
      _ = 2 * (r * (r ^ 2) ^ α) * f (t ^ 2 - r ^ 2) := by ring
      _ = _ := by rw [hrpow r hr]; ring
  have hgcont : ContinuousOn g ((fun r : ℝ => r ^ 2) '' Ioo (min 0 t) (max 0 t)) := by
    rintro u ⟨r, hr, rfl⟩
    rw [min_eq_left ht, max_eq_right ht] at hr
    exact ((continuousAt_id.rpow_const (Or.inl (ne_of_gt (sq_pos_of_pos hr.1)))).mul
      (hf.continuousAt.comp (continuousAt_const.sub continuousAt_id))).continuousWithinAt
  have hgimage : IntegrableOn g ((fun r : ℝ => r ^ 2) '' uIcc 0 t) := by
    apply hgi.mono_set
    rintro u ⟨r, hr, rfl⟩
    rw [uIcc_of_le ht] at hr
    exact ⟨sq_nonneg r, pow_le_pow_left₀ hr.1 hr.2 2⟩
  have hgcomp : IntegrableOn (fun r : ℝ => g (r ^ 2) * (2 * r)) (uIcc 0 t) := by
    rw [uIcc_of_le ht, integrableOn_Icc_iff_integrableOn_Ioc]
    have hc : Continuous (fun r : ℝ => 2 * (r ^ (n - 1) * f (t ^ 2 - r ^ 2))) :=
      continuous_const.mul ((continuous_id.pow _).mul
        (hf.comp (continuous_const.sub (continuous_id.pow 2))))
    apply hc.integrableOn_Ioc.congr_fun _ measurableSet_Ioc
    intro r hr
    exact (he r hr.1).symm
  have hs := intervalIntegral.integral_comp_mul_deriv'''
    (a := 0) (b := t) (f := fun r : ℝ => r ^ 2) (f' := fun r => 2 * r) (g := g)
    (continuous_id.pow 2).continuousOn
    (fun r _ => by
      convert ((hasDerivAt_id r).pow 2).hasDerivWithinAt using 1
      norm_num [id_eq])
    hgcont hgimage hgcomp
  have hleft : (∫ r in (0 : ℝ)..t, (g ∘ fun r => r ^ 2) r * (2 * r)) =
      2 * ∫ r in (0 : ℝ)..t, r ^ (n - 1) * f (t ^ 2 - r ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun r hr => by
      rw [uIoc_of_le ht] at hr
      exact he r hr.1
  rw [hleft] at hs
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  have hreflect := intervalIntegral.integral_comp_sub_left g (t ^ 2) (a := 0) (b := t ^ 2)
  simp only [sub_self, sub_zero] at hreflect
  have hright : (∫ u in (0 : ℝ)..t ^ 2, g u) =
      ∫ σ in Ioc 0 (t ^ 2), (t ^ 2 - σ) ^ α * f σ := by
    rw [← hreflect, intervalIntegral.integral_of_le (sq_nonneg t)]
    simp only [g, sub_sub_cancel]
  rw [hright] at hs
  change _ = (1 / 2 : ℝ) * ∫ σ in Ioc 0 (t ^ 2), (t ^ 2 - σ) ^ α * f σ
  linarith

/-- The exact physical radial-to-squared-proper-time bridge, including the
singular endpoint in dimension two and the derived sphere-area normalization. -/
theorem dimensionRadialSlice_eq_sigmaIntegral (n : ℕ) (hn : 0 < n)
    (c ρ t : ℝ) (ht : 0 ≤ t) :
    dimensionRadialSlice n c ρ t = (dimensionSphereArea (n + 1) / 2) *
      ∫ σ in Ioc 0 (t ^ 2),
        (t ^ 2 - σ) ^ (((((n + 1 : ℕ) : ℝ)) - 3) / 2) *
          dimensionKernel (n + 1) (c * ρ * σ ^ (((n + 1 : ℕ) : ℝ) / 2)) := by
  have hf : Continuous (fun σ : ℝ => dimensionKernel (n + 1)
      (c * ρ * σ ^ (((n + 1 : ℕ) : ℝ) / 2))) :=
    (continuous_dimensionKernel (n + 1)).comp
      (continuous_const.mul (Real.continuous_rpow_const (by positivity)))
  rw [dimensionRadialSlice, integral_dimensionRadial_sigma n hn t ht _ hf,
    dimensionRadialFactor_eq_sphere n hn]
  have he : (((n + 1 : ℕ) : ℝ) - 3) / 2 = ((n : ℝ) - 2) / 2 := by push_cast; ring
  rw [he]
  ring

/-- Named slice bridge consumed by the separately proved slice-moment and
mass theorems. Valid at zero as well as positive height, and in dimension two. -/
theorem dimensionRadialSlice_eq_sigma (n : ℕ) (hn : 0 < n)
    (c ρ t : ℝ) (ht : 0 ≤ t) :
    dimensionRadialSlice n c ρ t = (dimensionSphereArea (n + 1) / 2) *
      dimensionSigmaSlice (n + 1) (c * ρ) t := by
  simpa only [dimensionSigmaSlice] using dimensionRadialSlice_eq_sigmaIntegral n hn c ρ t ht

/-- The same identification starts directly from the Euclidean spatial slice. -/
theorem dimensionSpatialSlice_eq_sigma (n : ℕ) (hn : 0 < n)
    (c ρ t : ℝ) (ht : 0 ≤ t) :
    dimensionSpatialSlice n c ρ t = (dimensionSphereArea (n + 1) / 2) *
      dimensionSigmaSlice (n + 1) (c * ρ) t := by
  rw [dimensionSpatialSlice_eq_radial n hn c ρ t ht, dimensionRadialSlice_eq_sigma n hn c ρ t ht]

/-- The scalar regulated observable is derived from the actual bounded action,
with its physical density scale and all future partners. -/
theorem dimensionWeighted_wedgeRegulator_eq_regulated (m : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (m + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c ρ : ℝ) (hρ : 0 < ρ) :
    dimensionWeightedAction (m + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator m κ H)) (fun p => w p.2) =
      regulatedVerticalReduction (dimensionVerticalKernel (m + 1) a β c 1)
        (dimensionTangentialProfile m w) κ (ρ ^ (1 / (((m + 1) + 1 : ℕ) : ℝ))) := by
  rw [dimensionWeighted_wedgeRegulator_eq_profile m hκ hκ1 hH w hw hsource a β c ρ]
  unfold regulatedVerticalReduction
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [dimensionVerticalKernel_density_scaling (m + 1) (by omega) a β c ρ (κ * r)
    hρ (mul_nonneg hκ.le hr.le)]

/-- Conditional regulated local coefficient for the actual spacetime action.
Only the independent unit-density kernel's absolute integrability and mass
remain to be supplied by the slice-moment work. No action-limit or reduction
conclusion is a hypothesis. The tangential integral is in orthonormal coordinates,
including the zero-dimensional tangent space at spacetime dimension two. -/
theorem dimensionWeighted_wedgeRegulator_limit_of_mass (m : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (m + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c : ℝ)
    (hG : IntegrableOn (dimensionVerticalKernel (m + 1) a β c 1) (Ioi 0))
    (hmass : (∫ u : ℝ in Ioi 0, dimensionVerticalKernel (m + 1) a β c 1 u) = 1) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (m + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator m κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : Fin m → ℝ, w (dimensionSpatialCons 0 z))) := by
  let B := dimensionTangentialProfile m w
  let G := dimensionVerticalKernel (m + 1) a β c 1
  have hB : Continuous B := continuous_dimensionTangentialProfile m w hw R hsource
  obtain ⟨C, hC⟩ :=
    (hasCompactSupport_dimensionTangentialProfile m w R hsource).exists_bound_of_continuous hB
  have hl := signed_rescaling_limit (volume.restrict (Ioi 0)) G (fun x => B (x / κ))
    hG (hB.comp (continuous_id.div_const κ)) C (fun x => hC _)
  have hm : (∫ u : ℝ in Ioi 0, G u) = 1 := hmass
  simp only [hm, one_mul, zero_div] at hl
  have hk := tendsto_rpow_atTop (div_pos (by norm_num : (0 : ℝ) < 1)
    (Nat.cast_pos.mpr (by omega : 0 < (m + 1) + 1)))
  have hlim := ((hl.comp tendsto_inv_atTop_zero).const_mul κ⁻¹).comp hk
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (by
    rw [dimensionWeighted_wedgeRegulator_eq_regulated m hκ hκ1 hH w hw hsource a β c ρ hρ,
      regulatedVerticalReduction_rescale G B hκ (Real.rpow_pos_of_pos hρ _)] :
    dimensionWeightedAction (m + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator m κ H)) (fun p => w p.2) =
      κ⁻¹ * ∫ u : ℝ in Ioi 0, G u * B ((ρ ^ (1 / (((m + 1) + 1 : ℕ) : ℝ)))⁻¹ * u / κ)).symm

/-- A version whose remaining premises are precisely independently evaluated
moments of the concrete spatial slice. The mass conclusion is derived using
`DimensionReduction`, then applied to the actual weighted bilocal observable. -/
theorem dimensionWeighted_wedgeRegulator_limit_of_slice_moments (m : ℕ) {κ H R : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hH : 2 * κ * R ≤ H)
    (w : DimensionSpatial (m + 1) → ℝ) (hw : Continuous w)
    (hsource : ∀ x, R < ‖x‖ → w x = 0) (a β c : ℝ)
    (hi₀ : IntegrableOn (dimensionRadialSlice (m + 1) c 1) (Ioi 0))
    (hi₁ : IntegrableOn (fun t : ℝ => t * dimensionRadialSlice (m + 1) c 1 t) (Ioi 0))
    (hi₂ : IntegrableOn (fun t : ℝ => t ^ 2 * dimensionRadialSlice (m + 1) c 1 t) (Ioi 0))
    (h₀ : β * ∫ t : ℝ in Ioi 0, dimensionRadialSlice (m + 1) c 1 t = a)
    (h₁ : (∫ t : ℝ in Ioi 0, t * dimensionRadialSlice (m + 1) c 1 t) = 0)
    (h₂ : -β * ∫ t : ℝ in Ioi 0, t ^ 2 * dimensionRadialSlice (m + 1) c 1 t = 2) :
    Tendsto (fun ρ : ℝ => dimensionWeightedAction (m + 1) a β c ρ
      (dimensionGraphCap (dimensionWedgeRegulator m κ H)) (fun p => w p.2))
      atTop (𝓝 (κ⁻¹ * ∫ z : Fin m → ℝ, w (dimensionSpatialCons 0 z))) := by
  have hmass := integral_verticalActionReduction a β (dimensionRadialSlice (m + 1) c 1)
    (continuous_dimensionRadialSlice (m + 1) c 1).measurable hi₀ hi₁ hi₂ h₀ h₁ h₂
  apply dimensionWeighted_wedgeRegulator_limit_of_mass m hκ hκ1 hH w hw hsource a β c
  · rw [dimensionVerticalKernel_one]
    exact hmass.1
  · rw [dimensionVerticalKernel_one]
    exact hmass.2

/-- Exact identification with the independently defined, Mellin-integrated
physical slice; no moment hypothesis is used in this spatial change of variables. -/
theorem dimensionRadialSlice_eq_physical (n : ℕ) (hn : 0 < n)
    (c ρ t : ℝ) (ht : 0 ≤ t) :
    dimensionRadialSlice n c ρ t = dimensionPhysicalSlice (n + 1) (c * ρ) t := by
  rw [dimensionRadialSlice_eq_sigma n hn c ρ t ht]
  unfold dimensionSphereArea dimensionPhysicalSlice
  ring

theorem dimensionRadialSlice_one_eq_coneSlice (n : ℕ) (hn : 0 < n)
    (t : ℝ) (ht : 0 ≤ t) :
    dimensionRadialSlice n (dimensionIntervalCoefficient (n + 1)) 1 t =
      dimensionConeSlice (n + 1) t := by
  simpa only [dimensionConeSlice, mul_one] using dimensionRadialSlice_eq_physical n hn
    (dimensionIntervalCoefficient (n + 1)) 1 t ht

/-- The density-one vertical kernel obtained from the bilocal reduction is the
independently normalized plane kernel. The equality holds even at negative
heights because both finite-height integrals then have empty domains. -/
theorem dimensionVerticalKernel_one_eq_planeKernel (n : ℕ) (hn : 0 < n) :
    dimensionVerticalKernel n (dimensionPointCoefficient (n + 1))
      (dimensionPairCoefficient (n + 1)) (dimensionIntervalCoefficient (n + 1)) 1 =
        dimensionPlaneKernel (n + 1) := by
  rw [dimensionVerticalKernel_one]
  ext H
  unfold dimensionPlaneKernel verticalActionReduction
  have he : (∫ t in Ioc 0 H, (H - t) *
      dimensionRadialSlice n (dimensionIntervalCoefficient (n + 1)) 1 t) =
      ∫ t in Ioc 0 H, (H - t) * dimensionConeSlice (n + 1) t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [dimensionRadialSlice_one_eq_coneSlice n hn t ht.1.le]
  rw [he]

/-- The actual published coefficients and interval volume give the normalized
finite-density graph-cap reduction, with no extra analytic premise. This is the
bridge enabling the separately proved unit mass to act on a physical observable. -/
theorem dimensionWeighted_graphCap_normalized_reduction (n : ℕ) (hn : 0 < n)
    (h : DimensionSpatial n → ℝ) (hh : DimensionGraphCapData h)
    (w : DimensionSpatial n → ℝ) (hw : Continuous w) (ρ : ℝ) (hρ : 0 < ρ) :
    dimensionWeightedAction n (dimensionPointCoefficient (n + 1))
      (dimensionPairCoefficient (n + 1)) (dimensionIntervalCoefficient (n + 1)) ρ
        (dimensionGraphCap h) (fun p => w p.2) =
      ∫ x in {x | 0 < h x}, w x * (ρ ^ (1 / ((n + 1 : ℕ) : ℝ)) *
        dimensionPlaneKernel (n + 1) (ρ ^ (1 / ((n + 1 : ℕ) : ℝ)) * h x)) := by
  rw [dimensionWeighted_graphCap_reduction n hn h hh w hw]
  apply setIntegral_congr_fun hh.measurableSet_positive
  intro x hx
  dsimp only
  rw [dimensionVerticalKernel_density_scaling n hn _ _ _ ρ (h x) hρ hx.le,
    dimensionVerticalKernel_one_eq_planeKernel n hn]

end BoundaryDraft
