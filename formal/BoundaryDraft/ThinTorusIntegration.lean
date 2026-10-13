import BoundaryDraft.ThinTorusVolume
import BoundaryDraft.DimensionFourCompatibility
import BoundaryDraft.GraphTail

/-!
# Full-partner quotient integration for the thin torus
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace BoundaryDraft
namespace CompactTorus

variable (L : ℝ) [Fact (0 < L)]

local instance : BorelSpace (Space L) := inferInstance
local instance : SecondCountableTopology (Space L) := inferInstance

theorem distance_cover_on_cube (a v : DimensionSpatial 3) (hv : v ∈ coverCube L a) :
    (spatialDistance L).distance (cover L a) (cover L v) = ‖v - a‖ := by
  have hc (i : Fin 3) : dist ((a i : ℝ) : AddCircle L) ((v i : ℝ) : AddCircle L) = |v i - a i| := by
    rw [dist_comm, dist_eq_norm, ← QuotientAddGroup.mk_sub]
    apply (AddCircle.norm_coe_eq_abs_iff L (ne_of_gt (Fact.out : 0 < L))).mpr
    rw [abs_of_pos (Fact.out : 0 < L)]
    exact abs_le.mpr ⟨by linarith [(hv i).1], by linarith [(hv i).2]⟩
  rw [distance_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [cover, project, hc, PiLp.sub_apply, Real.norm_eq_abs]

/-- All quotient partners in a causal ball, not only targets in a source chart.
The fundamental cube merely transports the geometric measure. -/
theorem integral_spatial_causal (p : Space L) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : 2 * τ < L)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ q in {q | (spatialDistance L).distance p q ≤ τ},
      f ((spatialDistance L).distance p q) ∂spatialVolume L) =
      4 * Real.pi * ∫ r in (0 : ℝ)..τ, r ^ 2 * f r := by
  let a := centeredLift L p
  have ha : cover L a = p := cover_centeredLift L p
  let S := {q | (spatialDistance L).distance p q ≤ τ}
  have hd : Continuous (fun q => (spatialDistance L).distance p q) :=
    Continuous.comp (f := fun q : Space L => (p, q))
      (g := fun z : Space L × Space L => (spatialDistance L).distance z.1 z.2)
      (spatialDistance L).continuous (continuous_const.prodMk continuous_id)
  have hm : MeasurableSet S := (isClosed_le hd continuous_const).measurableSet
  have hg : StronglyMeasurable (S.indicator (fun q => f ((spatialDistance L).distance p q))) :=
    (hf.comp hd).stronglyMeasurable.indicator hm
  rw [← integral_indicator hm, ← (cover_measurePreserving L a).map_eq,
    integral_map (cover_measurePreserving L a).measurable.aemeasurable hg.aestronglyMeasurable]
  have he : (∫ v in coverCube L a,
      S.indicator (fun q => f ((spatialDistance L).distance p q)) (cover L v)) =
      ∫ v in Metric.closedBall a τ, f ‖v - a‖ := by
    rw [← integral_indicator measurableSet_closedBall, ← integral_indicator (measurableSet_coverCube L a)]
    apply integral_congr_ae
    exact Eventually.of_forall fun v => by
      by_cases hv : v ∈ coverCube L a
      · rw [indicator_of_mem hv]
        have hdv : (spatialDistance L).distance p (cover L v) = ‖v - a‖ := by
          rw [← ha]
          exact distance_cover_on_cube L a v hv
        simp only [S, indicator, mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, hdv]
      · rw [indicator_of_not_mem hv, indicator_of_not_mem (fun h =>
          hv (closedBall_subset_coverCube L a hτ h))]
  rw [he, ← integral_indicator measurableSet_closedBall,
    ← integral_add_left_eq_self (fun v : DimensionSpatial 3 =>
      (Metric.closedBall a τ).indicator (fun v => f ‖v - a‖) v) a]
  have he' (v : DimensionSpatial 3) :
      (Metric.closedBall a τ).indicator (fun v => f ‖v - a‖) (a + v) =
      (Metric.closedBall 0 τ).indicator (fun v => f ‖v‖) v := by
    simp only [indicator, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero]
  simp_rw [he']
  rw [integral_indicator measurableSet_closedBall,
    integral_dimensionSpatial_radial 3 (by decide) τ hτ0, dimensionRadialFactor_three]

/-- Continuous unrestricted representative of the actual thin-slab kernel. The
causal mask and both slab measures are imposed separately. -/
def thinKernel (ρ : ℝ) (x y : ℝ × Space L) : ℝ :=
  bdgKernel ((Real.pi / 24) * ρ *
    ((y.1 - x.1) ^ 2 - (spatialDistance L).distance x.2 y.2 ^ 2) ^ 2)

omit [Fact (0 < L)] in
theorem continuous_thinKernel (ρ : ℝ) (x : ℝ × Space L) : Continuous (thinKernel L ρ x) := by
  have hd : Continuous (fun y : ℝ × Space L => (spatialDistance L).distance x.2 y.2) :=
    Continuous.comp (f := fun y : ℝ × Space L => (x.2, y.2))
      (g := fun z : Space L × Space L => (spatialDistance L).distance z.1 z.2)
      (spatialDistance L).continuous (continuous_const.prodMk continuous_snd)
  unfold thinKernel bdgKernel bdgPolynomial
  fun_prop

/-- Compact domination before any signed time/spatial Fubini interchange. -/
theorem integrable_thinKernel (ρ T : ℝ) (x : ℝ × Space L) :
    Integrable (thinKernel L ρ x) (slabVolume L T) := by
  exact ((continuous_thinKernel L ρ x).continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set (Space L))))).mono_set
      (show slab L T ⊆ Icc (-T / 2) (T / 2) ×ˢ univ from
        fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, h.2⟩)

theorem thinKernel_eq_actual {T : ℝ} (hT : 2 * T < L) (ρ : ℝ)
    {x y : ℝ × Space L} (hx : x ∈ slab L T) (hy : y ∈ slab L T)
    (hxy : (measuredOrder L).Rel x y) :
    bdgKernel (ρ * (slabVolume L T ((measuredOrder L).interval x y)).toReal) = thinKernel L ρ x y := by
  rw [intervalVolume_thin L hT hx hy hxy, ENNReal.toReal_ofReal (by positivity)]
  unfold thinKernel
  congr 1
  ring

/-- The complete inner quotient integral, including targets across seams, is
exactly the full future cone to the upper time face. -/
theorem inner_integral {T : ℝ} (hT : 2 * T < L) (ρ : ℝ)
    {x : ℝ × Space L} (hx : x ∈ slab L T) :
    (∫ y in {y | (measuredOrder L).Rel x y},
      bdgKernel (ρ * (slabVolume L T ((measuredOrder L).interval x y)).toReal)
        ∂slabVolume L T) = coneRadialIntegral ρ (T / 2 - x.1) := by
  let C := {y | (measuredOrder L).Rel x y}
  have hC : MeasurableSet C := (measuredOrder L).measurable_rel.preimage
    (f := fun y : ℝ × Space L => (x, y)) (measurable_const.prodMk measurable_id)
  have hreplace : (∫ y in C,
      bdgKernel (ρ * (slabVolume L T ((measuredOrder L).interval x y)).toReal) ∂slabVolume L T) =
      ∫ y in C, thinKernel L ρ x y ∂slabVolume L T := by
    apply setIntegral_congr_ae hC
    filter_upwards [ae_restrict_mem (Ultrastatic.measurable_slab T)] with y hy hxy
    exact thinKernel_eq_actual L hT ρ hx hy hxy
  rw [hreplace, ← integral_indicator hC]
  have hi := (integrable_thinKernel L ρ T x).indicator hC
  have hvol : slabVolume L T =
      (volume.restrict (Ioo (-T / 2) (T / 2))).prod (spatialVolume L) := by
    rw [slabVolume, Ultrastatic.slabVolume, Ultrastatic.slab, ← Measure.prod_restrict,
      Measure.restrict_univ]
  rw [hvol, integral_prod _ (by rwa [hvol] at hi)]
  have hf (s : ℝ) (hs : s ∈ Ioo (-T / 2) (T / 2)) :
      (∫ q : Space L, C.indicator (thinKernel L ρ x) (s, q) ∂spatialVolume L) =
      (Ici x.1).indicator (fun s => coneRadialSlice ρ (s - x.1)) s := by
    by_cases hxs : x.1 ≤ s
    · rw [indicator_of_mem (show s ∈ Ici x.1 from hxs), coneRadialSlice_eq_radial]
      have he (q : Space L) : C.indicator (thinKernel L ρ x) (s, q) =
          {q | (spatialDistance L).distance x.2 q ≤ s - x.1}.indicator
            (fun q => bdgKernel ((Real.pi / 24) * ρ *
              ((s - x.1) ^ 2 - (spatialDistance L).distance x.2 q ^ 2) ^ 2)) q := rfl
      simp_rw [he]
      have hm : MeasurableSet {q | (spatialDistance L).distance x.2 q ≤ s - x.1} :=
        (isClosed_le
          (Continuous.comp (f := fun q : Space L => (x.2, q))
            (g := fun z : Space L × Space L => (spatialDistance L).distance z.1 z.2)
            (spatialDistance L).continuous (continuous_const.prodMk continuous_id))
          continuous_const).measurableSet
      rw [integral_indicator hm]
      exact integral_spatial_causal L x.2 (sub_nonneg.mpr hxs)
        (by linarith [hx.1.1, hs.2])
        (fun r : ℝ => bdgKernel ((Real.pi / 24) * ρ * ((s - x.1) ^ 2 - r ^ 2) ^ 2))
        (by unfold bdgKernel bdgPolynomial; fun_prop)
    · rw [indicator_of_not_mem (show s ∉ Ici x.1 from hxs)]
      apply integral_eq_zero_of_ae
      apply Eventually.of_forall
      intro q
      change C.indicator (thinKernel L ρ x) (s, q) = 0
      apply indicator_of_not_mem
      intro h
      exact hxs (Ultrastatic.time_le (spatialDistance L) (x := x) (y := (s, q)) h)
  rw [setIntegral_congr_fun measurableSet_Ioo hf, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici x.1 ∩ Ioo (-T / 2) (T / 2) = Ico x.1 (T / 2) := by
    ext s
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hx.1.1.trans_le h.1, h.2⟩
  rw [hset, ← integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx.1.2.le,
    intervalIntegral.integral_comp_sub_right, sub_self]
  rfl

/-- Both endpoint time faces and the whole quotient spatial volume. -/
theorem integral_time {T : ℝ} (hT : 0 ≤ T) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x : ℝ × Space L, g x.1 ∂slabVolume L T) =
      L ^ 3 * ∫ t in (-T / 2)..(T / 2), g t := by
  have hi : Integrable (fun x : ℝ × Space L => g x.1) (slabVolume L T) :=
    ((hg.comp continuous_fst).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set (Space L))))).mono_set
      (show slab L T ⊆ Icc (-T / 2) (T / 2) ×ˢ univ from
        fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, h.2⟩)
  have hvol : slabVolume L T =
      (volume.restrict (Ioo (-T / 2) (T / 2))).prod (spatialVolume L) := by
    rw [slabVolume, Ultrastatic.slabVolume, Ultrastatic.slab, ← Measure.prod_restrict,
      Measure.restrict_univ]
  rw [hvol, integral_prod _ (by rwa [hvol] at hi)]
  simp only [integral_const, Measure.real, spatialVolume_univ, smul_eq_mul,
    ENNReal.toReal_ofReal (pow_nonneg (le_of_lt (Fact.out : 0 < L)) 3)]
  rw [integral_const_mul, ← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -T / 2 ≤ T / 2)]

/-- The full two-endpoint pair integral, before any asymptotic argument. -/
theorem pair_integral {T : ℝ} (hT0 : 0 ≤ T) (hT : 2 * T < L) (ρ : ℝ) :
    (∫ x, ∫ y in {y | (measuredOrder L).Rel x y},
      bdgKernel (ρ * (slabVolume L T ((measuredOrder L).interval x y)).toReal)
        ∂slabVolume L T ∂slabVolume L T) =
      L ^ 3 * ∫ u in (0 : ℝ)..T, coneRadialIntegral ρ u := by
  calc
    _ = ∫ x : ℝ × Space L, coneRadialIntegral ρ (T / 2 - x.1) ∂slabVolume L T := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (Ultrastatic.measurable_slab T)] with x hx
      exact inner_integral L hT ρ hx
    _ = _ := by
      rw [integral_time L hT0 (fun t => coneRadialIntegral ρ (T / 2 - t))
        ((continuous_coneRadialIntegral ρ).comp (continuous_const.sub continuous_id)),
        intervalIntegral.integral_comp_sub_left, sub_self,
        show T / 2 - -T / 2 = T by ring]

/-- Time-triangle Fubini in its weighted form; the factor `T-u` includes BOTH
endpoint times. The identity follows from the continuous finite primitives. -/
theorem pair_integral_radial {T : ℝ} (hT0 : 0 ≤ T) (hT : 2 * T < L) (ρ : ℝ) :
    (∫ x, ∫ y in {y | (measuredOrder L).Rel x y},
      bdgKernel (ρ * (slabVolume L T ((measuredOrder L).interval x y)).toReal)
        ∂slabVolume L T ∂slabVolume L T) =
      L ^ 3 * (4 * Real.pi * ∫ τ in (0 : ℝ)..T, (T - τ) *
        ∫ r in (0 : ℝ)..τ, r ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (τ ^ 2 - r ^ 2) ^ 2)) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => T - t) (u' := fun _ => (-1 : ℝ))
    (v := coneRadialIntegral ρ) (v' := coneRadialSlice ρ)
    (a := (0 : ℝ)) (b := T)
    (fun t _ => by simpa using (hasDerivAt_id t).const_sub T)
    (fun t _ => ((continuous_coneRadialSlice ρ).integral_hasStrictDerivAt 0 t).hasDerivAt)
    (continuous_const.intervalIntegrable _ _)
    ((continuous_coneRadialSlice ρ).intervalIntegrable _ _)
  simp only [sub_self, zero_mul, coneRadialIntegral, intervalIntegral.integral_same,
    mul_zero, zero_sub, neg_mul, one_mul, intervalIntegral.integral_neg, neg_neg] at h
  change (∫ t in (0 : ℝ)..T, (T - t) * coneRadialSlice ρ t) =
    ∫ t in (0 : ℝ)..T, coneRadialIntegral ρ t at h
  rw [pair_integral L hT0 hT, ← h]
  simp_rw [coneRadialSlice_eq_radial]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro τ _
  ring

/-- Exact finite-density identity with the existing derivative-defined kernel.
This is proved from the actual quotient action, not used as its definition. -/
theorem action_eq_planeKernel {T : ℝ} (hT0 : 0 ≤ T) (hT : 2 * T < L) (ρ : ℝ) :
    MeasuredOrderBDG4.action (measuredOrder L) (slabVolume L T) ρ = L ^ 3 * planeKernel ρ T := by
  rw [MeasuredOrderBDG4.action_eq, slabVolume_univ,
    ENNReal.toReal_ofReal (mul_nonneg hT0 (pow_nonneg (le_of_lt (Fact.out : 0 < L)) 3)),
    pair_integral L hT0 hT, ← integral_radial_actionDensity]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable _ _)
    ((continuous_const.mul (continuous_coneRadialIntegral ρ)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul]
  ring

end CompactTorus
end BoundaryDraft
