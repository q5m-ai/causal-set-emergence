import BoundaryDraft.EllipsoidGeometry
import BoundaryDraft.ConeIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Exact four-dimensional graph-cap reduction

The original coordinate-product Lebesgue integral is decomposed using a
measure-preserving equivalence. Compact boxes dominate both the cap and the
truncated cone, providing absolute integrability for Fubini. Spatial polar
integration computes the coefficient from the Euclidean three-ball volume.
Translation and the proved complete-future theorem then identify each inner
integral; the vertical FTC gives `GraphReductionGoal` at every positive density.
No coarea formula or density limit is asserted here.
-/

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section
namespace BoundaryDraft

private def coordEquiv : ℝ × Spatial ≃ᵐ Spacetime :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm

private theorem coordEquiv_apply (t : ℝ) (x : Spatial) :
    coordEquiv (t, x) = Fin.cons t x := by
  simp [coordEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

private theorem coordEquiv_measurePreserving : MeasurePreserving coordEquiv :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm _

/-- Fubini in the original product Lebesgue measure, with time integrated
first. Absolute integrability is an explicit premise of the interchange. -/
theorem integral_spacetime_fibres (f : Spacetime → ℝ) (hf : Integrable f) :
    (∫ p, f p) = ∫ x : Spatial, ∫ t : ℝ, f (Fin.cons t x) := by
  have hi := (coordEquiv_measurePreserving.integrable_comp_emb
    coordEquiv.measurableEmbedding).mpr hf
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  rw [← coordEquiv_measurePreserving.integral_comp' f,
    Measure.volume_eq_prod, integral_prod_symm _ hi]
  simp_rw [coordEquiv_apply]

/-- Fubini with spatial slices integrated first. -/
theorem integral_spacetime_slices (f : Spacetime → ℝ) (hf : Integrable f) :
    (∫ p, f p) = ∫ t : ℝ, ∫ x : Spatial, f (Fin.cons t x) := by
  have hi := (coordEquiv_measurePreserving.integrable_comp_emb
    coordEquiv.measurableEmbedding).mpr hf
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  rw [← coordEquiv_measurePreserving.integral_comp' f,
    Measure.volume_eq_prod, integral_prod _ hi]
  simp_rw [coordEquiv_apply]

@[simp] theorem spatialPart_cons (t : ℝ) (x : Spatial) : spatialPart (Fin.cons t x) = x := by
  ext i
  simp [spatialPart]

private theorem continuous_spatialPart : Continuous spatialPart := by
  unfold spatialPart
  fun_prop

private theorem measurableSet_graphCap (h : Spatial → ℝ) (hc : Continuous h) :
    MeasurableSet (graphCapRegion h) := by
  exact ((isOpen_lt (hc.comp continuous_spatialPart).neg (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)).measurableSet

private theorem graphCap_subset_box (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) : graphCapRegion (ellipsoidProfile a b) ⊆
      Icc (Fin.cons (-a) (-b)) (Fin.cons 0 b) := by
  intro p hp
  have hh : 0 < ellipsoidProfile a b (spatialPart p) := by
    have := hp.1
    have := hp.2
    linarith
  have hs := ellipsoid_positive_subset_box a b ha hb hh
  have hu := ellipsoidProfile_le a b ha.le (spatialPart p)
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [hp.1]
    · exact hs.1 j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp.2.le
    · exact hs.2 j

/-- Compact domination supplies absolute integrability on the cap. -/
theorem integrableOn_ellipsoid_cap (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (f : Spacetime → ℝ) (hf : Continuous f) :
    IntegrableOn f (graphCapRegion (ellipsoidProfile a b)) :=
  hf.integrableOn_Icc.mono_set (graphCap_subset_box a b ha hb)

/-- Compact domination for every reduction-admissible cap. -/
theorem integrableOn_graphCap (h : Spatial → ℝ) (hh : GraphCapData h)
    (f : Spacetime → ℝ) (hf : Continuous f) : IntegrableOn f (graphCapRegion h) := by
  obtain ⟨R, hR⟩ := hh.cap_subset_box
  exact hf.integrableOn_Icc.mono_set hR

/-- Spatial absolute integrability uses the continuous positive part, so no
regularity of the raw profile outside its positive region is needed. -/
theorem integrableOn_graphCap_profile (h : Spatial → ℝ) (hh : GraphCapData h)
    (f : ℝ → ℝ) (hf : Continuous f) : IntegrableOn (fun x => f (h x)) {x | 0 < h x} := by
  have hi : IntegrableOn (fun x => f (max 0 (h x))) {x | 0 < h x} :=
    ((hf.comp hh.continuous_positivePart).continuousOn.integrableOn_compact
      hh.bounded_positive.isCompact_closure).mono_set subset_closure
  apply hi.congr_fun _ hh.measurableSet_positive
  intro x hx
  dsimp only
  rw [max_eq_right (le_of_lt hx)]

/-- Absolute integrability of the actual bilocal kernel, including causal
restriction, follows from a compact product box before any integration. -/
theorem integrableOn_graphCap_bdg (h : Spatial → ℝ) (hh : GraphCapData h) (ρ : ℝ) :
    IntegrableOn (fun p : Spacetime × Spacetime =>
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
      ((graphCapRegion h ×ˢ graphCapRegion h) ∩ {p | p.2 ∈ causalFuture p.1}) := by
  obtain ⟨R, hR⟩ := hh.cap_subset_box
  have hc : Continuous (fun p : Spacetime × Spacetime =>
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2)) := by
    unfold bdgKernel bdgPolynomial intervalSq spatialSeparationSq
    fun_prop
  apply (hc.continuousOn.integrableOn_compact
    ((isCompact_Icc : IsCompact (Icc (fun _ : Fin 4 => -R) (fun _ => R))).prod
      (isCompact_Icc : IsCompact (Icc (fun _ : Fin 4 => -R) (fun _ => R))))).mono_set
  intro p hp
  exact ⟨hR hp.1.1, hR hp.1.2⟩

/-- Profile-independent vertical Fubini, including null endpoint replacements.
Only measurability and absolute integrability are needed at this step. -/
theorem integral_graphCap_depth_of_integrable (h : Spatial → ℝ)
    (hm : MeasurableSet (graphCapRegion h)) (hpos : MeasurableSet {x | 0 < h x})
    (f : ℝ → ℝ) (hi : IntegrableOn (fun p : Spacetime => f (-p 0)) (graphCapRegion h)) :
    (∫ p in graphCapRegion h, f (-p 0)) =
      ∫ x in {x | 0 < h x}, ∫ t in (0 : ℝ)..h x, f t := by
  rw [← integral_indicator hm, integral_spacetime_fibres _ ((integrable_indicator_iff hm).mpr hi),
    ← integral_indicator hpos]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have he (t : ℝ) : (graphCapRegion h).indicator (fun p : Spacetime => f (-p 0)) (Fin.cons t x) =
        (Ioo (-h x) 0).indicator (fun t => f (-t)) t := by
      simp [Set.indicator, graphCapRegion]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    by_cases hx : 0 < h x
    · rw [Set.indicator_of_mem (show x ∈ {x | 0 < h x} from hx),
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : -h x ≤ 0)]
      simpa only [neg_zero, neg_neg] using
        (intervalIntegral.integral_comp_neg (a := -h x) (b := 0) f)
    · rw [Set.indicator_of_not_mem (show x ∉ {x | 0 < h x} from hx)]
      have hempty : Ioo (-h x) 0 = ∅ := Ioo_eq_empty_of_le (by linarith)
      rw [hempty, setIntegral_empty]

/-- Exact vertical integration on every cap in the general reduction class. -/
theorem integral_graphCap_depth (h : Spatial → ℝ) (hh : GraphCapData h)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in graphCapRegion h, f (-p 0)) =
      ∫ x in {x | 0 < h x}, ∫ t in (0 : ℝ)..h x, f t :=
  integral_graphCap_depth_of_integrable h hh.measurableSet_cap hh.measurableSet_positive f
    (integrableOn_graphCap h hh _ (hf.comp ((continuous_apply 0).neg)))

/-- The original ellipsoid fibre formula keeps its weaker positive-axis hypotheses. -/
theorem integral_ellipsoid_depth (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 0 < b i) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in graphCapRegion (ellipsoidProfile a b), f (-p 0)) =
      ∫ x in {x | 0 < ellipsoidProfile a b x},
        ∫ t in (0 : ℝ)..ellipsoidProfile a b x, f t :=
  integral_graphCap_depth_of_integrable _
    (measurableSet_graphCap _ (continuous_ellipsoidProfile a b))
    (measurableSet_ellipsoid_positive a b) f
    (integrableOn_ellipsoid_cap a b ha hb _ (hf.comp ((continuous_apply 0).neg)))

private def euclideanEquiv : EuclideanSpace ℝ (Fin 3) ≃ᵐ Spatial :=
  { WithLp.equiv 2 _ with
    measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)).measurable
    measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).measurable }

/-- Polar integration with the actual product Lebesgue measure on `Spatial`.
The coefficient is computed from the Euclidean three-ball, not stipulated. -/
theorem integral_spatial_radial (H : ℝ) (hH : 0 ≤ H) (f : ℝ → ℝ) :
    (∫ x in {x : Spatial | (∑ i : Fin 3, x i ^ 2) ≤ H ^ 2}, f (∑ i : Fin 3, x i ^ 2)) =
      4 * Real.pi * ∫ r in (0 : ℝ)..H, r ^ 2 * f (r ^ 2) := by
  let s := {x : Spatial | (∑ i : Fin 3, x i ^ 2) ≤ H ^ 2}
  have hs : MeasurableSet s := by
    apply isClosed_le ?_ continuous_const |>.measurableSet
    fun_prop
  have he (x : EuclideanSpace ℝ (Fin 3)) : ∑ i : Fin 3, (euclideanEquiv x) i ^ 2 = ‖x‖ ^ 2 := by
    simp [euclideanEquiv, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  have hem : MeasurePreserving euclideanEquiv := PiLp.volume_preserving_equiv (Fin 3)
  rw [← integral_indicator hs, ← hem.integral_comp']
  have hi (x : EuclideanSpace ℝ (Fin 3)) :
      s.indicator (fun x => f (∑ i : Fin 3, x i ^ 2)) (euclideanEquiv x) =
        (Icc 0 H).indicator (fun r => f (r ^ 2)) ‖x‖ := by
    have hx : euclideanEquiv x ∈ s ↔ ‖x‖ ∈ Icc 0 H := by
      dsimp [s]
      rw [he, sq_le_sq₀ (norm_nonneg _) hH]
      simp [norm_nonneg]
    simp only [Set.indicator, hx, he]
  simp_rw [hi]
  rw [integral_fun_norm_addHaar]
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1) =
      Real.pi * 4 / 3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_ofReal,
      show 0 ≤ Real.pi * 4 / 3 by positivity]
  simp only [finrank_euclideanSpace, Fintype.card_fin, hv, Nat.reduceSub,
    nsmul_eq_mul, smul_eq_mul]
  have hh : (∫ r in Ioi (0 : ℝ), r ^ 2 * (Icc 0 H).indicator (fun r => f (r ^ 2)) r) =
      ∫ r in (0 : ℝ)..H, r ^ 2 * f (r ^ 2) := by
    simp_rw [← Set.indicator_mul_right (Icc 0 H) (fun r => r ^ 2) (fun r => f (r ^ 2))]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hset : Icc 0 H ∩ Ioi (0 : ℝ) = Ioc 0 H := by
      ext r
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
    rw [hset, intervalIntegral.integral_of_le hH]
  rw [hh]
  ring

/-- The complete future cone at the origin, cut by the plane `t = H`.
The vertex and null surface are retained; the upper plane is excluded. -/
def truncatedFutureCone (H : ℝ) : Set Spacetime :=
  {p | p ∈ causalFuture 0 ∧ p 0 < H}

private theorem continuous_intervalSq (x : Spacetime) : Continuous (intervalSq x) := by
  unfold intervalSq spatialSeparationSq
  fun_prop

private theorem measurableSet_causalFuture (x : Spacetime) : MeasurableSet (causalFuture x) := by
  apply MeasurableSet.inter
  · exact (isClosed_le continuous_const (continuous_apply 0)).measurableSet
  · change MeasurableSet {y | spatialSeparationSq x y ≤ (y 0 - x 0) ^ 2}
    apply (isClosed_le (f := fun y => spatialSeparationSq x y)
      (g := fun y => (y 0 - x 0) ^ 2) ?_ ?_).measurableSet
    · unfold spatialSeparationSq
      fun_prop
    · fun_prop

private theorem measurableSet_truncatedFutureCone (H : ℝ) : MeasurableSet (truncatedFutureCone H) :=
  (measurableSet_causalFuture 0).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).measurableSet)

private theorem truncatedFutureCone_subset_box (H : ℝ) (hH : 0 ≤ H) :
    truncatedFutureCone H ⊆ Icc (fun _ => -H) (fun _ => H) := by
  intro p hp
  have ht0 : 0 ≤ p 0 := hp.1.1
  have htH : p 0 < H := hp.2
  have hsum : (∑ i : Fin 3, p i.succ ^ 2) ≤ (p 0) ^ 2 := by
    simpa [causalFuture, spatialSeparationSq] using hp.1.2
  have hs (i : Fin 3) : |p i.succ| ≤ H := by
    have hi : p i.succ ^ 2 ≤ H ^ 2 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (p j.succ)) (Finset.mem_univ i)).trans
        (hsum.trans ((sq_le_sq₀ ht0 hH).mpr htH.le))
    exact (sq_le_sq₀ (abs_nonneg _) hH).mp (by rwa [sq_abs])
  constructor <;> intro i
  · refine Fin.cases ?_ (fun j => (abs_le.mp (hs j)).1) i
    change -H ≤ p 0
    linarith
  · refine Fin.cases htH.le (fun j => (abs_le.mp (hs j)).2) i

/-- The concrete BDG integral over the four-dimensional truncated cone. -/
def coneIntegral (ρ H : ℝ) : ℝ :=
  ∫ p in truncatedFutureCone H, bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 p ^ 2)

/-- Coordinate Fubini and Euclidean polar integration identify the actual
four-dimensional cone integral with the already evaluated radial-time one. -/
theorem coneIntegral_eq_radial (ρ H : ℝ) (hH : 0 ≤ H) :
    coneIntegral ρ H = coneRadialIntegral ρ H := by
  let f := fun p : Spacetime => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 p ^ 2)
  have hf : Continuous f := by
    dsimp [f, bdgKernel, bdgPolynomial]
    have := continuous_intervalSq (0 : Spacetime)
    fun_prop
  have hi : IntegrableOn f (truncatedFutureCone H) :=
    hf.integrableOn_Icc.mono_set (truncatedFutureCone_subset_box H hH)
  have hm := measurableSet_truncatedFutureCone H
  unfold coneIntegral
  change (∫ p in truncatedFutureCone H, f p) = _
  rw [← integral_indicator hm, integral_spacetime_slices _ ((integrable_indicator_iff hm).mpr hi)]
  have he (t : ℝ) : (∫ x : Spatial, (truncatedFutureCone H).indicator f (Fin.cons t x)) =
      (Ico 0 H).indicator (coneRadialSlice ρ) t := by
    by_cases ht : t ∈ Ico 0 H
    · have he' (x : Spatial) : (truncatedFutureCone H).indicator f (Fin.cons t x) =
          {x : Spatial | ∑ i : Fin 3, x i ^ 2 ≤ t ^ 2}.indicator
            (fun x => bdgKernel ((Real.pi / 24) * ρ * (t ^ 2 - ∑ i : Fin 3, x i ^ 2) ^ 2)) x := by
        simp [Set.indicator, truncatedFutureCone, causalFuture, spatialSeparationSq,
          intervalSq, f, ht.1, ht.2]
      simp_rw [he']
      have hs : MeasurableSet {x : Spatial | ∑ i : Fin 3, x i ^ 2 ≤ t ^ 2} := by
        apply isClosed_le ?_ continuous_const |>.measurableSet
        fun_prop
      rw [Set.indicator_of_mem ht, integral_indicator hs,
        integral_spatial_radial t ht.1 (fun s => bdgKernel ((Real.pi / 24) * ρ * (t ^ 2 - s) ^ 2)),
        coneRadialSlice_eq_radial]
    · have he' (x : Spatial) : (truncatedFutureCone H).indicator f (Fin.cons t x) = 0 := by
        apply Set.indicator_of_not_mem
        intro hp
        exact ht ⟨hp.1.1, hp.2⟩
      simp_rw [he']
      rw [Set.indicator_of_not_mem ht, integral_zero]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hH]
  rfl

/-- Exact action density for the original four-dimensional cone integral. -/
theorem planeAuxiliaryThird_eq_coneIntegral (ρ H : ℝ) (hH : 0 ≤ H) :
    planeAuxiliaryThird ρ H / (8 * Real.pi) = 1 - ρ * coneIntegral ρ H := by
  rw [coneIntegral_eq_radial ρ H hH, planeAuxiliaryThird_eq_coneRadialIntegral]

/-- Every individual future-point kernel integral is absolutely integrable. -/
theorem integrableOn_graphCap_future_bdg (h : Spatial → ℝ) (hh : GraphCapData h)
    (ρ : ℝ) (x : Spacetime) :
    IntegrableOn (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2))
      (graphCapRegion h ∩ causalFuture x) := by
  apply (integrableOn_graphCap h hh _ ?_).mono_set inter_subset_left
  unfold bdgKernel bdgPolynomial
  have := continuous_intervalSq x
  fun_prop

/-- Translation of the complete future slice to the cone at the origin.
This starts from the concrete kernel and the actual cap/causal intersection. -/
theorem graphCap_future_integral (h : Spatial → ℝ) (hh : GraphCapData h) (ρ : ℝ)
    (x : Spacetime) (hx : x ∈ graphCapRegion h) :
    (∫ y in graphCapRegion h ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) = coneIntegral ρ (-x 0) := by
  rw [graphCap_complete_future h hh x hx]
  have hm : MeasurableSet {y | y ∈ causalFuture x ∧ y 0 < 0} :=
    (measurableSet_causalFuture x).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).measurableSet)
  rw [← integral_indicator hm, ← integral_add_left_eq_self _ x, coneIntegral,
    ← integral_indicator (measurableSet_truncatedFutureCone (-x 0))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    have ht : x 0 + p 0 < 0 ↔ p 0 < -x 0 := by constructor <;> intro ht <;> linarith
    simp [Set.indicator, truncatedFutureCone, causalFuture, intervalSq,
      spatialSeparationSq, ht]

/-- The original ellipsoid translation theorem is a specialization. -/
theorem ellipsoid_future_integral (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) (ρ : ℝ)
    (x : Spacetime) (hx : x ∈ graphCapRegion (ellipsoidProfile a b)) :
    (∫ y in graphCapRegion (ellipsoidProfile a b) ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) = coneIntegral ρ (-x 0) :=
  graphCap_future_integral _ (ellipsoid_graphCapData a b ha hb) ρ x hx

/-- Exact deterministic reduction from the unchanged four-dimensional action.
No regular-level, coarea, limit, or reduction premise is used. -/
theorem graphCap_graphReduction (h : Spatial → ℝ) (hh : GraphCapData h) :
    GraphReductionGoal h := by
  intro ρ _hρ
  let M := graphCapRegion h
  have hm : MeasurableSet M := hh.measurableSet_cap
  have hi1 : IntegrableOn (fun _ : Spacetime => (1 : ℝ)) M :=
    integrableOn_graphCap h hh _ continuous_const
  have hiQ : IntegrableOn (fun x : Spacetime => coneRadialIntegral ρ (-x 0)) M :=
    integrableOn_graphCap h hh _
      ((continuous_coneRadialIntegral ρ).comp ((continuous_apply 0).neg))
  have hinner : (∫ x in M, ∫ y in M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
        ∫ x in M, coneRadialIntegral ρ (-x 0) := by
    apply setIntegral_congr_fun hm
    intro x hx
    dsimp only [M] at hx ⊢
    rw [graphCap_future_integral h hh ρ x hx,
      coneIntegral_eq_radial ρ (-x 0) (neg_nonneg.mpr hx.2.le)]
  have hc : Continuous (fun t => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (1 - ρ * coneRadialIntegral ρ t)) :=
    continuous_const.mul (continuous_const.sub (continuous_const.mul (continuous_coneRadialIntegral ρ)))
  unfold continuumMean
  change (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ _x in M, (1 : ℝ)) - ρ * ∫ x in M, ∫ y in M ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) = _
  rw [hinner, ← integral_const_mul, ← integral_sub hi1 (hiQ.const_mul ρ),
    ← integral_const_mul]
  rw [integral_graphCap_depth h hh _ hc]
  apply setIntegral_congr_fun hh.measurableSet_positive
  intro x _
  exact integral_radial_actionDensity ρ (h x)

/-- Every admissible C³ graph cap has the exact finite-density reduction. -/
theorem AdmissibleGraphCap.graphReduction {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) :
    GraphReductionGoal h := graphCap_graphReduction h hh.toGraphCapData

/-- The original concrete theorem, with its original hypotheses and conclusion. -/
theorem ellipsoid_graphReduction (a : ℝ) (b : Fin 3 → ℝ)
    (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    GraphReductionGoal (ellipsoidProfile a b) :=
  graphCap_graphReduction _ (ellipsoid_graphCapData a b ha hb)

end BoundaryDraft
