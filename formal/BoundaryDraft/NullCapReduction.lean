import BoundaryDraft.NullCoordinates

/-!
# Exact reduction of the null-plane cap

The concrete open cap is pulled back through the audited null-coordinate map.
Transverse polar integration then leaves a three-variable region whose two
linear null-coordinate bounds produce the exact logarithmic weight.
-/

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section
namespace BoundaryDraft

private def transverseSq (p : Plane) : ℝ := ∑ i : Fin 2, p i ^ 2

private def nullSigma (p : Spacetime) : ℝ :=
  2 * p 0 * p 1 - (p 2 ^ 2 + p 3 ^ 2)

private def nullDefect (T u v : ℝ) : ℝ :=
  Real.sqrt 2 * T * (u + v) - T ^ 2

private def nullLower (T u v : ℝ) : ℝ := max 0 (nullDefect T u v)

private def nullUVRegion (T a : ℝ) : Set Plane :=
  {p | 0 < p 0 ∧ 0 < p 1 ∧ p 1 < a / Real.sqrt 2 ∧
    nullLower T (p 0) (p 1) < 2 * p 0 * p 1}

private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num)

private theorem two_div_sqrt_two : 2 / Real.sqrt 2 = Real.sqrt 2 := by
  apply (div_eq_iff sqrt_two_pos.ne').mpr
  nlinarith [sqrt_two_sq]

private theorem null_future_difference (u v : ℝ) :
    ((u + v) / Real.sqrt 2) ^ 2 - ((v - u) / Real.sqrt 2) ^ 2 =
      2 * u * v := by
  field_simp
  nlinarith [sqrt_two_sq]

private theorem null_past_difference (T u v : ℝ) :
    (T - (u + v) / Real.sqrt 2) ^ 2 - ((v - u) / Real.sqrt 2) ^ 2 =
      2 * u * v - nullDefect T u v := by
  unfold nullDefect
  field_simp
  nlinarith [sqrt_two_sq]

private theorem intervalSq_nullCapMatrix (p : Spacetime) :
    intervalSq (Matrix.toLin' nullCapMatrix p) 0 = nullSigma p := by
  rw [nullCapMatrix_apply]
  simp [intervalSq, spatialSeparationSq, nullSigma, Fin.sum_univ_succ]
  field_simp
  nlinarith [sqrt_two_sq]

private theorem nullCapMatrix_mem_iff (T a : ℝ) (ha : 0 < a) (haT : a < T)
    (p : Spacetime) :
    Matrix.toLin' nullCapMatrix p ∈ nullCapRegion T a ↔
      0 < p 0 ∧ 0 < p 1 ∧ p 1 < a / Real.sqrt 2 ∧
        p 2 ^ 2 + p 3 ^ 2 < 2 * p 0 * p 1 ∧
        p 2 ^ 2 + p 3 ^ 2 <
          2 * p 0 * p 1 - nullDefect T (p 0) (p 1) := by
  rw [nullCapMatrix_apply]
  let x : Spacetime :=
    ![-(p 0 + p 1) / Real.sqrt 2,
      (p 1 - p 0) / Real.sqrt 2, p 2, p 3]
  change x ∈ nullCapRegion T a ↔ _
  have hx0 : x 0 = -(p 0 + p 1) / Real.sqrt 2 := by simp [x]
  have hx1 : x 1 = (p 1 - p 0) / Real.sqrt 2 := by simp [x]
  have hx2 : x 2 = p 2 := by simp [x]
  have hx3 : x 3 = p 3 := by simp [x]
  have hs0 := sqrt_two_pos
  have hs2 := sqrt_two_sq
  have hxcut : x 0 - x 1 = -Real.sqrt 2 * p 1 := by
    calc
      x 0 - x 1 = -(2 * p 1) / Real.sqrt 2 := by rw [hx0, hx1]; ring
      _ = -(2 / Real.sqrt 2) * p 1 := by ring
      _ = -Real.sqrt 2 * p 1 := by rw [two_div_sqrt_two]
  constructor
  · intro hp
    rcases hp with ⟨hpast, hfuture, hcut⟩
    have hft : 0 < p 0 + p 1 := by
      have := hfuture.1
      simp [x] at this
      rcases div_neg_iff.mp this with hneg | hneg
      · linarith
      · linarith
    have hfq : p 2 ^ 2 + p 3 ^ 2 < 2 * p 0 * p 1 := by
      have hq := hfuture.2
      have hspace : spatialSeparationSq x 0 =
          ((p 1 - p 0) / Real.sqrt 2) ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
        simp [spatialSeparationSq, x, Fin.sum_univ_succ]
        ring
      rw [hspace, hx0] at hq
      field_simp at hq
      nlinarith [hs2]
    have huv : 0 < p 0 * p 1 := by
      have hq : 0 ≤ p 2 ^ 2 + p 3 ^ 2 := by positivity
      nlinarith
    have hu : 0 < p 0 := by
      rcases (mul_pos_iff.mp huv) with hpos | hneg
      · exact hpos.1
      · linarith [hft, hneg.1, hneg.2]
    have hv : 0 < p 1 := by
      rcases (mul_pos_iff.mp huv) with hpos | hneg
      · exact hpos.2
      · linarith [hft, hneg.1, hneg.2]
    have hvcut : p 1 < a / Real.sqrt 2 := by
      rw [hxcut] at hcut
      apply (lt_div_iff₀ hs0).mpr
      have hmul : (p 1 * Real.sqrt 2) * Real.sqrt 2 <
          a * Real.sqrt 2 := by nlinarith [hs2, hcut]
      exact (mul_lt_mul_right hs0).mp hmul
    have hpq : p 2 ^ 2 + p 3 ^ 2 <
        2 * p 0 * p 1 - nullDefect T (p 0) (p 1) := by
      have hq := hpast.2
      have hspace : spatialSeparationSq (pastTip T) x =
          ((p 1 - p 0) / Real.sqrt 2) ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
        simp [spatialSeparationSq, pastTip, x, Fin.sum_univ_succ]
        ring
      rw [hspace, hx0] at hq
      unfold nullDefect
      field_simp at hq
      nlinarith [hs2]
    exact ⟨hu, hv, hvcut, hfq, hpq⟩
  · rintro ⟨hu, hv, hvcut, hfq, hpq⟩
    have hvT : p 1 < T / Real.sqrt 2 :=
      hvcut.trans (div_lt_div_of_pos_right haT hs0)
    have hfactor : 0 < (T - Real.sqrt 2 * p 0) *
        (T - Real.sqrt 2 * p 1) := by
      have hq : 0 ≤ p 2 ^ 2 + p 3 ^ 2 := by positivity
      have : 0 < 2 * p 0 * p 1 - nullDefect T (p 0) (p 1) :=
        hq.trans_lt hpq
      unfold nullDefect at this
      nlinarith
    have hvfactor : 0 < T - Real.sqrt 2 * p 1 := by
      have hvT' := (lt_div_iff₀ hs0).mp hvT
      nlinarith
    have hufactor : 0 < T - Real.sqrt 2 * p 0 :=
      pos_of_mul_pos_left hfactor hvfactor.le
    have huT : p 0 < T / Real.sqrt 2 := by
      apply (lt_div_iff₀ hs0).mpr
      nlinarith
    have hsumT : p 0 + p 1 < Real.sqrt 2 * T := by
      rw [← two_div_sqrt_two]
      have := add_lt_add huT hvT
      field_simp at this ⊢
      nlinarith
    have hpastTime : (pastTip T) 0 < x 0 := by
      rw [hx0]
      simp only [pastTip, if_pos]
      apply (lt_div_iff₀ hs0).mpr
      linarith [hsumT]
    have hpastSq : spatialSeparationSq (pastTip T) x <
        (x 0 - (pastTip T) 0) ^ 2 := by
      have hspace : spatialSeparationSq (pastTip T) x =
          ((p 1 - p 0) / Real.sqrt 2) ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
        simp [spatialSeparationSq, pastTip, x, Fin.sum_univ_succ]
        ring
      rw [hspace, hx0]
      simp only [pastTip, if_pos]
      have htime : (-(p 0 + p 1) / Real.sqrt 2 - -T) ^ 2 =
          (T - (p 0 + p 1) / Real.sqrt 2) ^ 2 := by ring
      rw [htime]
      linarith [null_past_difference T (p 0) (p 1)]
    have hfutureTime : x 0 < 0 := by
      rw [hx0]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (add_pos hu hv)) hs0
    have hfutureSq : spatialSeparationSq x 0 < (0 - x 0) ^ 2 := by
      have hspace : spatialSeparationSq x 0 =
          ((p 1 - p 0) / Real.sqrt 2) ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
        simp [spatialSeparationSq, x, Fin.sum_univ_succ]
        ring
      rw [hspace, hx0]
      have htime : (0 - (-(p 0 + p 1) / Real.sqrt 2)) ^ 2 =
          ((p 0 + p 1) / Real.sqrt 2) ^ 2 := by ring
      rw [htime]
      linarith [null_future_difference (p 0) (p 1)]
    have hcut : -a < x 0 - x 1 := by
      rw [hxcut]
      have hvcut' : p 1 * Real.sqrt 2 < a := (lt_div_iff₀ hs0).mp hvcut
      linarith
    exact ⟨⟨hpastTime, hpastSq⟩, ⟨hfutureTime, hfutureSq⟩, hcut⟩

private theorem null_gap_factor (T u v : ℝ) :
    2 * u * v - nullDefect T u v =
      (T - Real.sqrt 2 * u) * (T - Real.sqrt 2 * v) := by
  unfold nullDefect
  calc
    2 * u * v - (Real.sqrt 2 * T * (u + v) - T ^ 2) =
        T ^ 2 - Real.sqrt 2 * T * (u + v) + 2 * u * v := by ring
    _ = T ^ 2 - Real.sqrt 2 * T * (u + v) +
        (Real.sqrt 2) ^ 2 * u * v := by rw [sqrt_two_sq]
    _ = _ := by ring

private theorem nullLower_lt_iff (T u v q : ℝ) :
    q < 2 * u * v - nullLower T u v ↔
      q < 2 * u * v ∧ q < 2 * u * v - nullDefect T u v := by
  unfold nullLower
  rcases le_total (nullDefect T u v) 0 with h | h
  · rw [max_eq_left h]
    constructor
    · intro hq
      exact ⟨by simpa using hq, lt_of_lt_of_le hq (by linarith)⟩
    · exact fun hq => by simpa using hq.1
  · rw [max_eq_right h]
    constructor
    · intro hq
      exact ⟨lt_of_lt_of_le hq (by linarith), hq⟩
    · exact fun hq => hq.2

private theorem nullUVRegion_eq_rectangle (T a : ℝ) (ha : 0 < a) (haT : a < T) :
    nullUVRegion T a =
      {p : Plane | p 0 ∈ Ioo (0 : ℝ) (T / Real.sqrt 2) ∧
        p 1 ∈ Ioo (0 : ℝ) (a / Real.sqrt 2)} := by
  have hT : 0 < T := ha.trans haT
  ext p
  simp only [nullUVRegion, mem_setOf_eq, mem_Ioo]
  constructor
  · rintro ⟨hu, hv, hva, hL⟩
    have hvT : p 1 < T / Real.sqrt 2 :=
      hva.trans (div_lt_div_of_pos_right haT sqrt_two_pos)
    have hgap : 0 < 2 * p 0 * p 1 - nullDefect T (p 0) (p 1) := by
      have hD : nullDefect T (p 0) (p 1) ≤ nullLower T (p 0) (p 1) :=
        le_max_right _ _
      linarith
    rw [null_gap_factor] at hgap
    have hvfac : 0 < T - Real.sqrt 2 * p 1 := by
      have := (lt_div_iff₀ sqrt_two_pos).mp hvT
      linarith
    have hufac : 0 < T - Real.sqrt 2 * p 0 :=
      pos_of_mul_pos_left hgap hvfac.le
    have huT : p 0 < T / Real.sqrt 2 := by
      apply (lt_div_iff₀ sqrt_two_pos).mpr
      linarith
    exact ⟨⟨hu, huT⟩, hv, hva⟩
  · rintro ⟨⟨hu, huT⟩, hv, hva⟩
    have hvT : p 1 < T / Real.sqrt 2 :=
      hva.trans (div_lt_div_of_pos_right haT sqrt_two_pos)
    have hufac : 0 < T - Real.sqrt 2 * p 0 := by
      have := (lt_div_iff₀ sqrt_two_pos).mp huT
      linarith
    have hvfac : 0 < T - Real.sqrt 2 * p 1 := by
      have := (lt_div_iff₀ sqrt_two_pos).mp hvT
      linarith
    have hA : 0 < 2 * p 0 * p 1 := by positivity
    have hD : nullDefect T (p 0) (p 1) < 2 * p 0 * p 1 := by
      have hdiff := null_gap_factor T (p 0) (p 1)
      have hpos := mul_pos hufac hvfac
      linarith
    exact ⟨hu, hv, hva, (max_lt_iff.mpr ⟨hA, hD⟩)⟩

private def timeSpatialCoordEquiv : ℝ × Spatial ≃ᵐ Spacetime :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm

private theorem timeSpatialCoordEquiv_measurePreserving :
    MeasurePreserving timeSpatialCoordEquiv :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm _

private theorem timeSpatialCoordEquiv_apply (u : ℝ) (x : Spatial) :
    timeSpatialCoordEquiv (u, x) = Fin.cons u x := by
  simp [timeSpatialCoordEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

private theorem integrable_spacetime_slice_ae (F : Spacetime → ℝ)
    (hF : Integrable F) :
    ∀ᵐ u : ℝ, Integrable (fun x : Spatial => F (Fin.cons u x)) := by
  have hi := (timeSpatialCoordEquiv_measurePreserving.integrable_comp_emb
    timeSpatialCoordEquiv.measurableEmbedding).mpr hF
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  filter_upwards [hi.prod_right_ae] with u hu
  simpa only [timeSpatialCoordEquiv_apply] using hu

/-- Exact reduction through null coordinates and transverse polar coarea,
still with the two null coordinates outside. -/
theorem integral_nullCap_eq_nullCoordinates (T a : ℝ) (ha : 0 < a) (haT : a < T)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in nullCapRegion T a, f (intervalSq x 0)) =
      ∫ u : ℝ, ∫ v : ℝ,
        (nullUVRegion T a).indicator
          (fun p => Real.pi * ∫ σ in nullLower T (p 0) (p 1)..2 * p 0 * p 1,
            f σ) ![u, v] := by
  classical
  have hT : 0 < T := ha.trans haT
  let F := fun x : Spacetime => f (intervalSq x 0)
  have hF : Continuous F :=
    hf.comp (continuous_intervalSq.comp (continuous_id.prodMk continuous_const))
  have hi : IntegrableOn F (nullCapRegion T a) :=
    integrableOn_nullCapRegion T a hT F hF
  have hm := measurableSet_nullCapRegion T a
  let G := fun p : Spacetime => (nullCapRegion T a).indicator F
    (Matrix.toLin' nullCapMatrix p)
  have hiG : Integrable G := by
    exact (nullCapMatrix_measurePreserving.integrable_comp_emb
      nullCapMatrix_measurableEmbedding).mpr
        ((integrable_indicator_iff hm).mpr hi)
  rw [← integral_indicator hm,
    ← nullCapMatrix_measurePreserving.integral_comp
      nullCapMatrix_measurableEmbedding
      (fun x => (nullCapRegion T a).indicator F x)]
  change (∫ p, G p) = _
  rw [integral_spacetime_slices G hiG]
  apply integral_congr_ae
  filter_upwards [integrable_spacetime_slice_ae G hiG] with u hu
  rw [integral_spatial_plane_slices _ hu]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    let A := 2 * u * v
    let L := nullLower T u v
    have hpoint (r : Plane) : G (Fin.cons u (Fin.cons v r)) =
        (if (![u, v] : Plane) ∈ nullUVRegion T a then
          {r : Plane | transverseSq r < A - L}.indicator
            (fun r => f (A - transverseSq r)) r else 0) := by
      have hsigma : nullSigma (Fin.cons u (Fin.cons v r)) =
          A - transverseSq r := by
        change 2 * u * v - (r 0 ^ 2 + r 1 ^ 2) = A - transverseSq r
        simp [A, transverseSq, Fin.sum_univ_succ]
      have hmem : Matrix.toLin' nullCapMatrix (Fin.cons u (Fin.cons v r)) ∈
          nullCapRegion T a ↔
          0 < u ∧ 0 < v ∧ v < a / Real.sqrt 2 ∧
            transverseSq r < A ∧
            transverseSq r < A - nullDefect T u v := by
        simpa [transverseSq, A, Fin.sum_univ_succ] using
          nullCapMatrix_mem_iff T a ha haT (Fin.cons u (Fin.cons v r))
      by_cases huv : (![u, v] : Plane) ∈ nullUVRegion T a
      · rw [if_pos huv]
        have huv' : 0 < u ∧ 0 < v ∧ v < a / Real.sqrt 2 ∧ L < A := by
          simpa [nullUVRegion, L, A] using huv
        have hbase : 0 < u ∧ 0 < v ∧ v < a / Real.sqrt 2 :=
          ⟨huv'.1, huv'.2.1, huv'.2.2.1⟩
        have heq : transverseSq r < A - L ↔
            transverseSq r < A ∧
              transverseSq r < A - nullDefect T u v :=
          nullLower_lt_iff T u v (transverseSq r)
        by_cases hr : transverseSq r < A - L
        · simp only [Set.indicator, mem_setOf_eq, if_pos hr]
          have hboth := heq.mp hr
          have hphys := hmem.mpr ⟨hbase.1, hbase.2.1, hbase.2.2,
            hboth.1, hboth.2⟩
          dsimp only [G]
          rw [Set.indicator_of_mem hphys]
          dsimp only [F]
          rw [intervalSq_nullCapMatrix, hsigma]
        · simp only [Set.indicator, mem_setOf_eq, if_neg hr]
          dsimp only [G]
          apply Set.indicator_of_not_mem
          intro hphys
          have hc := hmem.mp hphys
          exact hr (heq.mpr ⟨hc.2.2.2.1, hc.2.2.2.2⟩)
      · rw [if_neg huv]
        dsimp only [G]
        apply Set.indicator_of_not_mem
        intro hphys
        have hc := hmem.mp hphys
        apply huv
        have hq : 0 ≤ transverseSq r := by
          unfold transverseSq
          positivity
        have hlt : transverseSq r < A - L :=
          (nullLower_lt_iff T u v (transverseSq r)).mpr
            ⟨hc.2.2.2.1, hc.2.2.2.2⟩
        have hLA : L < A := by linarith
        simpa [nullUVRegion, L, A] using
          (show 0 < u ∧ 0 < v ∧ v < a / Real.sqrt 2 ∧ L < A from
            ⟨hc.1, hc.2.1, hc.2.2.1, hLA⟩)
    simp_rw [hpoint]
    by_cases huv : (![u, v] : Plane) ∈ nullUVRegion T a
    · simp only [huv, if_true]
      have huv' : 0 < u ∧ 0 < v ∧ v < a / Real.sqrt 2 ∧ L < A := by
        simpa [nullUVRegion, L, A] using huv
      have hLA : L ≤ A := le_of_lt huv'.2.2.2
      rw [integral_indicator (by
        apply isOpen_lt ?_ continuous_const |>.measurableSet
        unfold transverseSq
        fun_prop)]
      change (∫ p in {p : Plane | ∑ i : Fin 2, p i ^ 2 < A - L},
        f (A - ∑ i : Fin 2, p i ^ 2)) = _
      rw [integral_plane_sqBall_shift L A hLA f hf]
      rw [Set.indicator_of_mem huv]
      simp [L, A]
    · simp only [huv, if_false, integral_zero]
      rw [Set.indicator_of_not_mem huv]

/-- The remaining null-coordinate domain is an honest rectangle.  This form
is convenient for the two Fubini interchanges used to expose the proper-time
square as the outer coordinate. -/
private theorem integral_indicator_swap (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (lo hi : ℝ × ℝ) (hbox : S ⊆ Icc lo hi)
    (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    (∫ x : ℝ, ∫ y : ℝ, S.indicator g (x, y)) =
      ∫ y : ℝ, ∫ x : ℝ, S.indicator g (x, y) := by
  have hiOn : IntegrableOn g S := hg.integrableOn_Icc.mono_set hbox
  exact integral_integral_swap ((integrable_indicator_iff hS).mpr hiOn)

private def nullUpper (T σ v : ℝ) : ℝ :=
  (T ^ 2 + σ) / (Real.sqrt 2 * T) - v

private def nullULower (σ v : ℝ) : ℝ := σ / (2 * v)

private def nullUSRegion (T v : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc (0 : ℝ) (T / Real.sqrt 2) ∧
    p.2 ∈ Ioc (nullLower T p.1 v) (2 * p.1 * v)}

private def nullVSRegion (T a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc (0 : ℝ) (a / Real.sqrt 2) ∧
    p.2 ∈ Ioc (0 : ℝ) (Real.sqrt 2 * T * p.1)}

private theorem measurableSet_nullVSRegion (T a : ℝ) :
    MeasurableSet (nullVSRegion T a) := by
  have hV : MeasurableSet {p : ℝ × ℝ |
      0 < p.1 ∧ p.1 ≤ a / Real.sqrt 2} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isClosed_le continuous_fst continuous_const).measurableSet
  have hσ : MeasurableSet {p : ℝ × ℝ |
      0 < p.2 ∧ p.2 ≤ Real.sqrt 2 * T * p.1} :=
    (isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd (by fun_prop)).measurableSet
  simpa only [nullVSRegion, mem_Ioc] using hV.inter hσ

private theorem null_sigma_cut (T a : ℝ) :
    Real.sqrt 2 * T * (a / Real.sqrt 2) = a * T := by
  field_simp
  ring

private theorem nullVSRegion_subset_box (T a : ℝ) (ha : 0 < a) (haT : a < T) :
    nullVSRegion T a ⊆
      Icc ((0 : ℝ), (0 : ℝ)) (a / Real.sqrt 2, a * T) := by
  have hT : 0 < T := ha.trans haT
  intro p hp
  rcases hp with ⟨hv, hσ⟩
  have hσmax : p.2 ≤ a * T := calc
    p.2 ≤ Real.sqrt 2 * T * p.1 := hσ.2
    _ ≤ Real.sqrt 2 * T * (a / Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hv.2 (mul_nonneg sqrt_two_pos.le hT.le)
    _ = a * T := null_sigma_cut T a
  exact ⟨⟨hv.1.le, hσ.1.le⟩, hv.2, hσmax⟩

private theorem nullVSRegion_fibre_iff (T a σ v : ℝ)
    (ha : 0 < a) (haT : a < T) :
    (v, σ) ∈ nullVSRegion T a ↔
      σ ∈ Ioc (0 : ℝ) (a * T) ∧
        v ∈ Icc (σ / (Real.sqrt 2 * T)) (a / Real.sqrt 2) := by
  have hT : 0 < T := ha.trans haT
  have hden : 0 < Real.sqrt 2 * T := mul_pos sqrt_two_pos hT
  constructor
  · rintro ⟨hv, hσ⟩
    have hσmax : σ ≤ a * T := calc
      σ ≤ Real.sqrt 2 * T * v := hσ.2
      _ ≤ Real.sqrt 2 * T * (a / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left hv.2 hden.le
      _ = a * T := null_sigma_cut T a
    exact ⟨⟨hσ.1, hσmax⟩,
      (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hσ.2), hv.2⟩
  · rintro ⟨hσ, hlv, hvV⟩
    have hlpos : 0 < σ / (Real.sqrt 2 * T) := div_pos hσ.1 hden
    have hv0 : 0 < v := hlpos.trans_le hlv
    have hσv : σ ≤ Real.sqrt 2 * T * v := by
      simpa [mul_comm] using (div_le_iff₀ hden).mp hlv
    exact ⟨⟨hv0, hvV⟩, hσ.1, hσv⟩

private def nullCoordinateWidth (T σ v : ℝ) : ℝ :=
  nullUpper T σ v - nullULower σ v

private theorem measurable_nullCoordinateWidth (T : ℝ) :
    Measurable (fun p : ℝ × ℝ => nullCoordinateWidth T p.2 p.1) := by
  unfold nullCoordinateWidth nullUpper nullULower
  fun_prop

private theorem measurableSet_nullUSRegion (T v : ℝ) :
    MeasurableSet (nullUSRegion T v) := by
  have hL : Continuous (fun p : ℝ × ℝ => nullLower T p.1 v) := by
    unfold nullLower nullDefect
    fun_prop
  have hA : Continuous (fun p : ℝ × ℝ => 2 * p.1 * v) := by fun_prop
  have hU : MeasurableSet {p : ℝ × ℝ |
      0 < p.1 ∧ p.1 ≤ T / Real.sqrt 2} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isClosed_le continuous_fst continuous_const).measurableSet
  have hσ : MeasurableSet {p : ℝ × ℝ |
      nullLower T p.1 v < p.2 ∧ p.2 ≤ 2 * p.1 * v} :=
    (isOpen_lt hL continuous_snd).measurableSet.inter
      (isClosed_le continuous_snd hA).measurableSet
  simpa only [nullUSRegion, mem_Ioc] using hU.inter hσ

private theorem null_rectangle_product (T a : ℝ) :
    2 * (T / Real.sqrt 2) * (a / Real.sqrt 2) = a * T := by
  field_simp
  nlinarith [sqrt_two_sq]

private theorem null_sigma_max (T v : ℝ) :
    2 * (T / Real.sqrt 2) * v = Real.sqrt 2 * T * v := by
  calc
    2 * (T / Real.sqrt 2) * v = (2 / Real.sqrt 2) * T * v := by ring
    _ = _ := by rw [two_div_sqrt_two]

private theorem nullDefect_lt_iff_upper {T σ u v : ℝ} (hT : 0 < T) :
    nullDefect T u v < σ ↔ u < nullUpper T σ v := by
  have hden : 0 < Real.sqrt 2 * T := mul_pos sqrt_two_pos hT
  rw [nullUpper, lt_sub_iff_add_lt, lt_div_iff₀ hden]
  unfold nullDefect
  constructor <;> intro h <;> linarith

private theorem sigma_le_iff_uLower_le {σ u v : ℝ} (hv : 0 < v) :
    σ ≤ 2 * u * v ↔ nullULower σ v ≤ u := by
  unfold nullULower
  rw [div_le_iff₀ (mul_pos (by norm_num) hv)]
  ring_nf

private theorem nullUpper_le_timeBound {T σ v : ℝ} (hT : 0 < T)
    (hσ : σ ≤ Real.sqrt 2 * T * v) :
    nullUpper T σ v ≤ T / Real.sqrt 2 := by
  have hden : 0 < Real.sqrt 2 * T := mul_pos sqrt_two_pos hT
  have hbase : (T / Real.sqrt 2 + v) * (Real.sqrt 2 * T) =
      T ^ 2 + Real.sqrt 2 * T * v := by
    field_simp
    nlinarith [sqrt_two_sq]
  unfold nullUpper
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hden).mpr
  rw [hbase]
  linarith

private theorem nullLower_le_on_rectangle (T a u v : ℝ)
    (haT : a < T)
    (hu : u ∈ Ioc (0 : ℝ) (T / Real.sqrt 2))
    (hv : v ∈ Ioc (0 : ℝ) (a / Real.sqrt 2)) :
    nullLower T u v ≤ 2 * u * v := by
  have hvT : v ≤ T / Real.sqrt 2 :=
    hv.2.trans (div_le_div_of_nonneg_right haT.le sqrt_two_pos.le)
  have hufac : 0 ≤ T - Real.sqrt 2 * u := by
    have hm := (le_div_iff₀ sqrt_two_pos).mp hu.2
    linarith
  have hvfac : 0 ≤ T - Real.sqrt 2 * v := by
    have hm := (le_div_iff₀ sqrt_two_pos).mp hvT
    linarith
  have hgap : 0 ≤ 2 * u * v - nullDefect T u v := by
    rw [null_gap_factor]
    exact mul_nonneg hufac hvfac
  apply max_le
  · exact mul_nonneg (mul_nonneg (by norm_num) hu.1.le) hv.1.le
  · linarith

private theorem nullUSRegion_subset_box (T a v : ℝ)
    (ha : 0 < a) (haT : a < T)
    (hv : v ∈ Ioc (0 : ℝ) (a / Real.sqrt 2)) :
    nullUSRegion T v ⊆
      Icc ((0 : ℝ), (0 : ℝ)) (T / Real.sqrt 2, a * T) := by
  have hT : 0 < T := ha.trans haT
  have hU0 : 0 ≤ T / Real.sqrt 2 := div_nonneg hT.le sqrt_two_pos.le
  intro p hp
  rcases hp with ⟨hu, hσ⟩
  have hσ0 : 0 ≤ p.2 :=
    (le_max_left (0 : ℝ) (nullDefect T p.1 v)).trans hσ.1.le
  have huv : p.1 * v ≤ (T / Real.sqrt 2) * (a / Real.sqrt 2) :=
    mul_le_mul hu.2 hv.2 hv.1.le hU0
  have hσmax : p.2 ≤ a * T := calc
    p.2 ≤ 2 * p.1 * v := hσ.2
    _ = 2 * (p.1 * v) := by ring
    _ ≤ 2 * ((T / Real.sqrt 2) * (a / Real.sqrt 2)) :=
      mul_le_mul_of_nonneg_left huv (show (0 : ℝ) ≤ 2 by norm_num)
    _ = 2 * (T / Real.sqrt 2) * (a / Real.sqrt 2) := by ring
    _ = a * T := null_rectangle_product T a
  exact ⟨⟨hu.1.le, hσ0⟩, hu.2, hσmax⟩

private theorem nullULower_le_upper {T σ v : ℝ}
    (hT : 0 < T) (hv : 0 < v) (hvT : v ≤ T / Real.sqrt 2)
    (hσ : σ ≤ Real.sqrt 2 * T * v) :
    nullULower σ v ≤ nullUpper T σ v := by
  have hfac1 : 0 ≤ T - Real.sqrt 2 * v := by
    have hm := (le_div_iff₀ sqrt_two_pos).mp hvT
    linarith
  have hfac2 : 0 ≤ T - Real.sqrt 2 * σ / (2 * v) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (mul_pos (by norm_num) hv)).mpr
    have hsσ : Real.sqrt 2 * σ ≤ 2 * T * v := by
      calc
        Real.sqrt 2 * σ ≤ Real.sqrt 2 * (Real.sqrt 2 * T * v) :=
          mul_le_mul_of_nonneg_left hσ sqrt_two_pos.le
        _ = 2 * T * v := by rw [show Real.sqrt 2 * (Real.sqrt 2 * T * v) =
          (Real.sqrt 2) ^ 2 * T * v by ring, sqrt_two_sq]
    linarith
  have hid : T ^ 2 + σ -
      (nullULower σ v + v) * (Real.sqrt 2 * T) =
      (T - Real.sqrt 2 * v) *
        (T - Real.sqrt 2 * σ / (2 * v)) := by
    unfold nullULower
    field_simp
    ring_nf
    rw [sqrt_two_sq]
  have hmain : (nullULower σ v + v) * (Real.sqrt 2 * T) ≤ T ^ 2 + σ := by
    nlinarith [hid, mul_nonneg hfac1 hfac2]
  unfold nullUpper
  rw [le_sub_iff_add_le]
  exact (le_div_iff₀ (mul_pos sqrt_two_pos hT)).mpr hmain

private theorem nullUSRegion_fibre_iff (T v σ u : ℝ)
    (hT : 0 < T) (hv : 0 < v) :
    (u, σ) ∈ nullUSRegion T v ↔
      σ ∈ Ioc (0 : ℝ) (Real.sqrt 2 * T * v) ∧
        u ∈ Ico (nullULower σ v) (nullUpper T σ v) := by
  constructor
  · rintro ⟨hu, hσ⟩
    have hσ0 : 0 < σ :=
      (le_max_left (0 : ℝ) (nullDefect T u v)).trans_lt hσ.1
    have hσmax : σ ≤ Real.sqrt 2 * T * v := by
      calc
        σ ≤ 2 * u * v := hσ.2
        _ ≤ 2 * (T / Real.sqrt 2) * v :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2 (by norm_num)) hv.le
        _ = _ := null_sigma_max T v
    exact ⟨⟨hσ0, hσmax⟩,
      (sigma_le_iff_uLower_le hv).mp hσ.2,
      (nullDefect_lt_iff_upper hT).mp
        ((le_max_right (0 : ℝ) (nullDefect T u v)).trans_lt hσ.1)⟩
  · rintro ⟨hσ, hlu, huu⟩
    have hu0 : 0 < u := lt_of_lt_of_le
      (div_pos hσ.1 (mul_pos (by norm_num) hv)) hlu
    have huU : u ≤ T / Real.sqrt 2 :=
      (le_of_lt huu).trans (nullUpper_le_timeBound hT hσ.2)
    have hA : σ ≤ 2 * u * v := (sigma_le_iff_uLower_le hv).mpr hlu
    have hD : nullDefect T u v < σ :=
      (nullDefect_lt_iff_upper hT).mpr huu
    exact ⟨⟨hu0, huU⟩, (max_lt_iff.mpr ⟨hσ.1, hD⟩), hA⟩

private theorem nullCoordinateWidth_bounds (T a v σ : ℝ)
    (ha : 0 < a) (haT : a < T) (hmem : (v, σ) ∈ nullVSRegion T a) :
    0 ≤ nullCoordinateWidth T σ v ∧
      nullCoordinateWidth T σ v ≤ T / Real.sqrt 2 := by
  rcases hmem with ⟨hv, hσ⟩
  have hT : 0 < T := ha.trans haT
  have hvT : v ≤ T / Real.sqrt 2 :=
    hv.2.trans (div_le_div_of_nonneg_right haT.le sqrt_two_pos.le)
  have hlu : nullULower σ v ≤ nullUpper T σ v :=
    nullULower_le_upper hT hv.1 hvT hσ.2
  have hl0 : 0 ≤ nullULower σ v :=
    div_nonneg hσ.1.le (mul_nonneg (by norm_num) hv.1.le)
  have huU : nullUpper T σ v ≤ T / Real.sqrt 2 :=
    nullUpper_le_timeBound hT hσ.2
  unfold nullCoordinateWidth
  constructor <;> linarith

private theorem integrableOn_nullCoordinateWidth (T a : ℝ)
    (ha : 0 < a) (haT : a < T) (f : ℝ → ℝ) (hf : Continuous f) :
    IntegrableOn (fun p : ℝ × ℝ =>
      nullCoordinateWidth T p.2 p.1 * (Real.pi * f p.2))
      (nullVSRegion T a) := by
  let S := nullVSRegion T a
  let g := fun p : ℝ × ℝ =>
    nullCoordinateWidth T p.2 p.1 * (Real.pi * f p.2)
  have hT : 0 < T := ha.trans haT
  have hU : 0 ≤ T / Real.sqrt 2 := div_nonneg hT.le sqrt_two_pos.le
  have hS : MeasurableSet S := measurableSet_nullVSRegion T a
  have hbox := nullVSRegion_subset_box T a ha haT
  have hfinite : (volume : Measure (ℝ × ℝ)) S ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono hbox).trans_lt
      (isCompact_Icc.measure_lt_top :
        (volume : Measure (ℝ × ℝ))
          (Icc ((0 : ℝ), (0 : ℝ)) (a / Real.sqrt 2, a * T)) < ⊤)
  have hg : Measurable g := by
    dsimp [g]
    exact (measurable_nullCoordinateWidth T).mul
      (measurable_const.mul (hf.measurable.comp measurable_snd))
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm.continuousOn
  apply Measure.integrableOn_of_bounded hfinite hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hS] with p hp
  have hw := nullCoordinateWidth_bounds T a p.1 p.2 ha haT hp
  have hwabs : ‖nullCoordinateWidth T p.2 p.1‖ ≤ T / Real.sqrt 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact hw.2
  have hσbox : p.2 ∈ Icc (0 : ℝ) (a * T) := by
    exact ⟨hp.2.1.le, (nullVSRegion_subset_box T a ha haT hp).2.2⟩
  have hfC : ‖f p.2‖ ≤ C :=
    hC (mem_image_of_mem (fun x => ‖f x‖) hσbox)
  have hpi : ‖Real.pi * f p.2‖ ≤ |Real.pi| * C := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hfC (abs_nonneg _)
  change ‖nullCoordinateWidth T p.2 p.1 * (Real.pi * f p.2)‖ ≤
    T / Real.sqrt 2 * (|Real.pi| * C)
  rw [norm_mul]
  exact mul_le_mul hwabs hpi (norm_nonneg _) hU

private theorem integral_v_sigma_swap (T a : ℝ)
    (ha : 0 < a) (haT : a < T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ v in (0 : ℝ)..a / Real.sqrt 2,
      ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
        nullCoordinateWidth T σ v * (Real.pi * f σ)) =
      ∫ σ in (0 : ℝ)..a * T,
        ∫ v in σ / (Real.sqrt 2 * T)..a / Real.sqrt 2,
          nullCoordinateWidth T σ v * (Real.pi * f σ) := by
  let V := a / Real.sqrt 2
  let S := nullVSRegion T a
  let g := fun p : ℝ × ℝ =>
    nullCoordinateWidth T p.2 p.1 * (Real.pi * f p.2)
  have hT : 0 < T := ha.trans haT
  have hV : 0 ≤ V := div_nonneg ha.le sqrt_two_pos.le
  have haT0 : 0 ≤ a * T := mul_nonneg ha.le hT.le
  have hS : MeasurableSet S := measurableSet_nullVSRegion T a
  have hi : Integrable (S.indicator g) :=
    (integrable_indicator_iff hS).mpr
      (integrableOn_nullCoordinateWidth T a ha haT f hf)
  simp only [Measure.volume_eq_prod] at hi
  change Integrable (Function.uncurry
    (fun v σ : ℝ => S.indicator g (v, σ))) (volume.prod volume) at hi
  have hswap := integral_integral_swap hi
  have hleftInner (v : ℝ) :
      (∫ σ : ℝ, S.indicator g (v, σ)) =
        (Ioc (0 : ℝ) V).indicator
          (fun v => ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
            nullCoordinateWidth T σ v * (Real.pi * f σ)) v := by
    by_cases hv : v ∈ Ioc (0 : ℝ) V
    · have hmax : 0 ≤ Real.sqrt 2 * T * v :=
        mul_nonneg (mul_nonneg sqrt_two_pos.le hT.le) hv.1.le
      have he (σ : ℝ) : S.indicator g (v, σ) =
          (Ioc (0 : ℝ) (Real.sqrt 2 * T * v)).indicator
            (fun σ => nullCoordinateWidth T σ v * (Real.pi * f σ)) σ := by
        have hp : (v, σ) ∈ S ↔
            σ ∈ Ioc (0 : ℝ) (Real.sqrt 2 * T * v) := by
          change (v ∈ Ioc (0 : ℝ) V ∧
            σ ∈ Ioc (0 : ℝ) (Real.sqrt 2 * T * v)) ↔ _
          exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
        by_cases hσ : σ ∈ Ioc (0 : ℝ) (Real.sqrt 2 * T * v)
        · rw [Set.indicator_of_mem (hp.mpr hσ), Set.indicator_of_mem hσ]
        · rw [Set.indicator_of_not_mem (fun h => hσ (hp.mp h)),
            Set.indicator_of_not_mem hσ]
      simp_rw [he]
      rw [integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hmax,
        Set.indicator_of_mem hv]
    · have he (σ : ℝ) : S.indicator g (v, σ) = 0 := by
        apply Set.indicator_of_not_mem
        intro hp
        exact hv hp.1
      simp_rw [he]
      rw [integral_zero, Set.indicator_of_not_mem hv]
  have hleft :
      (∫ v : ℝ, ∫ σ : ℝ, S.indicator g (v, σ)) =
        ∫ v in (0 : ℝ)..V,
          ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
            nullCoordinateWidth T σ v * (Real.pi * f σ) := by
    simp_rw [hleftInner]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hV]
  have hrightInner (σ : ℝ) :
      (∫ v : ℝ, S.indicator g (v, σ)) =
        (Ioc (0 : ℝ) (a * T)).indicator
          (fun σ => ∫ v in σ / (Real.sqrt 2 * T)..V,
            nullCoordinateWidth T σ v * (Real.pi * f σ)) σ := by
    by_cases hσ : σ ∈ Ioc (0 : ℝ) (a * T)
    · have hden : 0 < Real.sqrt 2 * T := mul_pos sqrt_two_pos hT
      have hlV : σ / (Real.sqrt 2 * T) ≤ V := by
        apply (div_le_iff₀ hden).mpr
        have hcut : V * (Real.sqrt 2 * T) = a * T := by
          dsimp [V]
          field_simp
          ring
        rw [hcut]
        exact hσ.2
      have he (v : ℝ) : S.indicator g (v, σ) =
          (Icc (σ / (Real.sqrt 2 * T)) V).indicator
            (fun v => nullCoordinateWidth T σ v * (Real.pi * f σ)) v := by
        have hp : (v, σ) ∈ S ↔
            v ∈ Icc (σ / (Real.sqrt 2 * T)) V := by
          simpa [S, hσ] using nullVSRegion_fibre_iff T a σ v ha haT
        by_cases hv : v ∈ Icc (σ / (Real.sqrt 2 * T)) V
        · rw [Set.indicator_of_mem (hp.mpr hv), Set.indicator_of_mem hv]
        · rw [Set.indicator_of_not_mem (fun h => hv (hp.mp h)),
            Set.indicator_of_not_mem hv]
      simp_rw [he]
      rw [integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hlV,
        Set.indicator_of_mem hσ]
    · have he (v : ℝ) : S.indicator g (v, σ) = 0 := by
        apply Set.indicator_of_not_mem
        intro hp
        exact hσ (nullVSRegion_fibre_iff T a σ v ha haT |>.mp hp).1
      simp_rw [he]
      rw [integral_zero, Set.indicator_of_not_mem hσ]
  have hright :
      (∫ σ : ℝ, ∫ v : ℝ, S.indicator g (v, σ)) =
        ∫ σ in (0 : ℝ)..a * T,
          ∫ v in σ / (Real.sqrt 2 * T)..V,
            nullCoordinateWidth T σ v * (Real.pi * f σ) := by
    simp_rw [hrightInner]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le haT0]
  change (∫ v in (0 : ℝ)..V,
      ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
        nullCoordinateWidth T σ v * (Real.pi * f σ)) = _
  calc
    _ = ∫ v : ℝ, ∫ σ : ℝ, S.indicator g (v, σ) := hleft.symm
    _ = ∫ σ : ℝ, ∫ v : ℝ, S.indicator g (v, σ) := hswap
    _ = _ := hright

private def nullWidthPrimitive (T σ v : ℝ) : ℝ :=
  ((T ^ 2 + σ) / (Real.sqrt 2 * T)) * v - v ^ 2 / 2 -
    (σ / 2) * Real.log v

private theorem hasDerivAt_nullWidthPrimitive (T σ v : ℝ)
    (hv : v ≠ 0) :
    HasDerivAt (nullWidthPrimitive T σ)
      (nullCoordinateWidth T σ v) v := by
  have hlin := (hasDerivAt_id v).const_mul
    ((T ^ 2 + σ) / (Real.sqrt 2 * T))
  have hsq := ((hasDerivAt_id v).pow 2).div_const 2
  have hlog := (Real.hasDerivAt_log hv).const_mul (σ / 2)
  convert (hlin.sub hsq).sub hlog using 1
  all_goals
    simp [nullWidthPrimitive, nullCoordinateWidth, nullUpper, nullULower, id_eq]
    field_simp

private theorem continuousAt_nullCoordinateWidth (T σ v : ℝ) (hv : v ≠ 0) :
    ContinuousAt (nullCoordinateWidth T σ) v := by
  have hlower : ContinuousAt (nullULower σ) v := by
    unfold nullULower
    exact continuousAt_const.div (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero (by norm_num) hv)
  have hupper : ContinuousAt (nullUpper T σ) v := by
    unfold nullUpper
    fun_prop
  exact hupper.sub hlower

private theorem nullWidthIntegral_eq_core (T a σ : ℝ)
    (ha : 0 < a) (haT : a < T) (hσ : 0 < σ) (hσmax : σ ≤ a * T) :
    Real.pi * (∫ v in σ / (Real.sqrt 2 * T)..a / Real.sqrt 2,
      nullCoordinateWidth T σ v) = nullCapWeightCore T a σ := by
  have hT : 0 < T := ha.trans haT
  have hden : 0 < Real.sqrt 2 * T := mul_pos sqrt_two_pos hT
  let L := σ / (Real.sqrt 2 * T)
  let V := a / Real.sqrt 2
  have hL : 0 < L := div_pos hσ hden
  have hV : 0 < V := div_pos ha sqrt_two_pos
  have hLV : L ≤ V := by
    apply (div_le_div_iff₀ hden sqrt_two_pos).mpr
    have hs2 := sqrt_two_sq
    nlinarith [hσmax]
  have hint : IntervalIntegrable (nullCoordinateWidth T σ) volume L V := by
    apply (continuousOn_of_forall_continuousAt fun v hv => ?_).intervalIntegrable
    have hvIcc : v ∈ Icc L V := by simpa [uIcc_of_le hLV] using hv
    exact continuousAt_nullCoordinateWidth T σ v
      (ne_of_gt (hL.trans_le hvIcc.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_nullWidthPrimitive T σ v (by
      have hvIcc : v ∈ Icc L V := by simpa [uIcc_of_le hLV] using hv
      exact ne_of_gt (hL.trans_le hvIcc.1))) hint]
  have hlog : Real.log V - Real.log L = Real.log (a * T / σ) := by
    calc
      Real.log V - Real.log L = Real.log (V / L) :=
        (Real.log_div hV.ne' hL.ne').symm
      _ = Real.log (a * T / σ) := by
        congr 1
        dsimp [V, L]
        field_simp
        ring
  rw [show nullWidthPrimitive T σ V - nullWidthPrimitive T σ L =
      ((T ^ 2 + σ) / (Real.sqrt 2 * T)) * V - V ^ 2 / 2 -
        (((T ^ 2 + σ) / (Real.sqrt 2 * T)) * L - L ^ 2 / 2) -
        (σ / 2) * (Real.log V - Real.log L) by
      unfold nullWidthPrimitive
      ring,
    hlog,
    nullCapWeightCore_eq_log_ratio T a σ hσ (mul_pos ha hT)]
  dsimp [V, L]
  field_simp
  ring_nf
  have hs4 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 4 := by rw [sqrt_two_sq]; norm_num
  have hs6 : Real.sqrt 2 ^ 6 = 8 := by
    calc
      Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring
      _ = 8 := by rw [sqrt_two_sq]; norm_num
  rw [hs4, hs6]
  ring

private theorem nullWidthIntegral_zero (T a : ℝ)
    (ha : 0 < a) (haT : a < T) :
    Real.pi * (∫ v in (0 : ℝ)..a / Real.sqrt 2,
      nullCoordinateWidth T 0 v) = nullCapWeightCore T a 0 := by
  have hT : 0 < T := ha.trans haT
  let P := fun v : ℝ => (T / Real.sqrt 2) * v - v ^ 2 / 2
  have hd (v : ℝ) : HasDerivAt P (T / Real.sqrt 2 - v) v := by
    dsimp [P]
    convert ((hasDerivAt_id v).const_mul (T / Real.sqrt 2)).sub
      (((hasDerivAt_id v).pow 2).div_const 2) using 1
    all_goals
      simp only [id_eq]
      ring
  have he (v : ℝ) : nullCoordinateWidth T 0 v = T / Real.sqrt 2 - v := by
    unfold nullCoordinateWidth nullUpper nullULower
    field_simp
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hd v) ((by fun_prop : Continuous (fun v : ℝ => T / Real.sqrt 2 - v)).intervalIntegrable 0 (a / Real.sqrt 2))]
  dsimp [P, nullCapWeightCore]
  field_simp
  ring_nf

private theorem continuous_intervalIntegral_bounds (f : ℝ → ℝ) (hf : Continuous f)
    (l r : (ℝ × ℝ) → ℝ) (hl : Continuous l) (hr : Continuous r) :
    Continuous (fun p => ∫ σ in l p..r p, f σ) := by
  let F := fun x : ℝ => ∫ σ in (0 : ℝ)..x, f σ
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hf.integral_hasStrictDerivAt (0 : ℝ) x).continuousAt
  have he : (fun p => ∫ σ in l p..r p, f σ) =
      fun p => F (r p) - F (l p) := by
    funext p
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (0 : ℝ) (l p))
      (hf.intervalIntegrable (μ := volume) (l p) (r p))
    dsimp [F]
    linarith
  rw [he]
  exact (hF.comp hr).sub (hF.comp hl)

private theorem continuous_nullCoordinate_inner (T : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    Continuous (Function.uncurry (fun u v =>
      Real.pi * ∫ σ in nullLower T u v..2 * u * v, f σ)) := by
  have hL : Continuous (fun p : ℝ × ℝ => nullLower T p.1 p.2) := by
    unfold nullLower nullDefect
    fun_prop
  have hA : Continuous (fun p : ℝ × ℝ => 2 * p.1 * p.2) := by fun_prop
  exact continuous_const.mul (continuous_intervalIntegral_bounds f hf _ _ hL hA)

private theorem interval_integral_swap_rectangle (U V : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F u v) =
      ∫ v in (0 : ℝ)..V, ∫ u in (0 : ℝ)..U, F u v := by
  have hi0 : IntegrableOn (Function.uncurry F)
      (Icc (0 : ℝ) U ×ˢ Icc (0 : ℝ) V) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : IntegrableOn (Function.uncurry F)
      (Ioc (0 : ℝ) U ×ˢ Ioc (0 : ℝ) V) :=
    hi0.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [Measure.volume_eq_prod ℝ ℝ, IntegrableOn, ← Measure.prod_restrict] at hi
  have hswap := integral_integral_swap hi
  simpa only [← intervalIntegral.integral_of_le hU,
    ← intervalIntegral.integral_of_le hV] using hswap

private theorem integral_u_sigma_swap (T a v : ℝ)
    (ha : 0 < a) (haT : a < T)
    (hv : v ∈ Ioc (0 : ℝ) (a / Real.sqrt 2))
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u in (0 : ℝ)..T / Real.sqrt 2,
      ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ) =
      ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
        ∫ _u in nullULower σ v..nullUpper T σ v, Real.pi * f σ := by
  let U := T / Real.sqrt 2
  let S := nullUSRegion T v
  let g := fun p : ℝ × ℝ => Real.pi * f p.2
  have hT : 0 < T := ha.trans haT
  have hU : 0 ≤ U := div_nonneg hT.le sqrt_two_pos.le
  have hvT : v < U := by
    exact hv.2.trans_lt (div_lt_div_of_pos_right haT sqrt_two_pos)
  have hS : MeasurableSet S := measurableSet_nullUSRegion T v
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hswap := integral_indicator_swap S hS ((0 : ℝ), (0 : ℝ))
    (U, a * T) (nullUSRegion_subset_box T a v ha haT hv) g hg
  have hleftInner (u : ℝ) :
      (∫ σ : ℝ, S.indicator g (u, σ)) =
        (Ioc (0 : ℝ) U).indicator
          (fun u => ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ) u := by
    by_cases hu : u ∈ Ioc (0 : ℝ) U
    · have hLA := nullLower_le_on_rectangle T a u v haT hu hv
      have he (σ : ℝ) : S.indicator g (u, σ) =
          (Ioc (nullLower T u v) (2 * u * v)).indicator
            (fun σ => Real.pi * f σ) σ := by
        have hp : (u, σ) ∈ S ↔
            σ ∈ Ioc (nullLower T u v) (2 * u * v) := by
          change (u ∈ Ioc (0 : ℝ) U ∧
            σ ∈ Ioc (nullLower T u v) (2 * u * v)) ↔ _
          exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
        by_cases hσ : σ ∈ Ioc (nullLower T u v) (2 * u * v)
        · rw [Set.indicator_of_mem (hp.mpr hσ), Set.indicator_of_mem hσ]
        · rw [Set.indicator_of_not_mem (fun h => hσ (hp.mp h)),
            Set.indicator_of_not_mem hσ]
      simp_rw [he]
      rw [integral_indicator measurableSet_Ioc,
        Set.indicator_of_mem hu,
        ← intervalIntegral.integral_of_le hLA]
    · have he (σ : ℝ) : S.indicator g (u, σ) = 0 := by
        apply Set.indicator_of_not_mem
        intro hp
        exact hu hp.1
      simp_rw [he]
      rw [integral_zero, Set.indicator_of_not_mem hu]
  have hleft :
      (∫ u : ℝ, ∫ σ : ℝ, S.indicator g (u, σ)) =
        ∫ u in (0 : ℝ)..U,
          ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ := by
    simp_rw [hleftInner]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hU]
  have hrightInner (σ : ℝ) :
      (∫ u : ℝ, S.indicator g (u, σ)) =
        (Ioc (0 : ℝ) (Real.sqrt 2 * T * v)).indicator
          (fun σ => ∫ u in nullULower σ v..nullUpper T σ v,
            Real.pi * f σ) σ := by
    by_cases hσ : σ ∈ Ioc (0 : ℝ) (Real.sqrt 2 * T * v)
    · have hlu := nullULower_le_upper hT hv.1 hvT.le hσ.2
      have he (u : ℝ) : S.indicator g (u, σ) =
          (Ico (nullULower σ v) (nullUpper T σ v)).indicator
            (fun _ => Real.pi * f σ) u := by
        have hp : (u, σ) ∈ S ↔
            u ∈ Ico (nullULower σ v) (nullUpper T σ v) := by
          simpa [hσ] using nullUSRegion_fibre_iff T v σ u hT hv.1
        by_cases hu : u ∈ Ico (nullULower σ v) (nullUpper T σ v)
        · rw [Set.indicator_of_mem (hp.mpr hu), Set.indicator_of_mem hu]
        · rw [Set.indicator_of_not_mem (fun h => hu (hp.mp h)),
            Set.indicator_of_not_mem hu]
      simp_rw [he]
      rw [integral_indicator measurableSet_Ico,
        integral_Ico_eq_integral_Ioo,
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hlu,
        Set.indicator_of_mem hσ]
    · have he (u : ℝ) : S.indicator g (u, σ) = 0 := by
        apply Set.indicator_of_not_mem
        intro hp
        exact hσ (nullUSRegion_fibre_iff T v σ u hT hv.1 |>.mp hp).1
      simp_rw [he]
      rw [integral_zero, Set.indicator_of_not_mem hσ]
  have hmax : 0 ≤ Real.sqrt 2 * T * v :=
    mul_nonneg (mul_nonneg sqrt_two_pos.le hT.le) hv.1.le
  have hright :
      (∫ σ : ℝ, ∫ u : ℝ, S.indicator g (u, σ)) =
        ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
          ∫ u in nullULower σ v..nullUpper T σ v, Real.pi * f σ := by
    simp_rw [hrightInner]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hmax]
  change (∫ u in (0 : ℝ)..U,
      ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ) = _
  calc
    _ = ∫ u : ℝ, ∫ σ : ℝ, S.indicator g (u, σ) := hleft.symm
    _ = ∫ σ : ℝ, ∫ u : ℝ, S.indicator g (u, σ) := hswap
    _ = _ := hright

private theorem integral_u_sigma_swap_Icc (T a v : ℝ)
    (ha : 0 < a) (haT : a < T)
    (hv : v ∈ Icc (0 : ℝ) (a / Real.sqrt 2))
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ u in (0 : ℝ)..T / Real.sqrt 2,
      ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ) =
      ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
        ∫ _u in nullULower σ v..nullUpper T σ v, Real.pi * f σ := by
  rcases eq_or_lt_of_le hv.1 with hv0 | hv0
  · rw [← hv0]
    have hT : 0 < T := ha.trans haT
    have hU : 0 ≤ T / Real.sqrt 2 := div_nonneg hT.le sqrt_two_pos.le
    have hzero (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) (T / Real.sqrt 2)) :
        nullLower T u 0 = 0 := by
      have hucc : u ∈ Icc (0 : ℝ) (T / Real.sqrt 2) := by
        simpa [uIcc_of_le hU] using hu
      have humul : u * Real.sqrt 2 ≤ T :=
        (le_div_iff₀ sqrt_two_pos).mp hucc.2
      have hm := mul_le_mul_of_nonneg_left humul hT.le
      have hD : nullDefect T u 0 ≤ 0 := by
        unfold nullDefect
        nlinarith
      unfold nullLower
      rw [max_eq_left hD]
    rw [mul_zero, intervalIntegral.integral_same]
    calc
      (∫ u in (0 : ℝ)..T / Real.sqrt 2,
          ∫ σ in (nullLower T u 0)..(2 * u * 0), Real.pi * f σ) =
          ∫ _u in (0 : ℝ)..T / Real.sqrt 2, 0 := by
            apply intervalIntegral.integral_congr
            intro u hu
            change (∫ σ in (nullLower T u 0)..(2 * u * 0),
              Real.pi * f σ) = 0
            rw [hzero u hu, mul_zero, intervalIntegral.integral_same]
      _ = 0 := intervalIntegral.integral_zero
  · exact integral_u_sigma_swap T a v ha haT ⟨hv0, hv.2⟩ f hf

/-- The remaining null-coordinate domain is an honest rectangle.  This form
is convenient for the two Fubini interchanges used to expose the proper-time
square as the outer coordinate. -/
theorem integral_nullCoordinates_eq_rectangle (T a : ℝ) (ha : 0 < a) (haT : a < T)
    (f : ℝ → ℝ) :
    (∫ u : ℝ, ∫ v : ℝ,
      (nullUVRegion T a).indicator
        (fun p => Real.pi * ∫ σ in nullLower T (p 0) (p 1)..2 * p 0 * p 1,
          f σ) ![u, v]) =
      ∫ u in (0 : ℝ)..T / Real.sqrt 2,
        ∫ v in (0 : ℝ)..a / Real.sqrt 2,
          Real.pi * ∫ σ in nullLower T u v..2 * u * v, f σ := by
  rw [nullUVRegion_eq_rectangle T a ha haT]
  let U := T / Real.sqrt 2
  let V := a / Real.sqrt 2
  let H := fun u v : ℝ => Real.pi * ∫ σ in nullLower T u v..2 * u * v, f σ
  have he (u v : ℝ) :
      ({p : Plane | p 0 ∈ Ioo (0 : ℝ) U ∧ p 1 ∈ Ioo (0 : ℝ) V}).indicator
          (fun p => Real.pi * ∫ σ in nullLower T (p 0) (p 1)..2 * p 0 * p 1,
            f σ) ![u, v] =
        (Ioo (0 : ℝ) U).indicator
          (fun u => (Ioo (0 : ℝ) V).indicator (H u) v) u := by
    have hp : (![u, v] : Plane) ∈
        {p : Plane | p 0 ∈ Ioo (0 : ℝ) U ∧ p 1 ∈ Ioo (0 : ℝ) V} ↔
          u ∈ Ioo (0 : ℝ) U ∧ v ∈ Ioo (0 : ℝ) V := by simp
    by_cases hu : u ∈ Ioo (0 : ℝ) U
    · by_cases hv : v ∈ Ioo (0 : ℝ) V
      · rw [Set.indicator_of_mem (hp.mpr ⟨hu, hv⟩),
          Set.indicator_of_mem hu, Set.indicator_of_mem hv]
        rfl
      · rw [Set.indicator_of_not_mem (fun h => hv (hp.mp h).2),
          Set.indicator_of_mem hu, Set.indicator_of_not_mem hv]
    · rw [Set.indicator_of_not_mem (fun h => hu (hp.mp h).1),
        Set.indicator_of_not_mem hu]
  change (∫ u : ℝ, ∫ v : ℝ,
      ({p : Plane | p 0 ∈ Ioo (0 : ℝ) U ∧ p 1 ∈ Ioo (0 : ℝ) V}).indicator
        (fun p => Real.pi * ∫ σ in nullLower T (p 0) (p 1)..2 * p 0 * p 1,
          f σ) ![u, v]) =
    ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, H u v
  simp_rw [he]
  have ho (u : ℝ) :
      (∫ v : ℝ, (Ioo (0 : ℝ) U).indicator
        (fun u => (Ioo (0 : ℝ) V).indicator (H u) v) u) =
      (Ioo (0 : ℝ) U).indicator
        (fun u => ∫ v : ℝ, (Ioo (0 : ℝ) V).indicator (H u) v) u := by
    by_cases hu : u ∈ Ioo (0 : ℝ) U <;> simp [Set.indicator, hu]
  simp_rw [ho]
  rw [integral_indicator measurableSet_Ioo]
  have hi (u : ℝ) :
      (∫ v : ℝ, (Ioo (0 : ℝ) V).indicator (H u) v) =
        ∫ v in (0 : ℝ)..V, H u v := by
    rw [integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show 0 ≤ V from
        div_nonneg ha.le (Real.sqrt_nonneg _))]
  simp_rw [hi]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show 0 ≤ U from
      div_nonneg (ha.trans haT).le (Real.sqrt_nonneg _))]

/-- After the two justified Fubini interchanges, the transverse-null volume is
an elementary interval length.  No formula for that length is assumed. -/
theorem integral_nullCap_eq_sigma_v (T a : ℝ) (ha : 0 < a) (haT : a < T)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in nullCapRegion T a, f (intervalSq x 0)) =
      ∫ v in (0 : ℝ)..a / Real.sqrt 2,
        ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
          (nullUpper T σ v - nullULower σ v) * (Real.pi * f σ) := by
  let U := T / Real.sqrt 2
  let V := a / Real.sqrt 2
  let H := fun u v : ℝ =>
    Real.pi * ∫ σ in nullLower T u v..2 * u * v, f σ
  have hT : 0 < T := ha.trans haT
  have hU : 0 ≤ U := div_nonneg hT.le sqrt_two_pos.le
  have hV : 0 ≤ V := div_nonneg ha.le sqrt_two_pos.le
  rw [integral_nullCap_eq_nullCoordinates T a ha haT f hf,
    integral_nullCoordinates_eq_rectangle T a ha haT f]
  change (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, H u v) = _
  rw [interval_integral_swap_rectangle U V hU hV H
    (continuous_nullCoordinate_inner T f hf)]
  have hpi (u v : ℝ) : H u v =
      ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ := by
    dsimp [H]
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hpi]
  apply intervalIntegral.integral_congr
  intro v hvint
  have hvcc : v ∈ Icc (0 : ℝ) V := by
    simpa [uIcc_of_le hV] using hvint
  change (∫ u in (0 : ℝ)..T / Real.sqrt 2,
      ∫ σ in nullLower T u v..2 * u * v, Real.pi * f σ) =
    ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
      (nullUpper T σ v - nullULower σ v) * (Real.pi * f σ)
  rw [integral_u_sigma_swap_Icc T a v ha haT hvcc f hf]
  apply intervalIntegral.integral_congr
  intro σ _hσ
  change (∫ _u in nullULower σ v..nullUpper T σ v,
    Real.pi * f σ) =
      (nullUpper T σ v - nullULower σ v) * (Real.pi * f σ)
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]

/-- Exact coarea formula in the original four-dimensional Lebesgue measure.
The logarithmic `nullCapWeightCore` is derived by evaluating both coordinate
fibres, including the `σ = 0` endpoint separately. -/
theorem integral_nullCap_eq_weightCore (T a : ℝ) (ha : 0 < a) (haT : a < T)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in nullCapRegion T a, f (intervalSq x 0)) =
      ∫ σ in (0 : ℝ)..a * T, f σ * nullCapWeightCore T a σ := by
  have hT : 0 < T := ha.trans haT
  have haT0 : 0 ≤ a * T := mul_nonneg ha.le hT.le
  rw [integral_nullCap_eq_sigma_v T a ha haT f hf]
  change (∫ v in (0 : ℝ)..a / Real.sqrt 2,
      ∫ σ in (0 : ℝ)..Real.sqrt 2 * T * v,
        nullCoordinateWidth T σ v * (Real.pi * f σ)) = _
  rw [integral_v_sigma_swap T a ha haT f hf]
  apply intervalIntegral.integral_congr
  intro σ hσint
  have hσcc : σ ∈ Icc (0 : ℝ) (a * T) := by
    simpa [uIcc_of_le haT0] using hσint
  have hweight : Real.pi *
      (∫ v in σ / (Real.sqrt 2 * T)..a / Real.sqrt 2,
        nullCoordinateWidth T σ v) = nullCapWeightCore T a σ := by
    rcases eq_or_lt_of_le hσcc.1 with hzero | hpos
    · subst σ
      simpa using nullWidthIntegral_zero T a ha haT
    · exact nullWidthIntegral_eq_core T a σ ha haT hpos hσcc.2
  calc
    (∫ v in σ / (Real.sqrt 2 * T)..a / Real.sqrt 2,
        nullCoordinateWidth T σ v * (Real.pi * f σ)) =
        (Real.pi * f σ) *
          (∫ v in σ / (Real.sqrt 2 * T)..a / Real.sqrt 2,
            nullCoordinateWidth T σ v) := by
              rw [intervalIntegral.integral_mul_const]
              ring
    _ = f σ * (Real.pi *
          ∫ v in σ / (Real.sqrt 2 * T)..a / Real.sqrt 2,
            nullCoordinateWidth T σ v) := by ring
    _ = f σ * nullCapWeightCore T a σ := by rw [hweight]

end BoundaryDraft
