import BoundaryDraft.NullGeometry
import BoundaryDraft.SpacetimeIntegration
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Exact four-dimensional causal-interval kernel identity

The proof uses no power-series interchange.  Spatial polar integration and a
measure-preserving null-coordinate matrix reduce the actual four-dimensional
Lebesgue integral to a triangle.  Two explicit finite-interval primitives then
perform the BDG cancellation.
-/

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section
namespace BoundaryDraft

abbrev Plane := Fin 2 → ℝ

private def planeCoordEquiv : ℝ × ℝ ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm

private theorem planeCoordEquiv_apply (x y : ℝ) :
    planeCoordEquiv (x, y) = ![x, y] := rfl

private theorem planeCoordEquiv_measurePreserving : MeasurePreserving planeCoordEquiv :=
  (volume_preserving_finTwoArrow ℝ).symm _

/-- Fubini for a two-coordinate product, in coordinate order. -/
theorem integral_plane_fibres (f : Plane → ℝ) (hf : Integrable f) :
    (∫ p, f p) = ∫ x : ℝ, ∫ y : ℝ, f ![x, y] := by
  have hi := (planeCoordEquiv_measurePreserving.integrable_comp_emb
    planeCoordEquiv.measurableEmbedding).mpr hf
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  rw [← planeCoordEquiv_measurePreserving.integral_comp' f,
    Measure.volume_eq_prod, integral_prod _ hi]
  simp_rw [planeCoordEquiv_apply]

/-- Fubini with the second plane coordinate integrated outside. -/
theorem integral_plane_slices (f : Plane → ℝ) (hf : Integrable f) :
    (∫ p, f p) = ∫ y : ℝ, ∫ x : ℝ, f ![x, y] := by
  have hi := (planeCoordEquiv_measurePreserving.integrable_comp_emb
    planeCoordEquiv.measurableEmbedding).mpr hf
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  rw [← planeCoordEquiv_measurePreserving.integral_comp' f,
    Measure.volume_eq_prod, integral_prod_symm _ hi]
  simp_rw [planeCoordEquiv_apply]

/-- Time-radius image of a standard causal interval. -/
def timeRadialDiamond (T : ℝ) : Set Plane :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ p 0 ∧ p 0 + p 1 ≤ T}

/-- Triangular radial null-coordinate domain. -/
def nullTriangle (T : ℝ) : Set Plane :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ p 1 ∧ p 1 ≤ T / Real.sqrt 2}

private theorem measurableSet_timeRadialDiamond (T : ℝ) :
    MeasurableSet (timeRadialDiamond T) := by
  have h0 : Continuous (fun _ : Plane => (0 : ℝ)) := continuous_const
  have hp0 : Continuous (fun p : Plane => p 0) := continuous_apply 0
  have hp1 : Continuous (fun p : Plane => p 1) := continuous_apply 1
  have hT : Continuous (fun _ : Plane => T) := continuous_const
  exact (isClosed_le h0 hp1).inter
    ((isClosed_le hp1 hp0).inter (isClosed_le (hp0.add hp1) hT)) |>.measurableSet

private theorem measurableSet_nullTriangle (T : ℝ) :
    MeasurableSet (nullTriangle T) := by
  have h0 : Continuous (fun _ : Plane => (0 : ℝ)) := continuous_const
  have hp0 : Continuous (fun p : Plane => p 0) := continuous_apply 0
  have hp1 : Continuous (fun p : Plane => p 1) := continuous_apply 1
  have hT : Continuous (fun _ : Plane => T / Real.sqrt 2) := continuous_const
  exact (isClosed_le h0 hp0).inter
    ((isClosed_le hp0 hp1).inter (isClosed_le hp1 hT)) |>.measurableSet

private theorem timeRadialDiamond_subset_box (T : ℝ) (hT : 0 ≤ T) :
    timeRadialDiamond T ⊆ Icc (fun _ => -T) (fun _ => T) := by
  intro p hp
  have hr0 : 0 ≤ p 1 := hp.1
  have hrt : p 1 ≤ p 0 := hp.2.1
  have hsum : p 0 + p 1 ≤ T := hp.2.2
  constructor <;> intro i
  · fin_cases i <;> simp <;> linarith
  · fin_cases i <;> simp <;> linarith

private theorem integrableOn_timeRadialDiamond (T : ℝ) (hT : 0 ≤ T)
    (f : Plane → ℝ) (hf : Continuous f) : IntegrableOn f (timeRadialDiamond T) :=
  hf.integrableOn_Icc.mono_set (timeRadialDiamond_subset_box T hT)

/-- Spatial polar integration plus Fubini, still in ordinary time-radius
coordinates.  All sphere and interval boundary choices are retained as closed
sets here and hence need no informal endpoint convention. -/
theorem integral_standard_causalInterval_eq_timeRadial
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ y in causalInterval 0 (timeAxis T), f (intervalSq 0 y)) =
      ∫ p in timeRadialDiamond T,
        4 * Real.pi * p 1 ^ 2 * f (p 0 ^ 2 - p 1 ^ 2) := by
  let F := fun y : Spacetime => f (intervalSq 0 y)
  have hF : Continuous F := by
    exact hf.comp (continuous_intervalSq.comp (continuous_const.prodMk continuous_id))
  have hset : causalInterval 0 (timeAxis T) ⊆
      Icc (fun _ => -T) (fun _ => T) := by
    intro y hy
    have ht0 : 0 ≤ y 0 := hy.1.1
    have htT : y 0 ≤ T := hy.2.1
    have hs : (∑ i : Fin 3, y i.succ ^ 2) ≤ y 0 ^ 2 := by
      simpa [causalFuture, spatialSeparationSq] using hy.1.2
    have hc (i : Fin 3) : |y i.succ| ≤ T := by
      have hi0 : y i.succ ^ 2 ≤ ∑ j : Fin 3, y j.succ ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (y j.succ)) (Finset.mem_univ i)
      have hi : y i.succ ^ 2 ≤ T ^ 2 :=
        hi0.trans (hs.trans ((sq_le_sq₀ ht0 hT.le).mpr htT))
      exact (sq_le_sq₀ (abs_nonneg _) hT.le).mp (by simpa only [sq_abs] using hi)
    constructor <;> intro i
    · refine Fin.cases (by simp; linarith) (fun j => (abs_le.mp (hc j)).1) i
    · refine Fin.cases (by simpa) (fun j => (abs_le.mp (hc j)).2) i
  have hpast : IsClosed (causalPast (timeAxis T)) := by
    unfold causalPast causalFuture
    apply IsClosed.inter
    · exact isClosed_le (continuous_apply 0) continuous_const
    · change IsClosed {x : Spacetime | spatialSeparationSq x (timeAxis T) ≤
        (timeAxis T 0 - x 0) ^ 2}
      have hq : Continuous (fun _ : Spacetime => timeAxis T) := continuous_const
      have ht : Continuous (fun _ : Spacetime => timeAxis T 0) := continuous_const
      exact isClosed_le
        (continuous_spatialSeparationSq.comp (continuous_id.prodMk hq))
        ((ht.sub (continuous_apply 0)).pow 2)
  have hm : MeasurableSet (causalInterval 0 (timeAxis T)) :=
    (isClosed_causalFuture 0).measurableSet.inter hpast.measurableSet
  have hi : IntegrableOn F (causalInterval 0 (timeAxis T)) :=
    hF.integrableOn_Icc.mono_set hset
  rw [← integral_indicator hm,
    integral_spacetime_slices _ ((integrable_indicator_iff hm).mpr hi)]
  let G := fun p : Plane => 4 * Real.pi * p 1 ^ 2 * f (p 0 ^ 2 - p 1 ^ 2)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hiG : Integrable ((timeRadialDiamond T).indicator G) :=
    integrable_indicator_iff (measurableSet_timeRadialDiamond T) |>.mpr
      (integrableOn_timeRadialDiamond T hT.le G hG)
  rw [← integral_indicator (measurableSet_timeRadialDiamond T),
    integral_plane_fibres _ hiG]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    let H := min t (T - t)
    have hmem (x : Spatial) :
        Fin.cons t x ∈ causalInterval 0 (timeAxis T) ↔
          t ∈ Icc (0 : ℝ) T ∧ ∑ i : Fin 3, x i ^ 2 ≤ H ^ 2 := by
      constructor
      · intro hx
        have ht0 : 0 ≤ t := by
          simpa [causalInterval, causalFuture] using hx.1.1
        have htT : t ≤ T := by
          simpa [causalInterval, causalPast, causalFuture] using hx.2.1
        have hs0 : (∑ i : Fin 3, x i ^ 2) ≤ t ^ 2 := by
          simpa [causalInterval, causalFuture, spatialSeparationSq] using hx.1.2
        have hsT : (∑ i : Fin 3, x i ^ 2) ≤ (T - t) ^ 2 := by
          simpa [causalInterval, causalPast, causalFuture, spatialSeparationSq] using hx.2.2
        refine ⟨⟨ht0, htT⟩, ?_⟩
        rcases le_total t (T - t) with h | h
        · simpa [H, min_eq_left h] using hs0
        · simpa [H, min_eq_right h] using hsT
      · rintro ⟨ht, hs⟩
        have hH0 : 0 ≤ H := le_min ht.1 (sub_nonneg.mpr ht.2)
        have hs0 := hs.trans ((sq_le_sq₀ hH0 ht.1).mpr (min_le_left _ _))
        have hsT := hs.trans ((sq_le_sq₀ hH0 (sub_nonneg.mpr ht.2)).mpr
          (min_le_right _ _))
        constructor
        · exact ⟨by simpa [causalFuture] using ht.1, by
            simpa [causalFuture, spatialSeparationSq] using hs0⟩
        · exact ⟨by simpa [causalPast, causalFuture] using ht.2, by
            simpa [causalPast, causalFuture, spatialSeparationSq] using hsT⟩
    have hevent (x : Spatial) :
        (causalInterval 0 (timeAxis T)).indicator F (Fin.cons t x) =
          (if t ∈ Icc (0 : ℝ) T then
            {x : Spatial | ∑ i : Fin 3, x i ^ 2 ≤ H ^ 2}.indicator
              (fun x => f (t ^ 2 - ∑ i : Fin 3, x i ^ 2)) x else 0) := by
      by_cases ht : t ∈ Icc (0 : ℝ) T
      · rw [if_pos ht]
        by_cases hs : ∑ i : Fin 3, x i ^ 2 ≤ H ^ 2
        · rw [Set.indicator_of_mem ((hmem x).mpr ⟨ht, hs⟩)]
          simp [Set.indicator, hs, F, intervalSq, spatialSeparationSq]
        · rw [Set.indicator_of_not_mem (fun h => hs ((hmem x).mp h).2)]
          simp [Set.indicator, hs]
      · rw [if_neg ht, Set.indicator_of_not_mem (fun h => ht ((hmem x).mp h).1)]
    simp_rw [hevent]
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · simp only [ht, if_true]
      have hH0 : 0 ≤ H := le_min ht.1 (sub_nonneg.mpr ht.2)
      have hs : MeasurableSet {x : Spatial | ∑ i : Fin 3, x i ^ 2 ≤ H ^ 2} := by
        apply isClosed_le ?_ continuous_const |>.measurableSet
        fun_prop
      rw [integral_indicator hs,
        integral_spatial_radial H hH0 (fun s => f (t ^ 2 - s))]
      have hslice : (∫ r : ℝ, (timeRadialDiamond T).indicator G ![t, r]) =
          4 * Real.pi * ∫ r in (0 : ℝ)..H, r ^ 2 * f (t ^ 2 - r ^ 2) := by
        have he (r : ℝ) : (timeRadialDiamond T).indicator G ![t, r] =
            (Icc 0 H).indicator (fun r => 4 * Real.pi * r ^ 2 * f (t ^ 2 - r ^ 2)) r := by
          have hr : (![t, r] : Plane) ∈ timeRadialDiamond T ↔ r ∈ Icc 0 H := by
            simp only [timeRadialDiamond, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_fin_one, mem_setOf_eq, mem_Icc]
            constructor
            · rintro ⟨hr0, hrt, hsum⟩
              exact ⟨hr0, le_min hrt (by linarith)⟩
            · rintro ⟨hr0, hrH⟩
              exact ⟨hr0, hrH.trans (min_le_left _ _), by
                have := hrH.trans (min_le_right _ _)
                linarith⟩
          simp [Set.indicator, hr, G]
        simp_rw [he]
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hH0]
        calc
          (∫ r in (0 : ℝ)..H, 4 * Real.pi * r ^ 2 * f (t ^ 2 - r ^ 2)) =
              ∫ r in (0 : ℝ)..H, (4 * Real.pi) *
                (r ^ 2 * f (t ^ 2 - r ^ 2)) := by
                apply intervalIntegral.integral_congr
                intro r _
                ring
          _ = _ := intervalIntegral.integral_const_mul
            (4 * Real.pi) (fun r => r ^ 2 * f (t ^ 2 - r ^ 2))
      rw [hslice]
    · simp only [ht, if_false, integral_zero]
      have he (r : ℝ) : (timeRadialDiamond T).indicator G ![t, r] = 0 := by
        apply Set.indicator_of_not_mem
        intro hr
        simp only [timeRadialDiamond, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, mem_setOf_eq] at hr
        exact ht ⟨le_trans hr.1 hr.2.1, by linarith [hr.1, hr.2.2]⟩
      simp_rw [he]
      rw [integral_zero]

private def nullMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹;
     -(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹]

private theorem nullMatrix_apply (p : Plane) :
    Matrix.toLin' nullMatrix p =
      ![(p 0 + p 1) / Real.sqrt 2, (p 1 - p 0) / Real.sqrt 2] := by
  ext i
  fin_cases i <;> simp [nullMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    div_eq_mul_inv] <;> ring

private theorem det_nullMatrix : Matrix.det nullMatrix = 1 := by
  rw [Matrix.det_fin_two]
  simp [nullMatrix]
  field_simp

private theorem nullMatrix_injective : Function.Injective (Matrix.toLin' nullMatrix) := by
  intro p q h
  have h0 := congrFun h (0 : Fin 2)
  have h1 := congrFun h (1 : Fin 2)
  simp only [nullMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  ext i
  fin_cases i <;> field_simp at h0 h1 ⊢ <;> linarith

private theorem nullMatrix_measurableEmbedding :
    MeasurableEmbedding (Matrix.toLin' nullMatrix) :=
  (Matrix.toLin' nullMatrix).continuous_of_finiteDimensional.measurableEmbedding
    nullMatrix_injective

private theorem nullMatrix_measurePreserving :
    MeasurePreserving (Matrix.toLin' nullMatrix) := by
  refine ⟨(Matrix.toLin' nullMatrix).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [det_nullMatrix]; norm_num),
    det_nullMatrix]
  simp

private theorem nullMatrix_preimage (T : ℝ) :
    Matrix.toLin' nullMatrix ⁻¹' timeRadialDiamond T = nullTriangle T := by
  ext p
  rw [mem_preimage]
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsdiv : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hs0.ne').mpr
    nlinarith
  have hadd : (p 0 + p 1) / Real.sqrt 2 + (p 1 - p 0) / Real.sqrt 2 =
      Real.sqrt 2 * p 1 := by
    calc
      _ = (2 / Real.sqrt 2) * p 1 := by ring
      _ = _ := by rw [hsdiv]
  simp only [timeRadialDiamond, nullTriangle, mem_setOf_eq, nullMatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨hr0, hrt, hsum⟩
    have hnum : 0 ≤ p 1 - p 0 := by
      rw [← div_mul_cancel₀ (p 1 - p 0) hs0.ne']
      exact mul_nonneg hr0 hs0.le
    have hu0 : 0 ≤ p 0 := by
      have := (div_le_div_iff_of_pos_right hs0).mp hrt
      linarith
    refine ⟨hu0, by linarith, ?_⟩
    apply (le_div_iff₀ hs0).mpr
    rw [hadd] at hsum
    simpa only [mul_comm] using hsum
  · rintro ⟨hu0, huv, hvT⟩
    refine ⟨div_nonneg (sub_nonneg.mpr huv) hs0.le, ?_, ?_⟩
    · exact (div_le_div_iff_of_pos_right hs0).mpr (by linarith)
    · rw [hadd]
      simpa only [mul_comm] using (le_div_iff₀ hs0).mp hvT

/-- The time-radius integral in exact radial null coordinates, including the
Jacobian and angular factor. -/
theorem integral_timeRadial_eq_nullTriangle
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in timeRadialDiamond T,
      4 * Real.pi * p 1 ^ 2 * f (p 0 ^ 2 - p 1 ^ 2)) =
      2 * Real.pi * ∫ v in (0 : ℝ)..T / Real.sqrt 2,
        ∫ u in (0 : ℝ)..v, (v - u) ^ 2 * f (2 * u * v) := by
  let G := fun p : Plane => 4 * Real.pi * p 1 ^ 2 * f (p 0 ^ 2 - p 1 ^ 2)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hiG : Integrable ((timeRadialDiamond T).indicator G) :=
    integrable_indicator_iff (measurableSet_timeRadialDiamond T) |>.mpr
      (integrableOn_timeRadialDiamond T hT.le G hG)
  rw [← integral_indicator (measurableSet_timeRadialDiamond T),
    ← nullMatrix_measurePreserving.integral_comp nullMatrix_measurableEmbedding _]
  have hiN : Integrable (fun p => (timeRadialDiamond T).indicator G
      (Matrix.toLin' nullMatrix p)) := by
    exact (nullMatrix_measurePreserving.integrable_comp_emb
      nullMatrix_measurableEmbedding).mpr hiG
  have he (p : Plane) : (timeRadialDiamond T).indicator G
      (Matrix.toLin' nullMatrix p) =
        (nullTriangle T).indicator
          (fun p => 2 * Real.pi * (p 1 - p 0) ^ 2 * f (2 * p 0 * p 1)) p := by
    have hmem : Matrix.toLin' nullMatrix p ∈ timeRadialDiamond T ↔
        p ∈ nullTriangle T := by
      change p ∈ Matrix.toLin' nullMatrix ⁻¹' timeRadialDiamond T ↔ _
      rw [nullMatrix_preimage]
    by_cases hp : p ∈ nullTriangle T
    · rw [Set.indicator_of_mem (hmem.mpr hp), Set.indicator_of_mem hp]
      have hcoord := nullMatrix_apply p
      have hcoord0 := congrFun hcoord (0 : Fin 2)
      have hcoord1 := congrFun hcoord (1 : Fin 2)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hcoord0 hcoord1
      change 4 * Real.pi * (Matrix.toLin' nullMatrix p) 1 ^ 2 *
          f ((Matrix.toLin' nullMatrix p) 0 ^ 2 -
            (Matrix.toLin' nullMatrix p) 1 ^ 2) = _
      rw [hcoord0, hcoord1]
      congr 1
      · field_simp
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      · congr 1
        field_simp
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · rw [Set.indicator_of_not_mem (fun h => hp (hmem.mp h)),
        Set.indicator_of_not_mem hp]
  have hfun : (fun p => (timeRadialDiamond T).indicator G
      (Matrix.toLin' nullMatrix p)) =
      (nullTriangle T).indicator
        (fun p => 2 * Real.pi * (p 1 - p 0) ^ 2 * f (2 * p 0 * p 1)) := by
    funext p
    exact he p
  have hiN' : Integrable ((nullTriangle T).indicator
      (fun p => 2 * Real.pi * (p 1 - p 0) ^ 2 * f (2 * p 0 * p 1))) := by
    rw [← hfun]
    exact hiN
  rw [hfun, integral_plane_slices _ hiN']
  have hU : 0 ≤ T / Real.sqrt 2 := div_nonneg hT.le (Real.sqrt_nonneg _)
  have hslices : (∫ v : ℝ, ∫ u : ℝ,
      (nullTriangle T).indicator
        (fun p => 2 * Real.pi * (p 1 - p 0) ^ 2 * f (2 * p 0 * p 1)) ![u, v]) =
      2 * Real.pi * ∫ v in (0 : ℝ)..T / Real.sqrt 2,
        ∫ u in (0 : ℝ)..v, (v - u) ^ 2 * f (2 * u * v) := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le hU, ← integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      by_cases hv : v ∈ Icc (0 : ℝ) (T / Real.sqrt 2)
      · rw [Set.indicator_of_mem hv]
        have he' (u : ℝ) : (nullTriangle T).indicator
            (fun p => 2 * Real.pi * (p 1 - p 0) ^ 2 * f (2 * p 0 * p 1)) ![u, v] =
            (Icc 0 v).indicator
              (fun u => 2 * Real.pi * (v - u) ^ 2 * f (2 * u * v)) u := by
          simp [Set.indicator, nullTriangle, hv.2]
        simp_rw [he']
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hv.1]
        calc
          (∫ u in (0 : ℝ)..v, 2 * Real.pi * (v - u) ^ 2 * f (2 * u * v)) =
              ∫ u in (0 : ℝ)..v, (2 * Real.pi) *
                ((v - u) ^ 2 * f (2 * u * v)) := by
                apply intervalIntegral.integral_congr
                intro u _
                ring
          _ = _ := intervalIntegral.integral_const_mul
            (2 * Real.pi) (fun u => (v - u) ^ 2 * f (2 * u * v))
      · rw [Set.indicator_of_not_mem hv]
        have he' (u : ℝ) : (nullTriangle T).indicator
            (fun p => 2 * Real.pi * (p 1 - p 0) ^ 2 * f (2 * p 0 * p 1)) ![u, v] = 0 := by
          apply Set.indicator_of_not_mem
          intro hp
          simp only [nullTriangle, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, mem_setOf_eq] at hp
          exact hv ⟨hp.1.trans hp.2.1, hp.2.2⟩
        simp_rw [he']
        rw [integral_zero]
  exact hslices

private def intervalPrimitive (A w : ℝ) : ℝ :=
  (w - 4 * A * w ^ 2 + (4 / 3 : ℝ) * A ^ 2 * w ^ 3) * Real.exp (-A * w)

private theorem hasDerivAt_intervalPrimitive (A w : ℝ) :
    HasDerivAt (intervalPrimitive A)
      (bdgKernel (A * w)) w := by
  convert (((hasDerivAt_id w).sub
    (((hasDerivAt_id w).pow 2).const_mul (4 * A))).add
    (((hasDerivAt_id w).pow 3).const_mul ((4 / 3 : ℝ) * A ^ 2))).mul
      (((hasDerivAt_id w).const_mul (-A)).exp) using 1
  all_goals
    dsimp [intervalPrimitive, bdgKernel, bdgPolynomial]
    ring

private def intervalOuterPrimitive (Z s : ℝ) : ℝ :=
  (-(1 / (3 * Z)) + s - (4 / 3 : ℝ) * s ^ 2 +
      (1 / 3 - 2 * Z / 3) * s ^ 3 + (4 * Z / 3) * s ^ 4 -
      (2 * Z / 3) * s ^ 5) * Real.exp (-Z * s ^ 2)

private theorem hasDerivAt_intervalOuterPrimitive (Z s : ℝ) (hZ : Z ≠ 0) :
    HasDerivAt (intervalOuterPrimitive Z)
      ((1 - s) ^ 2 * (1 - 4 * Z * s ^ 2 + (4 / 3 : ℝ) * Z ^ 2 * s ^ 4) *
        Real.exp (-Z * s ^ 2)) s := by
  have hpoly := ((((((hasDerivAt_const s (-(1 / (3 * Z)))).add (hasDerivAt_id s)).sub
    (((hasDerivAt_id s).pow 2).const_mul (4 / 3 : ℝ))).add
    (((hasDerivAt_id s).pow 3).const_mul (1 / 3 - 2 * Z / 3))).add
    (((hasDerivAt_id s).pow 4).const_mul (4 * Z / 3))).sub
    (((hasDerivAt_id s).pow 5).const_mul (2 * Z / 3)))
  simp only [id_eq] at hpoly
  have hexp : HasDerivAt (fun x => Real.exp (-Z * x ^ 2))
      (-2 * Z * s * Real.exp (-Z * s ^ 2)) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul (-Z)).exp using 1
    simp only [id_eq]
    ring
  simp only [id_eq] at hexp
  convert hpoly.mul hexp using 1
  all_goals
    dsimp [intervalOuterPrimitive]
    field_simp
    ring

private theorem integral_integral_swap_unit (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y) =
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F x y := by
  have hi0 : IntegrableOn (Function.uncurry F)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : IntegrableOn (Function.uncurry F)
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    hi0.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [Measure.volume_eq_prod ℝ ℝ, IntegrableOn, ← Measure.prod_restrict] at hi
  have h := integral_integral_swap hi
  simpa only [← intervalIntegral.integral_of_le zero_le_one] using h

private theorem interval_triangle_evaluation (Z : ℝ) (hZ : 0 < Z) :
    (∫ q in (0 : ℝ)..1, q ^ 3 *
      ∫ s in (0 : ℝ)..1, (1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2)) =
        (1 - Real.exp (-Z)) / (12 * Z) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      p.1 ^ 3 * ((1 - p.2) ^ 2 * bdgKernel (Z * p.1 ^ 4 * p.2 ^ 2))) := by
    dsimp [bdgKernel, bdgPolynomial]
    fun_prop
  have hswap := integral_integral_swap_unit
    (fun q s => q ^ 3 * ((1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2))) hc
  have hleft : (∫ q in (0 : ℝ)..1, q ^ 3 *
      ∫ s in (0 : ℝ)..1, (1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2)) =
      ∫ q in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
        q ^ 3 * ((1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro q _
    exact (intervalIntegral.integral_const_mul (q ^ 3)
      (fun s => (1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2))).symm
  rw [hleft, hswap]
  have hinner (s : ℝ) :
      (∫ q in (0 : ℝ)..1, q ^ 3 * bdgKernel (Z * q ^ 4 * s ^ 2)) =
        (1 / 4 : ℝ) * (1 - 4 * (Z * s ^ 2) +
          (4 / 3 : ℝ) * (Z * s ^ 2) ^ 2) * Real.exp (-(Z * s ^ 2)) := by
    let A := Z * s ^ 2
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1) (f := fun q : ℝ => q ^ 4)
      (f' := fun q : ℝ => 4 * q ^ 3) (g := fun w => bdgKernel (A * w))
      (fun q _ => by
        convert ((hasDerivAt_id q).pow 4) using 1
        simp only [id_eq]
        ring)
      (by fun_prop)
      (by dsimp [bdgKernel, bdgPolynomial, A]; fun_prop)
    simp only [Function.comp_def, zero_pow (by decide : (4 : ℕ) ≠ 0), one_pow] at hsub
    have hprim : (∫ w in (0 : ℝ)..1, bdgKernel (A * w)) =
        (1 - 4 * A + (4 / 3 : ℝ) * A ^ 2) * Real.exp (-A) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun w _ => hasDerivAt_intervalPrimitive A w)
        ((by dsimp [bdgKernel, bdgPolynomial]; fun_prop : Continuous _).intervalIntegrable 0 1)]
      simp [intervalPrimitive]
    rw [hprim] at hsub
    change (∫ q in (0 : ℝ)..1, q ^ 3 * bdgKernel (Z * q ^ 4 * s ^ 2)) = _
    rw [show (∫ q in (0 : ℝ)..1,
      bdgKernel (A * q ^ 4) * (4 * q ^ 3)) =
        4 * ∫ q in (0 : ℝ)..1, q ^ 3 * bdgKernel (A * q ^ 4) by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro q _
          ring] at hsub
    dsimp [A] at hsub ⊢
    calc
      (∫ q in (0 : ℝ)..1, q ^ 3 * bdgKernel (Z * q ^ 4 * s ^ 2)) =
          ∫ q in (0 : ℝ)..1, q ^ 3 * bdgKernel (Z * s ^ 2 * q ^ 4) := by
            apply intervalIntegral.integral_congr
            intro q _
            change q ^ 3 * bdgKernel (Z * q ^ 4 * s ^ 2) =
              q ^ 3 * bdgKernel (Z * s ^ 2 * q ^ 4)
            rw [show Z * q ^ 4 * s ^ 2 = Z * s ^ 2 * q ^ 4 by ring]
      _ = (1 / 4 : ℝ) * (4 * ∫ q in (0 : ℝ)..1,
          q ^ 3 * bdgKernel (Z * s ^ 2 * q ^ 4)) := by ring
      _ = _ := by
        rw [hsub]
        ring
  have hfactor (s : ℝ) : (∫ q in (0 : ℝ)..1,
      q ^ 3 * ((1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2))) =
      (1 - s) ^ 2 * ∫ q in (0 : ℝ)..1,
        q ^ 3 * bdgKernel (Z * q ^ 4 * s ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro q _
    ring
  simp_rw [hfactor, hinner]
  have heq : (∫ s in (0 : ℝ)..1, (1 - s) ^ 2 *
      ((1 / 4 : ℝ) * (1 - 4 * (Z * s ^ 2) +
        (4 / 3 : ℝ) * (Z * s ^ 2) ^ 2) * Real.exp (-(Z * s ^ 2)))) =
      (1 / 4 : ℝ) * ∫ s in (0 : ℝ)..1,
        (1 - s) ^ 2 * (1 - 4 * Z * s ^ 2 +
          (4 / 3 : ℝ) * Z ^ 2 * s ^ 4) * Real.exp (-Z * s ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [heq]
  have hcont : Continuous (fun s : ℝ =>
      (1 - s) ^ 2 * (1 - 4 * Z * s ^ 2 + (4 / 3 : ℝ) * Z ^ 2 * s ^ 4) *
        Real.exp (-Z * s ^ 2)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_intervalOuterPrimitive Z s hZ.ne')
    (hcont.intervalIntegrable 0 1)]
  simp [intervalOuterPrimitive]
  field_simp
  ring

/-- Exact identity in the standard rest frame, starting from the actual
four-dimensional causal interval and concrete `bdgKernel`. -/
theorem standard_causalInterval_kernel_identity
    (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ρ * (∫ y in causalInterval 0 (timeAxis T),
      bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 y ^ 2)) =
        1 - Real.exp (-(Real.pi / 24) * ρ * T ^ 4) := by
  let Z := (Real.pi / 24) * ρ * T ^ 4
  have hZ : 0 < Z := by dsimp [Z]; positivity
  rw [integral_standard_causalInterval_eq_timeRadial T hT
      (fun σ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))
      (by dsimp [bdgKernel, bdgPolynomial]; fun_prop),
    integral_timeRadial_eq_nullTriangle T hT
      (fun σ => bdgKernel ((Real.pi / 24) * ρ * σ ^ 2))
      (by dsimp [bdgKernel, bdgPolynomial]; fun_prop)]
  let U := T / Real.sqrt 2
  have hU : U ≠ 0 := by dsimp [U]; positivity
  have hv (v : ℝ) : (∫ u in (0 : ℝ)..v,
      (v - u) ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (2 * u * v) ^ 2)) =
      v ^ 3 * ∫ s in (0 : ℝ)..1,
        (1 - s) ^ 2 * bdgKernel (Z * (v / U) ^ 4 * s ^ 2) := by
    have hu := intervalIntegral.smul_integral_comp_mul_left
      (fun u => (v - u) ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (2 * u * v) ^ 2))
      (a := (0 : ℝ)) (b := 1) v
    simp only [smul_eq_mul, mul_zero, mul_one] at hu
    calc
      _ = v * ∫ s in (0 : ℝ)..1,
          (v - v * s) ^ 2 * bdgKernel ((Real.pi / 24) * ρ * (2 * (v * s) * v) ^ 2) := hu.symm
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s _
        have hs4 : Real.sqrt 2 ^ 4 = 4 := by
          rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        have harg : (Real.pi / 24) * ρ * (2 * (v * s) * v) ^ 2 =
            Z * (v / U) ^ 4 * s ^ 2 := by
          dsimp [Z, U]
          field_simp
          ring_nf
          rw [hs4]
          ring
        change v * ((v - v * s) ^ 2 *
          bdgKernel ((Real.pi / 24) * ρ * (2 * (v * s) * v) ^ 2)) =
            v ^ 3 * ((1 - s) ^ 2 * bdgKernel (Z * (v / U) ^ 4 * s ^ 2))
        rw [harg]
        ring
  simp_rw [hv]
  have hscale : (∫ v in (0 : ℝ)..U,
      v ^ 3 * ∫ s in (0 : ℝ)..1,
        (1 - s) ^ 2 * bdgKernel (Z * (v / U) ^ 4 * s ^ 2)) =
      U ^ 4 * ∫ q in (0 : ℝ)..1,
        q ^ 3 * ∫ s in (0 : ℝ)..1,
          (1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2) := by
    have hs := intervalIntegral.smul_integral_comp_mul_left
      (fun v => v ^ 3 * ∫ s in (0 : ℝ)..1,
        (1 - s) ^ 2 * bdgKernel (Z * (v / U) ^ 4 * s ^ 2))
      (a := (0 : ℝ)) (b := 1) U
    simp only [smul_eq_mul, mul_zero, mul_one] at hs
    calc
      _ = U * ∫ q in (0 : ℝ)..1,
          (U * q) ^ 3 * ∫ s in (0 : ℝ)..1,
            (1 - s) ^ 2 * bdgKernel (Z * ((U * q) / U) ^ 4 * s ^ 2) := hs.symm
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro q _
        have hratio : U * q / U = q := by field_simp
        change U * ((U * q) ^ 3 * ∫ s in (0 : ℝ)..1,
          (1 - s) ^ 2 * bdgKernel (Z * (U * q / U) ^ 4 * s ^ 2)) =
            U ^ 4 * (q ^ 3 * ∫ s in (0 : ℝ)..1,
              (1 - s) ^ 2 * bdgKernel (Z * q ^ 4 * s ^ 2))
        rw [hratio]
        ring
  change ρ * (2 * Real.pi * ∫ v in (0 : ℝ)..U,
    v ^ 3 * ∫ s in (0 : ℝ)..1,
      (1 - s) ^ 2 * bdgKernel (Z * (v / U) ^ 4 * s ^ 2)) = _
  rw [hscale, interval_triangle_evaluation Z hZ]
  have hU4 : U ^ 4 = T ^ 4 / 4 := by
    dsimp [U]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith [sq_nonneg (T ^ 2), hs2]
  rw [hU4]
  dsimp [Z]
  field_simp
  ring

end BoundaryDraft
