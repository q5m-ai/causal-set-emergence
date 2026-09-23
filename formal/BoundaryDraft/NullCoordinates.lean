import BoundaryDraft.NullBoundary
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Null coordinates and the exact null-cap weight

The orthogonal `(+,-)` null-coordinate matrix below acts on all four original
coordinates.  Its Jacobian is proved from an explicit involution identity.
The transverse two-plane is then integrated in polar coordinates.
-/

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section
namespace BoundaryDraft

/-- The algebraic weight on its natural support.  Writing the logarithmic term
as `σ log σ - σ log (aT)` gives its mathematically correct value at `σ = 0`
without a separate convention. -/
def nullCapWeightCore (T a σ : ℝ) : ℝ :=
  Real.pi / 4 * (a * (2 * T - a) - 2 * (1 - a / T) * σ - σ ^ 2 / T ^ 2 +
    2 * σ * Real.log σ - 2 * σ * Real.log (a * T))

/-- The exact coarea weight, extended by zero off `0 ≤ σ < aT`. -/
def nullCapWeight (T a σ : ℝ) : ℝ :=
  if σ ∈ Ico (0 : ℝ) (a * T) then nullCapWeightCore T a σ else 0

@[simp] theorem nullCapWeight_zero (T a : ℝ) (h : 0 < a * T) :
    nullCapWeight T a 0 = Real.pi / 4 * (a * (2 * T - a)) := by
  simp [nullCapWeight, nullCapWeightCore, h]

@[simp] theorem nullCapWeight_of_ge (T a σ : ℝ) (h : a * T ≤ σ) :
    nullCapWeight T a σ = 0 := by
  simp [nullCapWeight, not_lt.mpr h]

/-- On positive support, the continuous-at-zero formula is exactly the
logarithmic formula stated in the calculation. -/
theorem nullCapWeightCore_eq_log_ratio (T a σ : ℝ)
    (hσ : 0 < σ) (haT : 0 < a * T) :
    nullCapWeightCore T a σ = Real.pi / 4 *
      (a * (2 * T - a) - 2 * (1 - a / T) * σ - σ ^ 2 / T ^ 2 -
        2 * σ * Real.log (a * T / σ)) := by
  rw [Real.log_div haT.ne' hσ.ne']
  unfold nullCapWeightCore
  ring

/-- Orthogonal null coordinates `(U,V,Y,Z) ↦ (t,z,y,z₂)`, with
`t = -(U+V)/√2` and `z = (V-U)/√2`. -/
def nullCapMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹, 0, 0;
     -(Real.sqrt 2)⁻¹,  (Real.sqrt 2)⁻¹, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Coordinate formula for the full four-dimensional null map. -/
theorem nullCapMatrix_apply (p : Spacetime) :
    Matrix.toLin' nullCapMatrix p =
      ![-(p 0 + p 1) / Real.sqrt 2,
        (p 1 - p 0) / Real.sqrt 2, p 2, p 3] := by
  ext i
  fin_cases i <;>
    simp [nullCapMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

private theorem nullCapMatrix_mul_self : nullCapMatrix * nullCapMatrix = 1 := by
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← mul_inv, hsqrt, one_div]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nullCapMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith

private theorem nullCapMatrix_det_ne_zero : Matrix.det nullCapMatrix ≠ 0 := by
  intro h
  have hd := congrArg Matrix.det nullCapMatrix_mul_self
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hd
  norm_num at hd

private theorem abs_det_nullCapMatrix : |Matrix.det nullCapMatrix| = 1 := by
  have hd := congrArg Matrix.det nullCapMatrix_mul_self
  rw [Matrix.det_mul, Matrix.det_one] at hd
  apply (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp
  rw [pow_two, ← abs_mul, hd, abs_one]
  norm_num

private theorem nullCapMatrix_injective :
    Function.Injective (Matrix.toLin' nullCapMatrix) := by
  intro p q h
  have h' := congrArg (Matrix.toLin' nullCapMatrix) h
  change nullCapMatrix.mulVec (nullCapMatrix.mulVec p) =
    nullCapMatrix.mulVec (nullCapMatrix.mulVec q) at h'
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    nullCapMatrix_mul_self, Matrix.one_mulVec, Matrix.one_mulVec] at h'
  exact h'

theorem nullCapMatrix_measurableEmbedding :
    MeasurableEmbedding (Matrix.toLin' nullCapMatrix) :=
  (Matrix.toLin' nullCapMatrix).continuous_of_finiteDimensional.measurableEmbedding
    nullCapMatrix_injective

/-- The null-coordinate Jacobian has absolute determinant one. -/
theorem nullCapMatrix_measurePreserving :
    MeasurePreserving (Matrix.toLin' nullCapMatrix) := by
  refine ⟨(Matrix.toLin' nullCapMatrix).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi nullCapMatrix_det_ne_zero,
    abs_inv, abs_det_nullCapMatrix]
  simp

private def spatialPlaneCoordEquiv : ℝ × Plane ≃ᵐ Spatial :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm

private theorem spatialPlaneCoordEquiv_apply (v : ℝ) (p : Plane) :
    spatialPlaneCoordEquiv (v, p) = Fin.cons v p := by
  simp [spatialPlaneCoordEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]

private theorem spatialPlaneCoordEquiv_measurePreserving :
    MeasurePreserving spatialPlaneCoordEquiv :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _

/-- Fubini for a spatial three-vector split into its first coordinate and a
transverse two-plane. -/
theorem integral_spatial_plane_slices (f : Spatial → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ v : ℝ, ∫ p : Plane, f (Fin.cons v p) := by
  have hi := (spatialPlaneCoordEquiv_measurePreserving.integrable_comp_emb
    spatialPlaneCoordEquiv.measurableEmbedding).mpr hf
  simp only [Function.comp_def, Measure.volume_eq_prod] at hi
  rw [← spatialPlaneCoordEquiv_measurePreserving.integral_comp' f,
    Measure.volume_eq_prod, integral_prod _ hi]
  simp_rw [spatialPlaneCoordEquiv_apply]

private def euclideanPlaneEquiv : EuclideanSpace ℝ (Fin 2) ≃ᵐ Plane :=
  { WithLp.equiv 2 _ with
    measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin 2 => ℝ)).measurable
    measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin 2 => ℝ)).measurable }

/-- Polar integration in the actual product Lebesgue measure on the
transverse plane. -/
theorem integral_plane_radial (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ) :
    (∫ x in {x : Plane | (∑ i : Fin 2, x i ^ 2) ≤ R ^ 2},
      f (∑ i : Fin 2, x i ^ 2)) =
      2 * Real.pi * ∫ r in (0 : ℝ)..R, r * f (r ^ 2) := by
  let s := {x : Plane | (∑ i : Fin 2, x i ^ 2) ≤ R ^ 2}
  have hs : MeasurableSet s := by
    apply isClosed_le ?_ continuous_const |>.measurableSet
    fun_prop
  have he (x : EuclideanSpace ℝ (Fin 2)) :
      ∑ i : Fin 2, (euclideanPlaneEquiv x) i ^ 2 = ‖x‖ ^ 2 := by
    simp [euclideanPlaneEquiv, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  have hem : MeasurePreserving euclideanPlaneEquiv :=
    PiLp.volume_preserving_equiv (Fin 2)
  rw [← integral_indicator hs, ← hem.integral_comp']
  have hi (x : EuclideanSpace ℝ (Fin 2)) :
      s.indicator (fun x => f (∑ i : Fin 2, x i ^ 2)) (euclideanPlaneEquiv x) =
        (Icc 0 R).indicator (fun r => f (r ^ 2)) ‖x‖ := by
    have hx : euclideanPlaneEquiv x ∈ s ↔ ‖x‖ ∈ Icc 0 R := by
      dsimp [s]
      rw [he, sq_le_sq₀ (norm_nonneg _) hR]
      simp [norm_nonneg]
    simp only [Set.indicator, hx, he]
  simp_rw [hi]
  rw [integral_fun_norm_addHaar]
  have hv : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real
      (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two,
      ENNReal.toReal_ofReal, Real.pi_pos.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, hv, Nat.reduceSub,
    nsmul_eq_mul, smul_eq_mul]
  have hh : (∫ r in Ioi (0 : ℝ), r *
      (Icc 0 R).indicator (fun r => f (r ^ 2)) r) =
      ∫ r in (0 : ℝ)..R, r * f (r ^ 2) := by
    simp_rw [← Set.indicator_mul_right (Icc 0 R) (fun r => r)
      (fun r => f (r ^ 2))]
    rw [integral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc]
    have hset : Icc 0 R ∩ Ioi (0 : ℝ) = Ioc 0 R := by
      ext r
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩⟩
    rw [hset, intervalIntegral.integral_of_le hR]
  simp only [pow_one]
  rw [hh]
  ring

/-- A transverse annulus, parametrized by its squared radii. -/
def planeSqShell (L A : ℝ) : Set Plane :=
  {p | L < ∑ i : Fin 2, p i ^ 2 ∧ ∑ i : Fin 2, p i ^ 2 ≤ A}

/-- Exact transverse coarea formula.  The factor is `π` because the coarea
coordinate is squared radius. -/
theorem integral_plane_sqShell (L A : ℝ) (hL : 0 ≤ L) (hLA : L ≤ A)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in planeSqShell L A,
      f (A - ∑ i : Fin 2, p i ^ 2)) =
      Real.pi * ∫ w in (0 : ℝ)..A - L, f w := by
  let rL := Real.sqrt L
  let rA := Real.sqrt A
  let diskL := {p : Plane | ∑ i : Fin 2, p i ^ 2 ≤ rL ^ 2}
  let diskA := {p : Plane | ∑ i : Fin 2, p i ^ 2 ≤ rA ^ 2}
  let g := fun p : Plane => f (A - ∑ i : Fin 2, p i ^ 2)
  have hA : 0 ≤ A := hL.trans hLA
  have hrL : 0 ≤ rL := Real.sqrt_nonneg _
  have hrA : 0 ≤ rA := Real.sqrt_nonneg _
  have hrLsq : rL ^ 2 = L := Real.sq_sqrt hL
  have hrAsq : rA ^ 2 = A := Real.sq_sqrt hA
  have hmL : MeasurableSet diskL := by
    dsimp [diskL]
    apply isClosed_le ?_ continuous_const |>.measurableSet
    fun_prop
  have hsub : diskL ⊆ diskA := by
    intro p hp
    dsimp [diskL] at hp
    dsimp [diskA]
    rw [hrLsq] at hp
    rw [hrAsq]
    exact hp.trans hLA
  have hdiff : diskA \ diskL = planeSqShell L A := by
    ext p
    simp only [mem_diff, mem_setOf_eq, planeSqShell, diskA, diskL,
      not_le, hrLsq, hrAsq]
    tauto
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hbox : diskA ⊆ Icc (fun _ : Fin 2 => -rA) (fun _ => rA) := by
    intro p hp
    have hs : ∑ i : Fin 2, p i ^ 2 ≤ rA ^ 2 := hp
    constructor <;> intro i
    · have hi : p i ^ 2 ≤ rA ^ 2 :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (p j))
          (Finset.mem_univ i)).trans hs
      exact (abs_le.mp ((sq_le_sq₀ (abs_nonneg _) hrA).mp
        (by simpa only [sq_abs] using hi))).1
    · have hi : p i ^ 2 ≤ rA ^ 2 :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (p j))
          (Finset.mem_univ i)).trans hs
      exact (abs_le.mp ((sq_le_sq₀ (abs_nonneg _) hrA).mp
        (by simpa only [sq_abs] using hi))).2
  have hiA : IntegrableOn g diskA := hg.integrableOn_Icc.mono_set hbox
  rw [← hdiff, integral_diff hmL hiA hsub]
  change (∫ p in diskA, f (A - ∑ i : Fin 2, p i ^ 2)) -
      (∫ p in diskL, f (A - ∑ i : Fin 2, p i ^ 2)) = _
  rw [integral_plane_radial rA hrA (fun s => f (A - s)),
    integral_plane_radial rL hrL (fun s => f (A - s))]
  let h := fun r : ℝ => r * f (A - r ^ 2)
  have hh : Continuous h := by dsimp [h]; fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hh.intervalIntegrable (μ := volume) (0 : ℝ) rL)
    (hh.intervalIntegrable (μ := volume) rL rA)
  have hrad : (∫ r in (0 : ℝ)..rA, h r) -
      (∫ r in (0 : ℝ)..rL, h r) = ∫ r in rL..rA, h r := by
    linarith
  change 2 * Real.pi * (∫ r in (0 : ℝ)..rA, h r) -
      2 * Real.pi * (∫ r in (0 : ℝ)..rL, h r) = _
  rw [← mul_sub, hrad]
  have hcv := intervalIntegral.integral_comp_mul_deriv
    (a := rL) (b := rA) (f := fun r : ℝ => A - r ^ 2)
    (f' := fun r => -2 * r) (g := f)
    (fun r _ => by
      convert (hasDerivAt_const r A).sub ((hasDerivAt_id r).pow 2) using 1
      simp only [id_eq]
      ring)
    (by fun_prop) hf
  simp only [Function.comp_apply] at hcv
  rw [hrLsq, hrAsq] at hcv
  have hleft : (∫ r in rL..rA, f (A - r ^ 2) * (-2 * r)) =
      -2 * ∫ r in rL..rA, h r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [h]
    ring
  rw [hleft, sub_self] at hcv
  rw [intervalIntegral.integral_symm (a := 0) (b := A - L)] at hcv
  have hscale : 2 * (∫ r in rL..rA, h r) =
      ∫ w in (0 : ℝ)..A - L, f w := by linarith
  calc
    2 * Real.pi * (∫ r in rL..rA, h r) =
        Real.pi * (2 * ∫ r in rL..rA, h r) := by ring
    _ = _ := by rw [hscale]

private theorem plane_sq_boundary_null (R : ℝ) (hR : 0 ≤ R) :
    volume {p : Plane | ∑ i : Fin 2, p i ^ 2 = R ^ 2} = 0 := by
  have hm : MeasurableSet {p : Plane | ∑ i : Fin 2, p i ^ 2 = R ^ 2} := by
    apply isClosed_eq ?_ continuous_const |>.measurableSet
    fun_prop
  rw [← (PiLp.volume_preserving_equiv (Fin 2)).measure_preimage
    hm.nullMeasurableSet]
  have he (x : EuclideanSpace ℝ (Fin 2)) :
      ∑ i : Fin 2, ((WithLp.equiv 2 (Fin 2 → ℝ)) x i) ^ 2 = ‖x‖ ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  have hpre : (WithLp.equiv 2 (Fin 2 → ℝ)) ⁻¹'
      {p : Plane | ∑ i : Fin 2, p i ^ 2 = R ^ 2} = Metric.sphere 0 R := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, Metric.mem_sphere, dist_zero_right]
    rw [he]
    exact sq_eq_sq₀ (norm_nonneg _) hR
  rw [hpre, Measure.addHaar_sphere]

/-- A transverse open disk expressed in the proper-square coordinate. -/
theorem integral_plane_sqBall_shift (L A : ℝ) (hLA : L ≤ A)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in {p : Plane | ∑ i : Fin 2, p i ^ 2 < A - L},
      f (A - ∑ i : Fin 2, p i ^ 2)) =
      Real.pi * ∫ w in L..A, f w := by
  let R := Real.sqrt (A - L)
  have hAL : 0 ≤ A - L := sub_nonneg.mpr hLA
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = A - L := Real.sq_sqrt hAL
  have hae : {p : Plane | ∑ i : Fin 2, p i ^ 2 < A - L} =ᶠ[ae volume]
      {p : Plane | ∑ i : Fin 2, p i ^ 2 ≤ R ^ 2} := by
    apply ae_eq_set.mpr
    constructor
    · have hsub : {p : Plane | ∑ i : Fin 2, p i ^ 2 < A - L} ⊆
          {p : Plane | ∑ i : Fin 2, p i ^ 2 ≤ R ^ 2} := by
        intro p hp
        simpa only [mem_setOf_eq, hRsq] using hp.le
      rw [diff_eq_empty.mpr hsub, measure_empty]
    · apply measure_mono_null
        (t := {p : Plane | ∑ i : Fin 2, p i ^ 2 = R ^ 2})
        (fun p hp => ?_) (plane_sq_boundary_null R hR)
      simp only [mem_diff, mem_setOf_eq] at hp ⊢
      rw [hRsq] at hp ⊢
      exact le_antisymm hp.1 (not_lt.mp hp.2)
  rw [setIntegral_congr_set hae,
    integral_plane_radial R hR (fun s => f (A - s))]
  let h := fun r : ℝ => r * f (A - r ^ 2)
  have hcv := intervalIntegral.integral_comp_mul_deriv
    (a := 0) (b := R) (f := fun r : ℝ => A - r ^ 2)
    (f' := fun r => -2 * r) (g := f)
    (fun r _ => by
      convert (hasDerivAt_const r A).sub ((hasDerivAt_id r).pow 2) using 1
      simp only [id_eq]
      ring)
    (by fun_prop) hf
  simp only [Function.comp_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at hcv
  rw [hRsq, show A - (A - L) = L by ring] at hcv
  have hleft : (∫ r in (0 : ℝ)..R, f (A - r ^ 2) * (-2 * r)) =
      -2 * ∫ r in (0 : ℝ)..R, h r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [h]
    ring
  rw [hleft, intervalIntegral.integral_symm L A] at hcv
  change 2 * Real.pi * (∫ r in (0 : ℝ)..R, h r) = _
  have hscale : 2 * (∫ r in (0 : ℝ)..R, h r) =
      ∫ w in L..A, f w := by linarith
  calc
    2 * Real.pi * (∫ r in (0 : ℝ)..R, h r) =
        Real.pi * (2 * ∫ r in (0 : ℝ)..R, h r) := by ring
    _ = _ := by rw [hscale]

end BoundaryDraft
