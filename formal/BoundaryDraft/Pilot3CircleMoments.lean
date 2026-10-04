import BoundaryDraft.Pilot3NullCoordinates

/-!
# Linear and quadratic moments of the full polar circle

The angular measure used by the overlap coordinates is the actual polar
measure `volume.toSphere`.  We first prove that this measure is preserved by
linear isometries, and then use coordinate reflections and permutations to
compute its first two moments.  The final theorem packages the quadratic
moment as the trace of a continuous bilinear map.
-/

open MeasureTheory Set Metric
open scoped BigOperators Topology InnerProductSpace Pointwise

noncomputable section
namespace BoundaryDraft

/-- Sector volumes are invariant under actual plane isometries. -/
private theorem pilot3_volume_sector_isometry (e : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space)
    (S : Set Pilot3Space) : volume (Ioo (0 : ℝ) 1 • (e '' S)) = volume (Ioo (0 : ℝ) 1 • S) := by
  have he : Ioo (0 : ℝ) 1 • (e '' S) = e '' (Ioo (0 : ℝ) 1 • S) := by
    ext x
    simp only [Set.mem_smul, mem_image]
    constructor
    · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨r • y, ⟨r, hr, y, hy, rfl⟩, e.map_smul r y⟩
    · rintro ⟨_, ⟨r, hr, y, hy, rfl⟩, rfl⟩
      exact ⟨r, hr, e y, ⟨y, hy, rfl⟩, (e.map_smul r y).symm⟩
  rw [he]
  have hm := e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding
    (e '' (Ioo (0 : ℝ) 1 • S))
  simpa only [e.injective.preimage_image] using hm.symm

/-- A linear isometry of the ambient plane, restricted to the unit
sphere. -/
def pilot3CircleEquiv (e : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space) :
    Pilot3Circle ≃ᵐ Pilot3Circle where
  toFun ω := ⟨e ω.val, mem_sphere_zero_iff_norm.mpr (by
    rw [e.norm_map]
    exact mem_sphere_zero_iff_norm.mp ω.property)⟩
  invFun ω := ⟨e.symm ω.val, mem_sphere_zero_iff_norm.mpr (by
    rw [e.symm.norm_map]
    exact mem_sphere_zero_iff_norm.mp ω.property)⟩
  left_inv ω := Subtype.ext (e.symm_apply_apply ω.val)
  right_inv ω := Subtype.ext (e.apply_symm_apply ω.val)
  measurable_toFun := ((e.continuous.comp continuous_subtype_val).subtype_mk _).measurable
  measurable_invFun := ((e.symm.continuous.comp continuous_subtype_val).subtype_mk _).measurable

@[simp]
theorem pilot3CircleEquiv_apply_val (e : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space)
    (ω : Pilot3Circle) : (pilot3CircleEquiv e ω).val = e ω.val := rfl

@[simp]
theorem pilot3CircleEquiv_symm_apply_val (e : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space)
    (ω : Pilot3Circle) : ((pilot3CircleEquiv e).symm ω).val = e.symm ω.val := rfl

/-- The actual polar-circle measure is invariant under every ambient linear
isometry.  This is derived from its radial-sector construction, rather than
assumed as a symmetry property. -/
theorem pilot3CircleMeasure_preserving_linearIsometry
    (e : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space) :
    MeasurePreserving (pilot3CircleEquiv e) pilot3CircleMeasure pilot3CircleMeasure := by
  refine ⟨(pilot3CircleEquiv e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (pilot3CircleEquiv e).measurable hs]
  have hpre : MeasurableSet ((pilot3CircleEquiv e) ⁻¹' s) :=
    hs.preimage (pilot3CircleEquiv e).measurable
  have himage :
      ((Subtype.val : Pilot3Circle → Pilot3Space) '' ((pilot3CircleEquiv e) ⁻¹' s)) =
        e.symm '' ((Subtype.val : Pilot3Circle → Pilot3Space) '' s) := by
    ext x
    constructor
    · rintro ⟨ω, hω, rfl⟩
      refine ⟨e ω.val, ⟨pilot3CircleEquiv e ω, hω, rfl⟩, ?_⟩
      exact e.symm_apply_apply ω.val
    · rintro ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      refine ⟨(pilot3CircleEquiv e).symm ω, ?_, ?_⟩
      · simpa
      · rfl
  rw [pilot3CircleMeasure, Measure.toSphere_apply' _ hpre,
    Measure.toSphere_apply' _ hs, himage, pilot3_volume_sector_isometry e.symm]

/-- Permute the two Euclidean coordinates. -/
def pilot3CoordinatePermutation (σ : Fin 2 ≃ Fin 2) :
    Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

@[simp]
theorem pilot3CoordinatePermutation_apply (σ : Fin 2 ≃ Fin 2)
    (x : Pilot3Space) (i : Fin 2) :
    pilot3CoordinatePermutation σ x i = x (σ.symm i) := rfl

/-- Reflect one Euclidean coordinate and leave the other coordinate fixed. -/
def pilot3CoordinateReflection (i : Fin 2) :
    Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin 2 =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp]
theorem pilot3CoordinateReflection_apply (i : Fin 2)
    (x : Pilot3Space) (j : Fin 2) :
    pilot3CoordinateReflection i x j = if j = i then -x j else x j := by
  by_cases h : j = i
  · subst j
    simp [pilot3CoordinateReflection]
  · simp [pilot3CoordinateReflection, h]

/-- Coordinate permutations preserve the actual polar-circle measure. -/
theorem pilot3CircleMeasure_preserving_permutation (σ : Fin 2 ≃ Fin 2) :
    MeasurePreserving (pilot3CircleEquiv (pilot3CoordinatePermutation σ))
      pilot3CircleMeasure pilot3CircleMeasure :=
  pilot3CircleMeasure_preserving_linearIsometry (pilot3CoordinatePermutation σ)

/-- Single-coordinate reflections preserve the actual polar-circle measure. -/
theorem pilot3CircleMeasure_preserving_reflection (i : Fin 2) :
    MeasurePreserving (pilot3CircleEquiv (pilot3CoordinateReflection i))
      pilot3CircleMeasure pilot3CircleMeasure :=
  pilot3CircleMeasure_preserving_linearIsometry (pilot3CoordinateReflection i)

private theorem continuous_integrable_pilot3Circle {f : Pilot3Circle → ℝ}
    (hf : Continuous f) : Integrable f pilot3CircleMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Absolute integrability of every directional linear observable. -/
theorem integrable_pilot3Circle_inner (u : Pilot3Space) :
    Integrable (fun ω : Pilot3Circle => ⟪u, ω.val⟫_ℝ) pilot3CircleMeasure := by
  apply continuous_integrable_pilot3Circle
  exact continuous_const.inner continuous_subtype_val

/-- Absolute integrability of every product of two coordinate observables. -/
theorem integrable_pilot3Circle_coord_mul (i j : Fin 2) :
    Integrable (fun ω : Pilot3Circle => ω.val i * ω.val j) pilot3CircleMeasure := by
  apply continuous_integrable_pilot3Circle
  exact ((continuous_apply i).comp continuous_subtype_val).mul
    ((continuous_apply j).comp continuous_subtype_val)

/-- Absolute integrability of every product of two directional observables. -/
theorem integrable_pilot3Circle_inner_mul (u v : Pilot3Space) :
    Integrable (fun ω : Pilot3Circle => ⟪u, ω.val⟫_ℝ * ⟪v, ω.val⟫_ℝ)
      pilot3CircleMeasure := by
  apply continuous_integrable_pilot3Circle
  exact (continuous_const.inner continuous_subtype_val).mul
    (continuous_const.inner continuous_subtype_val)

/-- Absolute integrability of a continuous bilinear quadratic observable. -/
theorem integrable_pilot3Circle_bilinear
    (B : Pilot3Space →L[ℝ] Pilot3Space →L[ℝ] ℝ) :
    Integrable (fun ω : Pilot3Circle => B ω.val ω.val) pilot3CircleMeasure := by
  apply continuous_integrable_pilot3Circle
  exact (B.continuous.comp continuous_subtype_val).clm_apply continuous_subtype_val

/-- Every directional first moment on the full polar circle vanishes. -/
theorem integral_pilot3Circle_inner (u : Pilot3Space) :
    (∫ ω : Pilot3Circle, ⟪u, ω.val⟫_ℝ ∂pilot3CircleMeasure) = 0 := by
  let e : Pilot3Space ≃ₗᵢ[ℝ] Pilot3Space := LinearIsometryEquiv.neg ℝ
  have h := (pilot3CircleMeasure_preserving_linearIsometry e).integral_comp
    (pilot3CircleEquiv e).measurableEmbedding (fun ω : Pilot3Circle => ⟪u, ω.val⟫_ℝ)
  have hneg :
      (∫ ω : Pilot3Circle, -⟪u, ω.val⟫_ℝ ∂pilot3CircleMeasure) =
        ∫ ω : Pilot3Circle, ⟪u, ω.val⟫_ℝ ∂pilot3CircleMeasure := by
    simpa [e] using h
  rw [integral_neg] at hneg
  linarith

private theorem integral_pilot3Circle_coord_mul_of_ne {i j : Fin 2} (hij : i ≠ j) :
    (∫ ω : Pilot3Circle, ω.val i * ω.val j ∂pilot3CircleMeasure) = 0 := by
  have h := (pilot3CircleMeasure_preserving_reflection i).integral_comp
    (pilot3CircleEquiv (pilot3CoordinateReflection i)).measurableEmbedding
    (fun ω : Pilot3Circle => ω.val i * ω.val j)
  have hneg :
      (∫ ω : Pilot3Circle, -(ω.val i * ω.val j) ∂pilot3CircleMeasure) =
        ∫ ω : Pilot3Circle, ω.val i * ω.val j ∂pilot3CircleMeasure := by
    simpa [hij, hij.symm] using h
  rw [integral_neg] at hneg
  linarith

private theorem integral_pilot3Circle_coord_sq_eq (i j : Fin 2) :
    (∫ ω : Pilot3Circle, ω.val i ^ 2 ∂pilot3CircleMeasure) =
      ∫ ω : Pilot3Circle, ω.val j ^ 2 ∂pilot3CircleMeasure := by
  let σ : Fin 2 ≃ Fin 2 := Equiv.swap i j
  have h := (pilot3CircleMeasure_preserving_permutation σ).integral_comp
    (pilot3CircleEquiv (pilot3CoordinatePermutation σ)).measurableEmbedding
    (fun ω : Pilot3Circle => ω.val i ^ 2)
  have hswap : σ.symm i = j := by
    change (Equiv.swap i j) i = j
    exact Equiv.swap_apply_left i j
  simp only [pilot3CircleEquiv_apply_val, pilot3CoordinatePermutation_apply] at h
  rw [hswap] at h
  exact h.symm

private theorem integral_pilot3Circle_coord_sq (i : Fin 2) :
    (∫ ω : Pilot3Circle, ω.val i ^ 2 ∂pilot3CircleMeasure) =
      Real.pi := by
  have hnorm (ω : Pilot3Circle) : ∑ j : Fin 2, ω.val j ^ 2 = 1 := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) ω.val
    rw [show ‖ω.val‖ = 1 from mem_sphere_zero_iff_norm.mp ω.property] at h
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm
  have hsum :
      (∑ j : Fin 2, ∫ ω : Pilot3Circle, ω.val j ^ 2 ∂pilot3CircleMeasure) =
        2 * Real.pi := by
    calc
      _ = ∫ ω : Pilot3Circle, ∑ j : Fin 2, ω.val j ^ 2 ∂pilot3CircleMeasure := by
        rw [integral_finset_sum _ (fun j _ => by
          simpa only [pow_two] using integrable_pilot3Circle_coord_mul j j)]
      _ = ∫ _ω : Pilot3Circle, (1 : ℝ) ∂pilot3CircleMeasure := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hnorm ω
      _ = pilot3CircleMeasure.real univ := by
        rw [integral_const, smul_eq_mul, mul_one]
      _ = 2 * Real.pi := pilot3Circle_mass
  have heq (j : Fin 2) :
      (∫ ω : Pilot3Circle, ω.val j ^ 2 ∂pilot3CircleMeasure) =
        ∫ ω : Pilot3Circle, ω.val i ^ 2 ∂pilot3CircleMeasure :=
    integral_pilot3Circle_coord_sq_eq j i
  simp_rw [heq] at hsum
  norm_num at hsum ⊢
  linarith

/-- The coordinate covariance matrix is `pi` times the identity. -/
theorem integral_pilot3Circle_coord_mul (i j : Fin 2) :
    (∫ ω : Pilot3Circle, ω.val i * ω.val j ∂pilot3CircleMeasure) =
      if i = j then Real.pi else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [if_pos rfl, pow_two] using integral_pilot3Circle_coord_sq i
  · rw [if_neg hij]
    exact integral_pilot3Circle_coord_mul_of_ne hij

private theorem integral_pilot3Circle_quadratic_coordinates (a : Fin 2 → Fin 2 → ℝ) :
    (∫ ω : Pilot3Circle, ∑ i : Fin 2, ∑ j : Fin 2,
        a i j * (ω.val i * ω.val j) ∂pilot3CircleMeasure) =
      (Real.pi) * ∑ i : Fin 2, a i i := by
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_pilot3Circle_coord_mul i j).const_mul (a i j))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (integrable_pilot3Circle_coord_mul _ j).const_mul (a _ j)), integral_const_mul,
    integral_pilot3Circle_coord_mul]
  calc
    (∑ i : Fin 2, ∑ j : Fin 2,
        a i j * (if i = j then Real.pi else 0)) =
        ∑ i : Fin 2, a i i * (Real.pi) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    _ = (Real.pi) * ∑ i : Fin 2, a i i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The second directional moment of the full sphere. -/
theorem integral_pilot3Circle_inner_mul (u v : Pilot3Space) :
    (∫ ω : Pilot3Circle, ⟪u, ω.val⟫_ℝ * ⟪v, ω.val⟫_ℝ
      ∂pilot3CircleMeasure) =
      (Real.pi) * ⟪u, v⟫_ℝ := by
  have hpoint (ω : Pilot3Circle) :
      ⟪u, ω.val⟫_ℝ * ⟪v, ω.val⟫_ℝ =
        ∑ i : Fin 2, ∑ j : Fin 2, (u i * v j) * (ω.val i * ω.val j) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_pilot3Circle_quadratic_coordinates]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The circle integral of a continuous bilinear quadratic observable is
`pi` times its trace in the standard Euclidean orthonormal basis. -/
theorem integral_pilot3Circle_bilinear
    (B : Pilot3Space →L[ℝ] Pilot3Space →L[ℝ] ℝ) :
    (∫ ω : Pilot3Circle, B ω.val ω.val ∂pilot3CircleMeasure) =
      (Real.pi) * ∑ i : Fin 2,
        B (EuclideanSpace.basisFun (Fin 2) ℝ i)
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hexpand (x y : Pilot3Space) :
      B x y = ∑ i : Fin 2, ∑ j : Fin 2,
        (B (e i) (e j)) * (x i * y j) := by
    conv_lhs =>
      rw [← e.toBasis.sum_repr x, ← e.toBasis.sum_repr y]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, EuclideanSpace.basisFun_repr, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [e]
    ring
  calc
    (∫ ω : Pilot3Circle, B ω.val ω.val ∂pilot3CircleMeasure) =
        ∫ ω : Pilot3Circle, ∑ i : Fin 2, ∑ j : Fin 2,
          (B (e i) (e j)) * (ω.val i * ω.val j) ∂pilot3CircleMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hexpand ω.val ω.val)
    _ = (Real.pi) * ∑ i : Fin 2, B (e i) (e i) :=
      integral_pilot3Circle_quadratic_coordinates _
    _ = _ := rfl

end BoundaryDraft
