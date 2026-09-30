import BoundaryDraft.OverlapCoordinates
import BoundaryDraft.SphereSurface

/-!
# Linear and quadratic moments of the overlap sphere

The angular measure used by the overlap coordinates is the actual polar
measure `volume.toSphere`.  We first prove that this measure is preserved by
linear isometries, and then use coordinate reflections and permutations to
compute its first two moments.  The final theorem packages the quadratic
moment as the trace of a continuous bilinear map.
-/

open MeasureTheory Set Metric
open scoped BigOperators Topology InnerProductSpace

noncomputable section
namespace BoundaryDraft

/-- A linear isometry of the ambient three-space, restricted to the unit
sphere. -/
def overlapSphereEquiv (e : OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace) :
    OverlapSphere ≃ᵐ OverlapSphere where
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
theorem overlapSphereEquiv_apply_val (e : OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace)
    (ω : OverlapSphere) : (overlapSphereEquiv e ω).val = e ω.val := rfl

@[simp]
theorem overlapSphereEquiv_symm_apply_val (e : OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace)
    (ω : OverlapSphere) : ((overlapSphereEquiv e).symm ω).val = e.symm ω.val := rfl

/-- The actual overlap-sphere measure is invariant under every ambient linear
isometry.  This is derived from its radial-sector construction, rather than
assumed as a symmetry property. -/
theorem overlapSphereMeasure_preserving_linearIsometry
    (e : OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace) :
    MeasurePreserving (overlapSphereEquiv e) overlapSphereMeasure overlapSphereMeasure := by
  refine ⟨(overlapSphereEquiv e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (overlapSphereEquiv e).measurable hs]
  have hpre : MeasurableSet ((overlapSphereEquiv e) ⁻¹' s) :=
    hs.preimage (overlapSphereEquiv e).measurable
  have himage :
      ((Subtype.val : OverlapSphere → OverlapSpace) '' ((overlapSphereEquiv e) ⁻¹' s)) =
        e.symm '' ((Subtype.val : OverlapSphere → OverlapSpace) '' s) := by
    ext x
    constructor
    · rintro ⟨ω, hω, rfl⟩
      refine ⟨e ω.val, ⟨overlapSphereEquiv e ω, hω, rfl⟩, ?_⟩
      exact e.symm_apply_apply ω.val
    · rintro ⟨_, ⟨ω, hω, rfl⟩, rfl⟩
      refine ⟨(overlapSphereEquiv e).symm ω, ?_, ?_⟩
      · simpa
      · rfl
  rw [overlapSphereMeasure, Measure.toSphere_apply' _ hpre,
    Measure.toSphere_apply' _ hs, himage, volume_sphere_sector_isometry e.symm]

/-- Permute the three Euclidean coordinates. -/
def overlapCoordinatePermutation (σ : Fin 3 ≃ Fin 3) :
    OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

@[simp]
theorem overlapCoordinatePermutation_apply (σ : Fin 3 ≃ Fin 3)
    (x : OverlapSpace) (i : Fin 3) :
    overlapCoordinatePermutation σ x i = x (σ.symm i) := rfl

/-- Reflect one Euclidean coordinate and leave the other two fixed. -/
def overlapCoordinateReflection (i : Fin 3) :
    OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin 3 =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp]
theorem overlapCoordinateReflection_apply (i : Fin 3)
    (x : OverlapSpace) (j : Fin 3) :
    overlapCoordinateReflection i x j = if j = i then -x j else x j := by
  by_cases h : j = i
  · subst j
    simp [overlapCoordinateReflection]
  · simp [overlapCoordinateReflection, h]

/-- Coordinate permutations preserve the actual overlap-sphere measure. -/
theorem overlapSphereMeasure_preserving_permutation (σ : Fin 3 ≃ Fin 3) :
    MeasurePreserving (overlapSphereEquiv (overlapCoordinatePermutation σ))
      overlapSphereMeasure overlapSphereMeasure :=
  overlapSphereMeasure_preserving_linearIsometry (overlapCoordinatePermutation σ)

/-- Single-coordinate reflections preserve the actual overlap-sphere measure. -/
theorem overlapSphereMeasure_preserving_reflection (i : Fin 3) :
    MeasurePreserving (overlapSphereEquiv (overlapCoordinateReflection i))
      overlapSphereMeasure overlapSphereMeasure :=
  overlapSphereMeasure_preserving_linearIsometry (overlapCoordinateReflection i)

private theorem continuous_integrable_overlapSphere {f : OverlapSphere → ℝ}
    (hf : Continuous f) : Integrable f overlapSphereMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Absolute integrability of every directional linear observable. -/
theorem integrable_overlapSphere_inner (u : JointSpace) :
    Integrable (fun ω : OverlapSphere => ⟪u, ω.val⟫_ℝ) overlapSphereMeasure := by
  apply continuous_integrable_overlapSphere
  exact continuous_const.inner continuous_subtype_val

/-- Absolute integrability of every product of two coordinate observables. -/
theorem integrable_overlapSphere_coord_mul (i j : Fin 3) :
    Integrable (fun ω : OverlapSphere => ω.val i * ω.val j) overlapSphereMeasure := by
  apply continuous_integrable_overlapSphere
  exact ((continuous_apply i).comp continuous_subtype_val).mul
    ((continuous_apply j).comp continuous_subtype_val)

/-- Absolute integrability of every product of two directional observables. -/
theorem integrable_overlapSphere_inner_mul (u v : JointSpace) :
    Integrable (fun ω : OverlapSphere => ⟪u, ω.val⟫_ℝ * ⟪v, ω.val⟫_ℝ)
      overlapSphereMeasure := by
  apply continuous_integrable_overlapSphere
  exact (continuous_const.inner continuous_subtype_val).mul
    (continuous_const.inner continuous_subtype_val)

/-- Absolute integrability of a continuous bilinear quadratic observable. -/
theorem integrable_overlapSphere_bilinear
    (B : JointSpace →L[ℝ] JointSpace →L[ℝ] ℝ) :
    Integrable (fun ω : OverlapSphere => B ω.val ω.val) overlapSphereMeasure := by
  apply continuous_integrable_overlapSphere
  exact (B.continuous.comp continuous_subtype_val).clm_apply continuous_subtype_val

/-- Every directional first moment on the full overlap sphere vanishes. -/
theorem integral_overlapSphere_inner (u : JointSpace) :
    (∫ ω : OverlapSphere, ⟪u, ω.val⟫_ℝ ∂overlapSphereMeasure) = 0 := by
  let e : OverlapSpace ≃ₗᵢ[ℝ] OverlapSpace := LinearIsometryEquiv.neg ℝ
  have h := (overlapSphereMeasure_preserving_linearIsometry e).integral_comp
    (overlapSphereEquiv e).measurableEmbedding (fun ω : OverlapSphere => ⟪u, ω.val⟫_ℝ)
  have hneg :
      (∫ ω : OverlapSphere, -⟪u, ω.val⟫_ℝ ∂overlapSphereMeasure) =
        ∫ ω : OverlapSphere, ⟪u, ω.val⟫_ℝ ∂overlapSphereMeasure := by
    simpa [e] using h
  rw [integral_neg] at hneg
  linarith

private theorem integral_overlapSphere_coord_mul_of_ne {i j : Fin 3} (hij : i ≠ j) :
    (∫ ω : OverlapSphere, ω.val i * ω.val j ∂overlapSphereMeasure) = 0 := by
  have h := (overlapSphereMeasure_preserving_reflection i).integral_comp
    (overlapSphereEquiv (overlapCoordinateReflection i)).measurableEmbedding
    (fun ω : OverlapSphere => ω.val i * ω.val j)
  have hneg :
      (∫ ω : OverlapSphere, -(ω.val i * ω.val j) ∂overlapSphereMeasure) =
        ∫ ω : OverlapSphere, ω.val i * ω.val j ∂overlapSphereMeasure := by
    simpa [hij, hij.symm] using h
  rw [integral_neg] at hneg
  linarith

private theorem integral_overlapSphere_coord_sq_eq (i j : Fin 3) :
    (∫ ω : OverlapSphere, ω.val i ^ 2 ∂overlapSphereMeasure) =
      ∫ ω : OverlapSphere, ω.val j ^ 2 ∂overlapSphereMeasure := by
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap i j
  have h := (overlapSphereMeasure_preserving_permutation σ).integral_comp
    (overlapSphereEquiv (overlapCoordinatePermutation σ)).measurableEmbedding
    (fun ω : OverlapSphere => ω.val i ^ 2)
  have hswap : σ.symm i = j := by
    change (Equiv.swap i j) i = j
    exact Equiv.swap_apply_left i j
  simp only [overlapSphereEquiv_apply_val, overlapCoordinatePermutation_apply] at h
  rw [hswap] at h
  exact h.symm

private theorem integral_overlapSphere_coord_sq (i : Fin 3) :
    (∫ ω : OverlapSphere, ω.val i ^ 2 ∂overlapSphereMeasure) =
      4 * Real.pi / 3 := by
  have hnorm (ω : OverlapSphere) : ∑ j : Fin 3, ω.val j ^ 2 = 1 := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) ω.val
    rw [show ‖ω.val‖ = 1 from mem_sphere_zero_iff_norm.mp ω.property] at h
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm
  have hsum :
      (∑ j : Fin 3, ∫ ω : OverlapSphere, ω.val j ^ 2 ∂overlapSphereMeasure) =
        4 * Real.pi := by
    calc
      _ = ∫ ω : OverlapSphere, ∑ j : Fin 3, ω.val j ^ 2 ∂overlapSphereMeasure := by
        rw [integral_finset_sum _ (fun j _ => by
          simpa only [pow_two] using integrable_overlapSphere_coord_mul j j)]
      _ = ∫ _ω : OverlapSphere, (1 : ℝ) ∂overlapSphereMeasure := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hnorm ω
      _ = overlapSphereMeasure.real univ := by
        rw [integral_const, smul_eq_mul, mul_one]
      _ = 4 * Real.pi := overlapSphere_mass
  have heq (j : Fin 3) :
      (∫ ω : OverlapSphere, ω.val j ^ 2 ∂overlapSphereMeasure) =
        ∫ ω : OverlapSphere, ω.val i ^ 2 ∂overlapSphereMeasure :=
    integral_overlapSphere_coord_sq_eq j i
  simp_rw [heq] at hsum
  norm_num at hsum ⊢
  linarith

/-- The coordinate covariance matrix is `(4 * pi / 3)` times the identity. -/
theorem integral_overlapSphere_coord_mul (i j : Fin 3) :
    (∫ ω : OverlapSphere, ω.val i * ω.val j ∂overlapSphereMeasure) =
      if i = j then 4 * Real.pi / 3 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa only [if_pos rfl, pow_two] using integral_overlapSphere_coord_sq i
  · rw [if_neg hij]
    exact integral_overlapSphere_coord_mul_of_ne hij

private theorem integral_overlapSphere_quadratic_coordinates (a : Fin 3 → Fin 3 → ℝ) :
    (∫ ω : OverlapSphere, ∑ i : Fin 3, ∑ j : Fin 3,
        a i j * (ω.val i * ω.val j) ∂overlapSphereMeasure) =
      (4 * Real.pi / 3) * ∑ i : Fin 3, a i i := by
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_overlapSphere_coord_mul i j).const_mul (a i j))]
  simp_rw [integral_finset_sum _ (fun j _ =>
    (integrable_overlapSphere_coord_mul _ j).const_mul (a _ j)), integral_const_mul,
    integral_overlapSphere_coord_mul]
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
        a i j * (if i = j then 4 * Real.pi / 3 else 0)) =
        ∑ i : Fin 3, a i i * (4 * Real.pi / 3) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    _ = (4 * Real.pi / 3) * ∑ i : Fin 3, a i i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The second directional moment of the full sphere. -/
theorem integral_overlapSphere_inner_mul (u v : JointSpace) :
    (∫ ω : OverlapSphere, ⟪u, ω.val⟫_ℝ * ⟪v, ω.val⟫_ℝ
      ∂overlapSphereMeasure) =
      (4 * Real.pi / 3) * ⟪u, v⟫_ℝ := by
  have hpoint (ω : OverlapSphere) :
      ⟪u, ω.val⟫_ℝ * ⟪v, ω.val⟫_ℝ =
        ∑ i : Fin 3, ∑ j : Fin 3, (u i * v j) * (ω.val i * ω.val j) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_overlapSphere_quadratic_coordinates]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The spherical average of a continuous bilinear quadratic observable is
`4*pi/3` times its trace in the standard Euclidean orthonormal basis. -/
theorem integral_overlapSphere_bilinear
    (B : JointSpace →L[ℝ] JointSpace →L[ℝ] ℝ) :
    (∫ ω : OverlapSphere, B ω.val ω.val ∂overlapSphereMeasure) =
      (4 * Real.pi / 3) * ∑ i : Fin 3,
        B (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have hexpand (x y : JointSpace) :
      B x y = ∑ i : Fin 3, ∑ j : Fin 3,
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
    (∫ ω : OverlapSphere, B ω.val ω.val ∂overlapSphereMeasure) =
        ∫ ω : OverlapSphere, ∑ i : Fin 3, ∑ j : Fin 3,
          (B (e i) (e j)) * (ω.val i * ω.val j) ∂overlapSphereMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => hexpand ω.val ω.val)
    _ = (4 * Real.pi / 3) * ∑ i : Fin 3, B (e i) (e i) :=
      integral_overlapSphere_quadratic_coordinates _
    _ = _ := rfl

end BoundaryDraft
