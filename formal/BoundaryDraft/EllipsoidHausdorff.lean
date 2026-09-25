import BoundaryDraft.SphereSurface
import BoundaryDraft.GraphExamples
import BoundaryDraft.GraphSurface

/-!
# Canonical and parametric ellipsoid area

Local graphs are used to transport the canonical measure through the existing
axis map. The global sphere parameterization and its checked Jacobian remain
the original declarations from `EllipsoidSurface`.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Matrix Pointwise
noncomputable section
namespace BoundaryDraft

/-- Invertible diagonal coordinates with the Euclidean norm. -/
def euclideanAxisEquiv {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (WithLp.equiv 2 _).symm (fun i => b i * x i)
      invFun := fun x => (WithLp.equiv 2 _).symm (fun i => x i / b i)
      left_inv := by intro x; ext i; exact mul_div_cancel_left₀ _ (hb i).ne'
      right_inv := by intro x; ext i; exact mul_div_cancel₀ _ (hb i).ne'
      map_add' := by intro x y; ext i; simp; ring
      map_smul' := by intro c x; ext i; simp; ring }

abbrev ellipsoidPlaneAxis (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) : SurfacePlane ≃L[ℝ] SurfacePlane :=
  euclideanAxisEquiv (fun i => b i.succ) (fun i => hb i.succ)

/-- The upper ellipsoid as a scalar graph in its last two coordinates. -/
def ellipsoidGraphHeight (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) (z : SurfacePlane) : ℝ :=
  b 0 * sphereGraphHeight ((ellipsoidPlaneAxis b hb).symm z)

theorem continuous_ellipsoidGraphHeight (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    Continuous (ellipsoidGraphHeight b hb) :=
  continuous_const.mul (continuous_sphereGraphHeight.comp (ellipsoidPlaneAxis b hb).symm.continuous)

theorem ellipsoidAxisLinear_surfaceGraph (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (y : SurfacePlane) :
    ellipsoidAxisLinear b (surfaceGraph sphereGraphHeight y) =
      surfaceGraph (ellipsoidGraphHeight b hb) (ellipsoidPlaneAxis b hb y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change b 0 * sphereGraphHeight y = b 0 * sphereGraphHeight
      ((ellipsoidPlaneAxis b hb).symm (ellipsoidPlaneAxis b hb y))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · rfl

theorem contDiffOn_ellipsoidGraphHeight (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    ContDiffOn ℝ 1 (ellipsoidGraphHeight b hb) (ellipsoidPlaneAxis b hb '' ball 0 1) := by
  apply contDiffOn_const.mul
  apply contDiffOn_sphereGraphHeight.comp (ellipsoidPlaneAxis b hb).symm.contDiff.contDiffOn
  rintro _ ⟨y, hy, rfl⟩
  simpa using hy

theorem hasFDerivAt_ellipsoidGraphHeight (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    HasFDerivAt (ellipsoidGraphHeight b hb)
      (b 0 • (sphereGraphHeightDeriv y).comp (ellipsoidPlaneAxis b hb).symm.toContinuousLinearMap)
      (ellipsoidPlaneAxis b hb y) := by
  have hg : HasFDerivAt sphereGraphHeight (sphereGraphHeightDeriv y)
      ((ellipsoidPlaneAxis b hb).symm (ellipsoidPlaneAxis b hb y)) := by
    simpa using hasFDerivAt_sphereGraphHeight hy
  exact (hg.comp (ellipsoidPlaneAxis b hb y)
    (ellipsoidPlaneAxis b hb).symm.hasFDerivAt).const_mul (b 0)

theorem det_ellipsoidPlaneAxis (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    (ellipsoidPlaneAxis b hb).toContinuousLinearMap.det = b 1 * b 2 := by
  change (ellipsoidPlaneAxis b hb).toLinearEquiv.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  simp only [Matrix.det_fin_two, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr]
  simp [ellipsoidPlaneAxis, euclideanAxisEquiv, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply]

/-- Nonnegative integration is transported by the checked local graph area
formula, including arbitrary measurable weights. -/
theorem lintegral_normalizedHausdorffTwo_surfaceGraph {g : SurfacePlane → ℝ}
    (hg : Continuous g) (U : Set SurfacePlane) (hU : IsOpen U) (hgU : ContDiffOn ℝ 1 g U)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (f : JointSpace → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in surfaceGraph g '' s, f x ∂normalizedHausdorffTwo) =
      ∫⁻ y in s, ENNReal.ofReal (surfaceGraphJacobian g y) * f (surfaceGraph g y) := by
  rw [normalizedHausdorffTwo_restrict_surfaceGraph_image_of_contDiffOn hg U hU hgU s hs hsU,
    (continuous_measurableEmbedding_surfaceGraph hg).lintegral_map]
  exact lintegral_withDensity_eq_lintegral_mul _
    (measurable_surfaceGraphJacobian g).ennreal_ofReal
    (hf.comp (continuous_surfaceGraph hg).measurable)

private theorem graphAreaJacobian_smul (c d : ℝ) (v w : JointSpace) :
    graphAreaJacobian (c • v) (d • w) = |c| * |d| * graphAreaJacobian v w := by
  have he : ((WithLp.equiv 2 _).symm (crossProduct (c • v) (d • w)) : JointSpace) =
      (c * d) • (WithLp.equiv 2 _).symm (crossProduct v w) := by
    ext i
    fin_cases i <;> simp [cross_apply] <;> ring
  rw [graphAreaJacobian, he, norm_smul, Real.norm_eq_abs, abs_mul]
  rfl

/-- Compatibility of local graph densities uses the already checked global
ellipsoid tangential Jacobian, on a normalized tangent frame. -/
theorem ellipsoidGraphJacobian_density (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    (b 1 * b 2) * surfaceGraphJacobian (ellipsoidGraphHeight b hb) (ellipsoidPlaneAxis b hb y) =
      surfaceGraphJacobian sphereGraphHeight y *
        ellipsoidSurfaceJacobian b ⟨surfaceGraph sphereGraphHeight y,
          mem_sphere_zero_iff_norm.mpr (norm_surfaceGraph_sphere hy)⟩ := by
  let e0 := EuclideanSpace.basisFun (Fin 2) ℝ 0
  let e1 := EuclideanSpace.basisFun (Fin 2) ℝ 1
  let L := b 0 • (sphereGraphHeightDeriv y).comp (ellipsoidPlaneAxis b hb).symm.toContinuousLinearMap
  let v := surfaceGraphDerivative (sphereGraphHeightDeriv y) e0
  let w := surfaceGraphDerivative (sphereGraphHeightDeriv y) e1
  have hg := sphereGraphHeight_pos hy
  have hframe : crossProduct (sphereGraphHeight y • v) w =
      (surfaceGraph sphereGraphHeight y : Spatial) := by
    ext i
    fin_cases i <;>
      simp [v, w, e0, e1, surfaceGraphDerivative, sphereGraphHeightDeriv,
        surfaceGraph, cross_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
        innerSL, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
        Fin.cons, Fin.cases, Fin.induction, Fin.induction.go] <;>
      field_simp [hg.ne']
  have hD (z : SurfacePlane) : ellipsoidAxisLinear b (surfaceGraphDerivative (sphereGraphHeightDeriv y) z) =
      surfaceGraphDerivative L (ellipsoidPlaneAxis b hb z) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change b 0 * sphereGraphHeightDeriv y z =
        b 0 * sphereGraphHeightDeriv y ((ellipsoidPlaneAxis b hb).symm (ellipsoidPlaneAxis b hb z))
      rw [ContinuousLinearEquiv.symm_apply_apply]
    · rfl
  have hB (i : Fin 2) : ellipsoidPlaneAxis b hb (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      b i.succ • EuclideanSpace.basisFun (Fin 2) ℝ i := by
    ext j
    by_cases he : j = i
    · subst j; simp [ellipsoidPlaneAxis, euclideanAxisEquiv, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply]
    · simp [ellipsoidPlaneAxis, euclideanAxisEquiv, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply, he, Ne.symm he]
  have hJ := ellipsoid_tangent_jacobian b hb
    ⟨surfaceGraph sphereGraphHeight y, mem_sphere_zero_iff_norm.mpr (norm_surfaceGraph_sphere hy)⟩
    (sphereGraphHeight y • v) w hframe
  change graphAreaJacobian (ellipsoidAxisLinear b (sphereGraphHeight y • v))
    (ellipsoidAxisLinear b w) = _ at hJ
  rw [map_smul] at hJ
  dsimp only [v, w] at hJ
  rw [hD, hD, hB, hB, map_smul, map_smul, smul_smul,
    graphAreaJacobian_smul, abs_mul, abs_of_pos hg,
    abs_of_pos (hb (Fin.succ 0)), abs_of_pos (hb (Fin.succ 1)),
    surfaceGraphDerivative_areaJacobian] at hJ
  rw [surfaceGraphJacobian, (hasFDerivAt_ellipsoidGraphHeight b hb hy).fderiv,
    sphereGraphJacobian hy]
  change (b 1 * b 2) * Real.sqrt (1 + ‖L‖ ^ 2) = _
  rw [← hJ]
  field_simp
  ring

/-- A measurable ambient extension of the existing sphere Jacobian. It is
used only to express subtype transport, and agrees definitionally on the sphere. -/
def ellipsoidAmbientDensity (b : Fin 3 → ℝ) (x : JointSpace) : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ i, b i) * ‖ellipsoidReciprocal b x‖)

theorem measurable_ellipsoidAmbientDensity (b : Fin 3 → ℝ) :
    Measurable (ellipsoidAmbientDensity b) := by
  apply Measurable.ennreal_ofReal
  apply measurable_const.mul
  apply Measurable.norm
  exact (PiLp.continuous_equiv_symm 2 _).measurable.comp
    (measurable_pi_lambda _ fun i =>
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).measurable.div_const _)

@[simp] theorem ellipsoidAmbientDensity_coe (b : Fin 3 → ℝ) (u : JointSphere) :
    ellipsoidAmbientDensity b u.val = ENNReal.ofReal (ellipsoidSurfaceJacobian b u) := rfl

theorem normalizedHausdorffTwo_ellipsoidGraph_image (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsB : s ⊆ ball 0 1) :
    normalizedHausdorffTwo (ellipsoidAxisLinear b '' (surfaceGraph sphereGraphHeight '' s)) =
      ∫⁻ x in surfaceGraph sphereGraphHeight '' s, ellipsoidAmbientDensity b x ∂normalizedHausdorffTwo := by
  let B := ellipsoidPlaneAxis b hb
  let g := ellipsoidGraphHeight b hb
  have hBs := B.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  have hU : IsOpen (B '' ball 0 1) := B.toHomeomorph.isOpenMap _ isOpen_ball
  have hsub : B '' s ⊆ B '' ball 0 1 := image_mono hsB
  have himage : ellipsoidAxisLinear b '' (surfaceGraph sphereGraphHeight '' s) =
      surfaceGraph g '' (B '' s) := by
    rw [← image_comp, ← image_comp]
    exact image_congr (fun y _ => ellipsoidAxisLinear_surfaceGraph b hb y)
  have hleft := lintegral_normalizedHausdorffTwo_surfaceGraph
    (continuous_ellipsoidGraphHeight b hb) (B '' ball 0 1) hU
    (contDiffOn_ellipsoidGraphHeight b hb) (B '' s) hBs hsub (fun _ => 1) measurable_const
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at hleft
  rw [himage, hleft]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun y _ => B.hasFDerivAt.hasFDerivWithinAt) B.injective.injOn]
  rw [lintegral_normalizedHausdorffTwo_surfaceGraph continuous_sphereGraphHeight
    (ball 0 1) isOpen_ball contDiffOn_sphereGraphHeight s hs hsB
    (ellipsoidAmbientDensity b) (measurable_ellipsoidAmbientDensity b)]
  apply setLIntegral_congr_fun hs
  filter_upwards [] with y
  intro hy
  change ENNReal.ofReal |B.toContinuousLinearMap.det| * ENNReal.ofReal (surfaceGraphJacobian g (B y)) = _
  rw [det_ellipsoidPlaneAxis, abs_of_pos (mul_pos (hb 1) (hb 2)),
    ← ENNReal.ofReal_mul (mul_pos (hb 1) (hb 2)).le,
    ellipsoidGraphJacobian_density b hb (hsB hy),
    ENNReal.ofReal_mul (surfaceGraphJacobian_pos sphereGraphHeight y).le]
  rfl

theorem normalizedHausdorffTwo_axis_upper_sphere (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (S : Set JointSpace) (hS : MeasurableSet S) (hSB : S ⊆ sphere 0 1) (hS0 : ∀ x ∈ S, 0 < x 0) :
    normalizedHausdorffTwo (ellipsoidAxisLinear b '' S) =
      ∫⁻ x in S, ellipsoidAmbientDensity b x ∂normalizedHausdorffTwo := by
  let s := ball (0 : SurfacePlane) 1 ∩ surfaceGraph sphereGraphHeight ⁻¹' S
  have hs : MeasurableSet s := measurableSet_ball.inter
    (hS.preimage (continuous_surfaceGraph continuous_sphereGraphHeight).measurable)
  have he : surfaceGraph sphereGraphHeight '' s = S := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy.2
    · intro x hx
      obtain ⟨hB, hG⟩ := surfaceGraph_sphereGraphHeight_of_pos
        (mem_sphere_zero_iff_norm.mp (hSB hx)) (hS0 x hx)
      exact ⟨surfaceGraphBase x, ⟨hB, by simpa only [mem_preimage, hG] using hx⟩, hG⟩
  rw [← he]
  exact normalizedHausdorffTwo_ellipsoidGraph_image b hb s hs inter_subset_left

theorem normalizedHausdorffTwo_isometry_preserving (e : JointSpace ≃ₗᵢ[ℝ] JointSpace) :
    MeasurePreserving e normalizedHausdorffTwo normalizedHausdorffTwo := by
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e (ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure JointSpace)) = _
  rw [Measure.map_smul]
  exact congrArg (ENNReal.ofReal (Real.pi / 4) • ·) (e.toIsometryEquiv.map_hausdorffMeasure 2)

theorem lintegral_normalizedHausdorffTwo_isometry_image
    (e : JointSpace ≃ₗᵢ[ℝ] JointSpace) (S : Set JointSpace) (f : JointSpace → ℝ≥0∞) :
    (∫⁻ x in e '' S, f x ∂normalizedHausdorffTwo) =
      ∫⁻ x in S, f (e x) ∂normalizedHausdorffTwo := by
  rw [← ((normalizedHausdorffTwo_isometry_preserving e).restrict_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' S)).lintegral_comp_emb e.toHomeomorph.measurableEmbedding,
    e.injective.preimage_image]

@[simp] theorem ellipsoidAmbientDensity_neg (b : Fin 3 → ℝ) (x : JointSpace) :
    ellipsoidAmbientDensity b (-x) = ellipsoidAmbientDensity b x := by
  have he : ellipsoidReciprocal b (-x) = -ellipsoidReciprocal b x := by
    ext i; simp [ellipsoidReciprocal, neg_div]
  simp only [ellipsoidAmbientDensity, he, norm_neg]

theorem normalizedHausdorffTwo_axis_lower_sphere (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (S : Set JointSpace) (hS : MeasurableSet S) (hSB : S ⊆ sphere 0 1) (hS0 : ∀ x ∈ S, x 0 < 0) :
    normalizedHausdorffTwo (ellipsoidAxisLinear b '' S) =
      ∫⁻ x in S, ellipsoidAmbientDensity b x ∂normalizedHausdorffTwo := by
  let e : JointSpace ≃ₗᵢ[ℝ] JointSpace := LinearIsometryEquiv.neg ℝ
  have h := normalizedHausdorffTwo_axis_upper_sphere b hb (e '' S)
    (e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hS)
    (by rintro _ ⟨x, hx, rfl⟩; simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hSB hx)
    (by rintro _ ⟨x, hx, rfl⟩; exact neg_pos.mpr (hS0 x hx))
  have he : ellipsoidAxisLinear b '' (e '' S) = e '' (ellipsoidAxisLinear b '' S) := by
    rw [← image_comp, ← image_comp]
    exact image_congr (fun x _ => (ellipsoidAxisLinear b).map_neg x)
  rw [he, normalizedHausdorffTwo_isometry_image,
    lintegral_normalizedHausdorffTwo_isometry_image] at h
  change normalizedHausdorffTwo (ellipsoidAxisLinear b '' S) =
    ∫⁻ x in S, ellipsoidAmbientDensity b (-x) ∂normalizedHausdorffTwo at h
  simpa only [ellipsoidAmbientDensity_neg] using h

/-- The equator has zero canonical area, by the checked planar normalization.
Its ellipsoid image is null too; no exceptional set is silently discarded. -/
theorem normalizedHausdorffTwo_equator :
    normalizedHausdorffTwo {x : JointSpace | x ∈ sphere 0 1 ∧ x 0 = 0} = 0 := by
  have he : {x : JointSpace | x ∈ sphere 0 1 ∧ x 0 = 0} =
      surfaceGraphDerivative 0 '' sphere (0 : SurfacePlane) 1 := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      have hs : ‖surfaceGraphBase x‖ ^ 2 = 1 := by
        have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x
        rw [mem_sphere_zero_iff_norm.mp hx, one_pow, Fin.sum_univ_succ, hx0] at hn
        simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add,
          PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hn.symm
      refine ⟨surfaceGraphBase x, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm]
        nlinarith [norm_nonneg (surfaceGraphBase x)]
      · ext i
        exact Fin.cases hx0.symm (fun _ => rfl) i
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      have hs := surfaceGraphDerivative_norm_sq 0 y
      rw [ContinuousLinearMap.zero_apply, zero_pow (by norm_num : 2 ≠ 0), zero_add,
        mem_sphere_zero_iff_norm.mp hy, one_pow] at hs
      nlinarith [norm_nonneg (surfaceGraphDerivative 0 y)]
  rw [he, normalizedHausdorffTwo_surfaceGraphDerivative_image, Measure.addHaar_sphere, mul_zero]

theorem normalizedHausdorffTwo_linear_image_null (A : JointSpace →L[ℝ] JointSpace)
    (S : Set JointSpace) (hS : normalizedHausdorffTwo S = 0) :
    normalizedHausdorffTwo (A '' S) = 0 := by
  have hraw : (μH[2] : Measure JointSpace) S = 0 := by
    change ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure JointSpace) S = 0 at hS
    exact (mul_eq_zero.mp hS).resolve_left (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have h := A.lipschitz.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 2) S
  rw [hraw, mul_zero, nonpos_iff_eq_zero] at h
  change ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure JointSpace) (A '' S) = 0
  rw [h, mul_zero]

/-- Pullback through the original ambient axis map, first as an ambient
measure restricted to the sphere. -/
theorem normalizedHausdorffTwo_comap_axis_restrict_sphere (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    (Measure.comap (ellipsoidAxisLinear b) normalizedHausdorffTwo).restrict JointSphere =
      (normalizedHausdorffTwo.withDensity (ellipsoidAmbientDensity b)).restrict JointSphere := by
  let P : Set JointSpace := {x | x ∈ JointSphere ∧ 0 < x 0}
  let M : Set JointSpace := {x | x ∈ JointSphere ∧ x 0 < 0}
  let E : Set JointSpace := {x | x ∈ JointSphere ∧ x 0 = 0}
  have hP : MeasurableSet P := isClosed_sphere.measurableSet.inter
    (measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).measurable)
  have hM : MeasurableSet M := isClosed_sphere.measurableSet.inter
    (measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).measurable measurable_const)
  have hE : MeasurableSet E := isClosed_sphere.measurableSet.inter
    (measurableSet_eq_fun (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).measurable measurable_const)
  have hcover : JointSphere = (P ∪ M) ∪ E := by
    ext x
    simp only [P, M, E, mem_union, mem_setOf_eq]
    constructor
    · intro hx
      rcases lt_trichotomy (x 0) 0 with h | h | h
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl (Or.inl ⟨hx, h⟩)
    · rintro ((h | h) | h) <;> exact h.1
  have hA : MeasurableEmbedding (ellipsoidAxisLinear b) :=
    (euclideanAxisEquiv b hb).toHomeomorph.measurableEmbedding
  rw [hcover, Measure.restrict_union_congr, Measure.restrict_union_congr]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs, hA.comap_apply,
      withDensity_apply _ (hs.inter hP)]
    exact normalizedHausdorffTwo_axis_upper_sphere b hb _ (hs.inter hP)
      (fun _ hx => hx.2.1) (fun _ hx => hx.2.2)
  · ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs, hA.comap_apply,
      withDensity_apply _ (hs.inter hM)]
    exact normalizedHausdorffTwo_axis_lower_sphere b hb _ (hs.inter hM)
      (fun _ hx => hx.2.1) (fun _ hx => hx.2.2)
  · have hz : normalizedHausdorffTwo E = 0 := normalizedHausdorffTwo_equator
    have hAz := normalizedHausdorffTwo_linear_image_null (ellipsoidAxisLinear b).toContinuousLinearMap E hz
    rw [Measure.restrict_eq_zero.mpr (by rw [hA.comap_apply]; exact hAz),
      restrict_withDensity hE, Measure.restrict_eq_zero.mpr hz, withDensity_zero_left]

private theorem withDensity_map_embedding {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) (μ : Measure X) (g : Y → ℝ≥0∞) :
    (Measure.map f μ).withDensity g = Measure.map f (μ.withDensity (fun x => g (f x))) := by
  ext s hs
  rw [withDensity_apply _ hs, hf.map_apply, withDensity_apply _ (hf.measurable hs),
    hf.restrict_map μ s, hf.lintegral_map]

theorem ellipsoidAxisLinear_image_sphere (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    ellipsoidAxisLinear b '' JointSphere = ellipsoidJoint b := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ellipsoidJointParam b hb ⟨u, hu⟩).property
  · intro hx
    refine ⟨((ellipsoidJointParam b hb).symm ⟨x, hx⟩).val,
      ((ellipsoidJointParam b hb).symm ⟨x, hx⟩).property, ?_⟩
    exact congrArg Subtype.val ((ellipsoidJointParam b hb).apply_symm_apply ⟨x, hx⟩)

theorem measurableSet_ellipsoidJoint (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    MeasurableSet (ellipsoidJoint b) := by
  rw [← ellipsoidAxisLinear_image_sphere b hb]
  exact (euclideanAxisEquiv b hb).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
    isClosed_sphere.measurableSet

/-- Measure-level compatibility in ambient Euclidean space. The map by
`Subtype.val` is essential: the existing parametric measure lives on the joint
subtype, whereas the canonical Hausdorff measure lives in three-space. -/
theorem normalizedHausdorffTwo_restrict_ellipsoidJoint (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    normalizedHausdorffTwo.restrict (ellipsoidJoint b) =
      Measure.map (Subtype.val : ellipsoidJoint b → JointSpace) (ellipsoidSurfaceMeasure b hb) := by
  have hA : MeasurableEmbedding (ellipsoidAxisLinear b) :=
    (euclideanAxisEquiv b hb).toHomeomorph.measurableEmbedding
  have hm := hA.restrict_map (Measure.comap (ellipsoidAxisLinear b) normalizedHausdorffTwo)
    (ellipsoidAxisLinear b '' JointSphere)
  have hrange : range (ellipsoidAxisLinear b) = univ := (euclideanAxisEquiv b hb).surjective.range_eq
  rw [hA.map_comap, hrange, Measure.restrict_univ, hA.injective.preimage_image,
    normalizedHausdorffTwo_comap_axis_restrict_sphere b hb,
    ellipsoidAxisLinear_image_sphere b hb, restrict_withDensity isClosed_sphere.measurableSet,
    normalizedHausdorffTwo_restrict_sphere,
    withDensity_map_embedding (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet)] at hm
  rw [hm, Measure.map_map hA.measurable measurable_subtype_coe, ellipsoidSurfaceMeasure,
    Measure.map_map measurable_subtype_coe (ellipsoidJointParam b hb).measurable]
  rfl

/-- The same compatibility on the measurable joint subtype. No new surface
measure is used to make the identity true. -/
theorem normalizedHausdorffTwo_comap_ellipsoidJoint (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i) :
    Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo =
      ellipsoidSurfaceMeasure b hb := by
  have hv := MeasurableEmbedding.subtype_coe (measurableSet_ellipsoidJoint b hb)
  have hm := congrArg (Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace))
    (normalizedHausdorffTwo_restrict_ellipsoidJoint b hb)
  rw [hv.comap_map, hv.comap_restrict] at hm
  have he : (Subtype.val : ellipsoidJoint b → JointSpace) ⁻¹' ellipsoidJoint b = univ := by
    ext x; simp only [mem_preimage, mem_univ, iff_true]; exact x.property
  simpa only [he, Measure.restrict_univ] using hm

/-- Nonnegative measurable joint observables have the same integral in the
canonical and original parametric measures. In fact the identity holds for
all nonnegative functions by measure equality. -/
theorem lintegral_ellipsoid_canonical (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : ellipsoidJoint b → ℝ≥0∞) :
    (∫⁻ x, f x ∂Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo) =
      ∫⁻ x, f x ∂ellipsoidSurfaceMeasure b hb := by
  rw [normalizedHausdorffTwo_comap_ellipsoidJoint b hb]

/-- Absolute integrability of any joint observable agrees in the two subtype
measures, independently of how it might be extended off the joint. -/
theorem integrable_ellipsoid_subtype_canonical_iff (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : ellipsoidJoint b → ℝ) :
    Integrable f (Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo) ↔
      Integrable f (ellipsoidSurfaceMeasure b hb) := by
  rw [normalizedHausdorffTwo_comap_ellipsoidJoint b hb]

/-- Signed integral compatibility for observables defined only on the joint. -/
theorem integral_ellipsoid_subtype_canonical (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : ellipsoidJoint b → ℝ) :
    (∫ x, f x ∂Measure.comap (Subtype.val : ellipsoidJoint b → JointSpace) normalizedHausdorffTwo) =
      ∫ x, f x ∂ellipsoidSurfaceMeasure b hb := by
  rw [normalizedHausdorffTwo_comap_ellipsoidJoint b hb]

/-- Absolute integrability is preserved by ambient/subtype transport. -/
theorem integrableOn_ellipsoid_canonical_iff (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : JointSpace → ℝ) :
    IntegrableOn f (ellipsoidJoint b) normalizedHausdorffTwo ↔
      Integrable (fun x : ellipsoidJoint b => f x.val) (ellipsoidSurfaceMeasure b hb) := by
  rw [IntegrableOn, normalizedHausdorffTwo_restrict_ellipsoidJoint b hb,
    (MeasurableEmbedding.subtype_coe (measurableSet_ellipsoidJoint b hb)).integrable_map_iff]
  rfl

/-- Signed integral compatibility, with subtype transport explicit. As usual
for the Bochner integral, the measure identity also covers nonintegrable
functions; the preceding theorem transports actual integrability. -/
theorem integral_ellipsoid_canonical (b : Fin 3 → ℝ) (hb : ∀ i, 0 < b i)
    (f : JointSpace → ℝ) :
    (∫ x in ellipsoidJoint b, f x ∂normalizedHausdorffTwo) =
      ∫ x : ellipsoidJoint b, f x.val ∂ellipsoidSurfaceMeasure b hb := by
  rw [normalizedHausdorffTwo_restrict_ellipsoidJoint b hb,
    (MeasurableEmbedding.subtype_coe (measurableSet_ellipsoidJoint b hb)).integral_map]

/-- Canonical absolute integrability reuses the established positive-angle
parametric proof, under exactly its original hypotheses. -/
theorem integrableOn_ellipsoid_canonical_coth (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    IntegrableOn (fun x => jointCoth (ellipsoidSlope a b x)) (ellipsoidJoint b) normalizedHausdorffTwo :=
  (integrableOn_ellipsoid_canonical_iff b (fun i => by linarith [hb i]) _).mpr
    (integrable_ellipsoid_coth a b ha hb)

/-- The canonical variable-angle integral equals the existing parametric
value; neither the integral evaluation nor the global Jacobian is reproved. -/
theorem integral_ellipsoid_canonical_coth (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    (∫ x in ellipsoidJoint b, jointCoth (ellipsoidSlope a b x) ∂normalizedHausdorffTwo) =
      2 * Real.pi * (∏ i, b i) / a := by
  rw [integral_ellipsoid_canonical b (fun i => by linarith [hb i])]
  exact integral_ellipsoid_coth a b ha hb

/-- The admissible cap's canonical joint is exactly the original ellipsoid
joint, under the original concrete hypotheses. -/
theorem graphJoint_ellipsoid (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) : graphJoint (ellipsoidProfile a b) = ellipsoidJoint b := by
  have hb0 : ∀ i, 0 < b i := fun i => by linarith [hb i]
  let e := euclideanAxisEquiv b hb0
  have hiff (x : JointSpace) : 0 < ellipsoidProfile a b x ↔ ‖e.symm x‖ < 1 := by
    rw [ellipsoidProfile_pos_iff a b ha, ← ellipsoidRadius_sq]
    change ‖e.symm x‖ ^ 2 < 1 ↔ ‖e.symm x‖ < 1
    constructor <;> intro h <;> nlinarith [norm_nonneg (e.symm x)]
  have hpos : {x : JointSpace | 0 < ellipsoidProfile a b x} = e '' ball 0 1 := by
    ext x
    rw [mem_setOf_eq, hiff]
    constructor
    · intro hx
      exact ⟨e.symm x, mem_ball_zero_iff.mpr hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [e.symm_apply_apply] using mem_ball_zero_iff.mp hy
  rw [(ellipsoid_admissible a b ha hb).graphJoint_eq_frontier, hpos]
  change frontier (e.toHomeomorph '' ball 0 1) = _
  rw [← e.toHomeomorph.image_frontier, frontier_ball (0 : JointSpace) (by norm_num : (1 : ℝ) ≠ 0)]
  exact ellipsoidAxisLinear_image_sphere b hb0

/-- The existing general graph-cap measure, not a replacement definition,
agrees with the original parametric ellipsoid measure after subtype transport. -/
theorem graphSurfaceMeasure_ellipsoid (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    graphSurfaceMeasure (ellipsoidProfile a b) =
      Measure.map (Subtype.val : ellipsoidJoint b → JointSpace)
        (ellipsoidSurfaceMeasure b (fun i => by linarith [hb i])) := by
  rw [← normalizedHausdorffTwo_restrict_ellipsoidJoint b (fun i => by linarith [hb i]),
    normalizedHausdorffTwo, Measure.restrict_smul, graphSurfaceMeasure, graphJoint_ellipsoid a b ha hb]

/-- Canonical reciprocal-gradient and variable-angle boundary values recover
the original constant, with no strengthening of the axis assumptions. -/
theorem graphBoundaryIntegral_ellipsoid (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) :
    graphBoundaryIntegral (ellipsoidProfile a b) = 2 * Real.pi * (∏ i, b i) / a := by
  rw [(ellipsoid_admissible a b ha hb).graphBoundaryIntegral_eq_angle,
    graphSurfaceMeasure_ellipsoid a b ha hb,
    (MeasurableEmbedding.subtype_coe
      (measurableSet_ellipsoidJoint b (fun i => by linarith [hb i]))).integral_map]
  simpa only [graphSlope, graphGradient_ellipsoid, ellipsoidSlope] using
    integral_ellipsoid_coth a b ha hb

/-- Reinterpretation of the checked concrete limit in the canonical measure.
This does not prove the general graph-cap limit. -/
theorem ellipsoid_canonical_limit (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) : GraphCapLimitGoal (ellipsoidProfile a b) := by
  unfold GraphCapLimitGoal
  rw [graphBoundaryIntegral_ellipsoid a b ha hb]
  exact ellipsoidLimitGoal a b ha hb

end BoundaryDraft
