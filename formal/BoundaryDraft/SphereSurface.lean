import BoundaryDraft.HausdorffAreaLocal
import BoundaryDraft.EllipsoidSurface

/-!
# Canonical and polar sphere surface measure

A hemisphere graph and its radial filling identify normalized Hausdorff area
with three times radial-sector volume. A finite isometric hemisphere cover
then identifies the canonical and existing polar measures on the entire
sphere, including all seams and poles. Neither measure is redefined.
-/

open MeasureTheory Set Filter Metric intervalIntegral
open scoped Topology ENNReal Matrix Pointwise
noncomputable section
namespace BoundaryDraft

/-- Height of the upper unit hemisphere, continuously extended to the plane. -/
def sphereGraphHeight (y : SurfacePlane) : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)

/-- Its actual differential on the open unit disk. -/
def sphereGraphHeightDeriv (y : SurfacePlane) : SurfacePlane →L[ℝ] ℝ :=
  (-1 / sphereGraphHeight y) • innerSL ℝ y

theorem continuous_sphereGraphHeight : Continuous sphereGraphHeight :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))

theorem sphereGraphHeight_pos {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    0 < sphereGraphHeight y := by
  apply Real.sqrt_pos.2
  have h : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  nlinarith [norm_nonneg y]

theorem sphereGraphHeight_sq {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    sphereGraphHeight y ^ 2 = 1 - ‖y‖ ^ 2 := by
  apply Real.sq_sqrt
  have h : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  nlinarith [norm_nonneg y]

theorem hasFDerivAt_sphereGraphHeight {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    HasFDerivAt sphereGraphHeight (sphereGraphHeightDeriv y) y := by
  have h := ((hasFDerivAt_id y).norm_sq.const_sub 1).sqrt
    (ne_of_gt (Real.sqrt_pos.mp (sphereGraphHeight_pos hy)))
  convert h using 1
  ext v
  simp [sphereGraphHeightDeriv, sphereGraphHeight]
  ring

theorem contDiffOn_sphereGraphHeight : ContDiffOn ℝ 1 sphereGraphHeight (ball 0 1) := by
  apply ContDiffOn.sqrt
  · exact contDiffOn_const.sub ((contDiff_norm_sq ℝ).contDiffOn)
  · intro y hy
    exact ne_of_gt (Real.sqrt_pos.mp (sphereGraphHeight_pos hy))

theorem sphereGraphJacobian {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    surfaceGraphJacobian sphereGraphHeight y = 1 / sphereGraphHeight y := by
  rw [surfaceGraphJacobian, (hasFDerivAt_sphereGraphHeight hy).fderiv]
  have hn : ‖sphereGraphHeightDeriv y‖ = |(-1 : ℝ) / sphereGraphHeight y| * ‖y‖ := by
    change ‖((-1 : ℝ) / sphereGraphHeight y) • (innerSL ℝ y)‖ = _
    have hn := norm_smul ((-1 : ℝ) / sphereGraphHeight y) (innerSL ℝ y)
    rw [Real.norm_eq_abs, innerSL_apply_norm] at hn
    exact hn
  rw [hn]
  have hg := sphereGraphHeight_pos hy
  have hsq := sphereGraphHeight_sq hy
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [abs_div, abs_neg, abs_one, abs_of_pos hg]
  field_simp
  nlinarith

theorem norm_surfaceGraph_sphere {y : SurfacePlane} (hy : y ∈ ball 0 1) :
    ‖surfaceGraph sphereGraphHeight y‖ = 1 := by
  have h : ‖surfaceGraph sphereGraphHeight y‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
    change (∑ i : Fin 3, ‖(Fin.cons (sphereGraphHeight y) (y : Fin 2 → ℝ) : Fin 3 → ℝ) i‖ ^ 2) = 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ)]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (add_eq_of_eq_sub (sphereGraphHeight_sq hy))
  nlinarith [norm_nonneg (surfaceGraph sphereGraphHeight y)]

/-- Radial filling of the upper hemisphere. The first coordinate is radius;
the last two are Euclidean graph coordinates. -/
def sphereGraphCone (p : JointSpace) : JointSpace :=
  p 0 • surfaceGraph sphereGraphHeight (surfaceGraphBase p)

def sphereGraphConeDeriv (p : JointSpace) : JointSpace →L[ℝ] JointSpace :=
  (EuclideanSpace.proj 0).smulRight (surfaceGraph sphereGraphHeight (surfaceGraphBase p)) +
    p 0 • (surfaceGraphDerivative (sphereGraphHeightDeriv (surfaceGraphBase p))).comp
      surfaceGraphBaseL

theorem continuous_sphereGraphCone : Continuous sphereGraphCone :=
  (EuclideanSpace.proj 0).continuous.smul
    ((continuous_surfaceGraph continuous_sphereGraphHeight).comp continuous_surfaceGraphBase)

theorem hasFDerivAt_sphereGraphCone {p : JointSpace}
    (hp : surfaceGraphBase p ∈ ball 0 1) :
    HasFDerivAt sphereGraphCone (sphereGraphConeDeriv p) p := by
  have hg := hasFDerivAt_sphereGraphHeight hp
  have hG : HasFDerivAt (surfaceGraph sphereGraphHeight)
      (surfaceGraphDerivative (sphereGraphHeightDeriv (surfaceGraphBase p)))
      (surfaceGraphBase p) := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt).comp _
      (hg.finCons (F' := fun _ : Fin 3 => ℝ)
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).hasFDerivAt)
  simpa only [sphereGraphConeDeriv, add_comm] using
    (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt (x := p)).smul
      (hG.comp p surfaceGraphBaseL.hasFDerivAt))

theorem det_sphereGraphConeDeriv {p : JointSpace}
    (hp : surfaceGraphBase p ∈ ball 0 1) :
    (sphereGraphConeDeriv p).det = p 0 ^ 2 / sphereGraphHeight (surfaceGraphBase p) := by
  have hg := (sphereGraphHeight_pos hp).ne'
  have hs := sphereGraphHeight_sq hp
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two] at hs
  change (sphereGraphConeDeriv p).toLinearMap.det = _
  let g := sphereGraphHeight (surfaceGraphBase p)
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (sphereGraphConeDeriv p).toLinearMap =
      ![![g, -p 0 * p 1 / g, -p 0 * p 2 / g], ![p 1, p 0, 0], ![p 2, 0, p 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr,
        sphereGraphConeDeriv, sphereGraphHeightDeriv, surfaceGraphDerivative, surfaceGraph,
        surfaceGraphBase, surfaceGraphBaseL, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply, innerSL, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, Fin.sum_univ_two, Fin.sum_univ_succ, Fin.cons, Fin.cases, Fin.induction, Fin.induction.go, g] <;> ring
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, hm,
    Matrix.det_fin_three]
  change g * p 0 * p 0 - g * 0 * 0 - (-p 0 * p 1 / g) * p 1 * p 0 +
    (-p 0 * p 1 / g) * 0 * p 2 + (-p 0 * p 2 / g) * p 1 * 0 -
    (-p 0 * p 2 / g) * p 0 * p 2 = p 0 ^ 2 / g
  change g ^ 2 = 1 - (p 1 ^ 2 + p 2 ^ 2) at hs
  field_simp [show g ≠ 0 from hg]
  nlinarith [congrArg (fun z : ℝ => p 0 ^ 2 * z) hs]

theorem sphereGraphCone_injOn :
    InjOn sphereGraphCone {p | 0 < p 0 ∧ surfaceGraphBase p ∈ ball 0 1} := by
  intro p hp q hq he
  have hn : p 0 = q 0 := by
    have hn := congrArg norm he
    simpa only [sphereGraphCone, norm_smul, Real.norm_eq_abs,
      abs_of_pos hp.1, abs_of_pos hq.1, norm_surfaceGraph_sphere hp.2,
      norm_surfaceGraph_sphere hq.2, mul_one] using hn
  have hG : surfaceGraph sphereGraphHeight (surfaceGraphBase p) =
      surfaceGraph sphereGraphHeight (surfaceGraphBase q) := by
    rw [sphereGraphCone, sphereGraphCone, hn] at he
    exact (smul_right_injective _ hq.1.ne') he
  have hb := congrArg surfaceGraphBase hG
  simp only [surfaceGraphBase_surfaceGraph] at hb
  ext i
  refine Fin.cases hn (fun j => ?_) i
  exact congrArg (fun z : SurfacePlane => z j) hb

/-- Product coordinates used only for Lebesgue Fubini, not for Hausdorff
measure: the Euclidean volume equivalences are explicit. -/
def surfaceVolumeCoordinates : ℝ × SurfacePlane ≃ᵐ JointSpace :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    (show SurfacePlane ≃ᵐ (Fin 2 → ℝ) from
      { toEquiv := WithLp.equiv 2 _
        measurable_toFun := (PiLp.continuous_equiv 2 _).measurable
        measurable_invFun := (PiLp.continuous_equiv_symm 2 _).measurable })).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.trans
      (show (Fin 3 → ℝ) ≃ᵐ JointSpace from
        { toEquiv := (WithLp.equiv 2 _).symm
          measurable_toFun := (PiLp.continuous_equiv_symm 2 _).measurable
          measurable_invFun := (PiLp.continuous_equiv 2 _).measurable }))

theorem surfaceVolumeCoordinates_apply (r : ℝ) (y : SurfacePlane) :
    surfaceVolumeCoordinates (r, y) = (WithLp.equiv 2 _).symm (Fin.cons r y) := by
  simp [surfaceVolumeCoordinates, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv,
    MeasurableEquiv.prodCongr]
  rfl

theorem surfaceVolumeCoordinates_measurePreserving : MeasurePreserving surfaceVolumeCoordinates := by
  exact (PiLp.volume_preserving_equiv_symm (Fin 3)).comp
    (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm _).comp
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_equiv (Fin 2))))

theorem normalizedHausdorffTwo_sphereGraph_image (s : Set SurfacePlane)
    (hs : MeasurableSet s) (hsB : s ⊆ ball 0 1) :
    normalizedHausdorffTwo (surfaceGraph sphereGraphHeight '' s) =
      ∫⁻ y in s, ENNReal.ofReal (1 / sphereGraphHeight y) := by
  have hm := normalizedHausdorffTwo_restrict_surfaceGraph_image_of_contDiffOn
    continuous_sphereGraphHeight (ball 0 1) isOpen_ball contDiffOn_sphereGraphHeight s hs hsB
  have h := congrArg (fun μ : Measure JointSpace => μ univ) hm
  dsimp only at h
  rw [Measure.restrict_apply_univ, Measure.map_apply
    (continuous_surfaceGraph continuous_sphereGraphHeight).measurable MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  rw [h]
  apply setLIntegral_congr_fun hs
  filter_upwards [] with y
  intro hy
  rw [sphereGraphJacobian (hsB hy)]

theorem sphereGraphCone_image (s : Set SurfacePlane) :
    sphereGraphCone '' {p | p 0 ∈ Ioo (0 : ℝ) 1 ∧ surfaceGraphBase p ∈ s} =
      Ioo (0 : ℝ) 1 • (surfaceGraph sphereGraphHeight '' s) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact mem_smul.mpr ⟨p 0, hp.1, _, ⟨surfaceGraphBase p, hp.2, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩ := mem_smul.mp hx
    refine ⟨surfaceVolumeCoordinates (r, y), ?_, ?_⟩
    · rw [surfaceVolumeCoordinates_apply]
      exact ⟨hr, hy⟩
    · rw [surfaceVolumeCoordinates_apply]
      rfl

/-- The radial-sector volume is computed by a three-dimensional Jacobian and
Tonelli, rather than assumed from a surface-area formula. -/
theorem volume_sphereGraph_sector (s : Set SurfacePlane) (hs : MeasurableSet s)
    (hsB : s ⊆ ball 0 1) :
    volume (Ioo (0 : ℝ) 1 • (surfaceGraph sphereGraphHeight '' s)) =
      ENNReal.ofReal (1 / 3 : ℝ) * ∫⁻ y in s, ENNReal.ofReal (1 / sphereGraphHeight y) := by
  let D : Set JointSpace := {p | p 0 ∈ Ioo (0 : ℝ) 1 ∧ surfaceGraphBase p ∈ s}
  have hD : MeasurableSet D :=
    (measurableSet_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).measurable).inter
      (hs.preimage continuous_surfaceGraphBase.measurable)
  have hinj : InjOn sphereGraphCone D := by
    intro p hp q hq he
    exact sphereGraphCone_injOn ⟨hp.1.1, hsB hp.2⟩ ⟨hq.1.1, hsB hq.2⟩ he
  have hpre : surfaceVolumeCoordinates ⁻¹' D = Ioo (0 : ℝ) 1 ×ˢ s := by
    ext p
    simp only [mem_preimage, D, mem_setOf_eq, surfaceVolumeCoordinates_apply]
    rfl
  rw [← sphereGraphCone_image]
  change volume (sphereGraphCone '' D) = _
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hD
    (fun p (hp : p ∈ D) => (hasFDerivAt_sphereGraphCone (hsB hp.2)).hasFDerivWithinAt) hinj]
  have he : (∫⁻ p in D, ENNReal.ofReal |(sphereGraphConeDeriv p).det|) =
      ∫⁻ p in D, ENNReal.ofReal (p 0 ^ 2) * ENNReal.ofReal (1 / sphereGraphHeight (surfaceGraphBase p)) := by
    apply setLIntegral_congr_fun hD
    filter_upwards [] with p
    intro hp
    rw [det_sphereGraphConeDeriv (hsB hp.2), abs_of_nonneg
      (div_nonneg (sq_nonneg _) (sphereGraphHeight_pos (hsB hp.2)).le),
      div_eq_mul_inv, ← one_div, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [he, ← (surfaceVolumeCoordinates_measurePreserving.restrict_preimage_emb
    surfaceVolumeCoordinates.measurableEmbedding D).lintegral_comp_emb
      surfaceVolumeCoordinates.measurableEmbedding, hpre, Measure.volume_eq_prod]
  simp only [surfaceVolumeCoordinates_apply]
  change (∫⁻ p : ℝ × SurfacePlane in Ioo (0 : ℝ) 1 ×ˢ s,
    ENNReal.ofReal (p.1 ^ 2) * ENNReal.ofReal (1 / sphereGraphHeight p.2) ∂volume.prod volume) = _
  rw [← Measure.prod_restrict, lintegral_prod_mul
    (f := fun r : ℝ => ENNReal.ofReal (r ^ 2))
    (g := fun y : SurfacePlane => ENNReal.ofReal (1 / sphereGraphHeight y))
    (by fun_prop) ((measurable_const.div continuous_sphereGraphHeight.measurable).ennreal_ofReal.aemeasurable)]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_pow (n := 2)).1.mono_set Ioo_subset_Ioc_self)
    (Eventually.of_forall fun r => sq_nonneg r), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

theorem surfaceGraph_sphereGraphHeight_of_pos {x : JointSpace}
    (hx : ‖x‖ = 1) (hx0 : 0 < x 0) :
    surfaceGraphBase x ∈ ball 0 1 ∧ surfaceGraph sphereGraphHeight (surfaceGraphBase x) = x := by
  have hs : x 0 ^ 2 + ‖surfaceGraphBase x‖ ^ 2 = 1 := by
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x
    rw [hx, one_pow, Fin.sum_univ_succ] at hn
    simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hn.symm
  have hb : surfaceGraphBase x ∈ ball 0 1 := by
    rw [mem_ball_zero_iff]
    nlinarith [sq_pos_of_pos hx0, norm_nonneg (surfaceGraphBase x)]
  refine ⟨hb, ?_⟩
  have hg : sphereGraphHeight (surfaceGraphBase x) = x 0 := by
    unfold sphereGraphHeight
    exact (Real.sqrt_eq_iff_eq_sq (by nlinarith) hx0.le).mpr (by linarith)
  ext i
  exact Fin.cases hg (fun _ => rfl) i

/-- On an upper-hemisphere patch, canonical area is three times the volume of
its radial sector. This identifies measures on every measurable subset. -/
theorem normalizedHausdorffTwo_upper_sphere (S : Set JointSpace)
    (hS : MeasurableSet S) (hSB : S ⊆ sphere 0 1) (hS0 : ∀ x ∈ S, 0 < x 0) :
    normalizedHausdorffTwo S = 3 * volume (Ioo (0 : ℝ) 1 • S) := by
  let s := ball (0 : SurfacePlane) 1 ∩ surfaceGraph sphereGraphHeight ⁻¹' S
  have hs : MeasurableSet s := measurableSet_ball.inter
    (hS.preimage (continuous_surfaceGraph continuous_sphereGraphHeight).measurable)
  have he : surfaceGraph sphereGraphHeight '' s = S := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨hb, hg⟩ := surfaceGraph_sphereGraphHeight_of_pos
        (mem_sphere_zero_iff_norm.mp (hSB hx)) (hS0 x hx)
      exact ⟨surfaceGraphBase x, ⟨hb, by simpa only [mem_preimage, hg] using hx⟩, hg⟩
  rw [← he, normalizedHausdorffTwo_sphereGraph_image s hs inter_subset_left,
    volume_sphereGraph_sector s hs inter_subset_left, ← mul_assoc]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [ENNReal.mul_inv_cancel (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul]

theorem normalizedHausdorffTwo_isometry_image (e : JointSpace ≃ₗᵢ[ℝ] JointSpace)
    (S : Set JointSpace) : normalizedHausdorffTwo (e '' S) = normalizedHausdorffTwo S := by
  simp only [normalizedHausdorffTwo, Measure.smul_apply, smul_eq_mul]
  rw [e.isometry.hausdorffMeasure_image (Or.inl (by norm_num))]

theorem volume_sphere_sector_isometry (e : JointSpace ≃ₗᵢ[ℝ] JointSpace) (S : Set JointSpace) :
    volume (Ioo (0 : ℝ) 1 • (e '' S)) = volume (Ioo (0 : ℝ) 1 • S) := by
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

/-- Move any coordinate hemisphere to the chart used above. -/
def sphereHemisphereIsometry (j : Fin 3) (neg : Bool) : JointSpace ≃ₗᵢ[ℝ] JointSpace :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap j 0)).trans
    (if neg then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ JointSpace)

theorem sphereHemisphereIsometry_zero (j : Fin 3) (neg : Bool) (x : JointSpace) :
    sphereHemisphereIsometry j neg x 0 = if neg then -x j else x j := by
  cases neg <;> simp [sphereHemisphereIsometry, LinearIsometryEquiv.piLpCongrLeft_apply]
  all_goals exact congrArg x (Equiv.swap_apply_right j 0)

theorem sphere_has_positive_hemisphere (u : JointSphere) :
    ∃ k : Fin 3 × Bool, 0 < sphereHemisphereIsometry k.1 k.2 u.val 0 := by
  have hn : u.val ≠ 0 := by
    intro he
    have h := mem_sphere_zero_iff_norm.mp u.property
    simp [he] at h
  have hj : ∃ j, u.val j ≠ 0 := by
    by_contra! he
    apply hn
    ext j
    exact he j
  obtain ⟨j, hj⟩ := hj
  rcases lt_or_gt_of_ne hj with h | h
  · exact ⟨(j, true), by simpa [sphereHemisphereIsometry_zero] using neg_pos.mpr h⟩
  · exact ⟨(j, false), by simpa [sphereHemisphereIsometry_zero] using h⟩

/-- Euclidean normalized Hausdorff area on the sphere subtype agrees with the
existing radial-sector polar measure. The finite hemisphere cover loses no
poles, seams, or equator. -/
theorem normalizedHausdorffTwo_comap_sphere :
    Measure.comap (Subtype.val : JointSphere → JointSpace) normalizedHausdorffTwo =
      (volume : Measure JointSpace).toSphere := by
  let U : Fin 3 × Bool → Set JointSphere := fun k =>
    {u | 0 < sphereHemisphereIsometry k.1 k.2 u.val 0}
  have hU (k) : MeasurableSet (U k) := by
    exact measurableSet_lt measurable_const
      (((EuclideanSpace.proj 0).continuous.comp
        ((sphereHemisphereIsometry k.1 k.2).continuous.comp continuous_subtype_val)).measurable)
  have hcover : (⋃ k, U k) = univ := by
    ext u
    simp only [mem_iUnion, mem_univ, iff_true]
    exact sphere_has_positive_hemisphere u
  have hval := MeasurableEmbedding.subtype_coe (isClosed_sphere.measurableSet : MeasurableSet JointSphere)
  suffices ∀ k, (Measure.comap (Subtype.val : JointSphere → JointSpace) normalizedHausdorffTwo).restrict
      (U k) = (volume : Measure JointSpace).toSphere.restrict (U k) by
    have he := Measure.restrict_iUnion_congr.mpr this
    simpa only [hcover, Measure.restrict_univ] using he
  intro k
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, hval.comap_apply,
    Measure.toSphere_apply' _ (hs.inter (hU k))]
  have hS := hval.measurableSet_image.mpr (hs.inter (hU k))
  let e := sphereHemisphereIsometry k.1 k.2
  have harea := normalizedHausdorffTwo_upper_sphere
    (e '' (Subtype.val '' (s ∩ U k)))
    (e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hS)
    (by rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩
        simpa only [mem_sphere_zero_iff_norm, e.norm_map] using u.property)
    (by rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩; exact hu.2)
  rw [normalizedHausdorffTwo_isometry_image, volume_sphere_sector_isometry] at harea
  simpa [JointSpace] using harea

/-- Ambient/subtype transport for the canonical sphere measure. -/
theorem normalizedHausdorffTwo_restrict_sphere :
    normalizedHausdorffTwo.restrict JointSphere =
      Measure.map (Subtype.val : JointSphere → JointSpace) (volume : Measure JointSpace).toSphere := by
  rw [← normalizedHausdorffTwo_comap_sphere,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_comap, Subtype.range_coe]

end BoundaryDraft
