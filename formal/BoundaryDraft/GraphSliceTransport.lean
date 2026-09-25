import BoundaryDraft.GraphChartTransport
import BoundaryDraft.GraphCoordinateChart

/-!
# Canonical slice transport on one chart

An inverse cutoff gives a globally C¹ scalar graph representing every slice
inside a controlled target ball. The existing scalar-graph area theorem then
identifies its area with the canonical level measure, not a new parametric
measure. This is the one-chart layer; no finite atlas is constructed here.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- A single coordinate chart with a proved C¹ inverse extension on a target
ball. Its fields contain no measure transformation assumptions. -/
structure SliceHeightChart (h : Spatial → ℝ) extends CoordinateHeightChart h where
  center : JointSpace
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball center radius ⊆ chart.target
  inverseExtension : JointSpace → JointSpace
  contDiff_extension : ContDiff ℝ 1 inverseExtension
  extension_eq : EqOn inverseExtension chart.symm (Metric.ball center radius)

namespace AdmissibleGraphCap

/-- Construct the one-chart data from the unchanged admissibility hypotheses. -/
theorem exists_sliceHeightChart {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (x : JointSpace) (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    ∃ c : SliceHeightChart h, x ∈ c.chart.source ∧ c.center = c.chart x := by
  obtain ⟨c, hxC⟩ := hh.exists_coordinateHeightChart x hx hr
  obtain ⟨k, r, hk, hr, hball, he⟩ := c.exists_inverse_extension _ (c.chart.map_source hxC)
  exact ⟨{
    toCoordinateHeightChart := c
    center := c.chart x
    radius := r
    radius_pos := hr
    ball_subset := hball
    inverseExtension := k
    contDiff_extension := hk
    extension_eq := he }, hxC, rfl⟩

end AdmissibleGraphCap

private theorem graphAreaJacobian_isometry (R : JointSpace ≃ₗᵢ[ℝ] JointSpace)
    (v w : JointSpace) : graphAreaJacobian (R v) (R w) = graphAreaJacobian v w := by
  simp only [graphAreaJacobian_eq_sqrt_gram, R.norm_map, R.inner_map_map]

private theorem surfaceGraphDerivative_zero_basis (i : Fin 2) :
    surfaceGraphDerivative 0 (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      EuclideanSpace.basisFun (Fin 3) ℝ i.succ := by
  ext j
  simp only [EuclideanSpace.basisFun_apply]
  change (Fin.cons (0 : ℝ) (Pi.single i (1 : ℝ)) : Fin 3 → ℝ) j =
    (Pi.single i.succ (1 : ℝ) : Fin 3 → ℝ) j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Pi.single_apply, (Fin.succ_ne_zero i).symm]
  · simp only [Fin.cons_succ, Pi.single_apply, Fin.succ_inj]

private theorem normalizedHausdorffTwo_isometry_image (R : JointSpace ≃ₗᵢ[ℝ] JointSpace)
    (s : Set JointSpace) :
    normalizedHausdorffTwo.restrict (R '' s) = Measure.map R (normalizedHausdorffTwo.restrict s) := by
  have hm : Measure.map R normalizedHausdorffTwo = normalizedHausdorffTwo := by
    rw [normalizedHausdorffTwo, Measure.map_smul]
    congr 1
    exact R.toIsometryEquiv.map_hausdorffMeasure 2
  have he := R.toHomeomorph.measurableEmbedding.restrict_map normalizedHausdorffTwo (R '' s)
  change (Measure.map R normalizedHausdorffTwo).restrict (R '' s) =
    Measure.map R (normalizedHausdorffTwo.restrict (R ⁻¹' (R '' s))) at he
  rw [hm, R.injective.preimage_image] at he
  exact he

namespace SliceHeightChart

variable {h : Spatial → ℝ} (c : SliceHeightChart h)

/-- A globally C¹ scalar function representing a slice in rotated coordinates. -/
def scalarSlice (t : ℝ) (u : SurfacePlane) : ℝ :=
  c.rotation (c.inverseExtension (surfaceGraph (fun _ => t) u)) 0

/-- Global scalar-graph extension of the local slice, hence a measurable
embedding even outside the controlled target ball. -/
def slice (t : ℝ) (u : SurfacePlane) : JointSpace :=
  c.rotation.symm (surfaceGraph (c.scalarSlice t) u)

/-- Only these parameters are used for actual local geometric transport. -/
def sliceDomain (t : ℝ) : Set SurfacePlane :=
  (surfaceGraph (fun _ => t)) ⁻¹' Metric.ball c.center c.radius

theorem isOpen_sliceDomain (t : ℝ) : IsOpen (c.sliceDomain t) :=
  Metric.isOpen_ball.preimage (continuous_surfaceGraph continuous_const)

theorem contDiff_scalarSlice (t : ℝ) : ContDiff ℝ 1 (c.scalarSlice t) := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0).contDiff.comp
    (c.rotation.contDiff.comp (c.contDiff_extension.comp
      (jointHeightCoordinates.symm.contDiff.comp (contDiff_const.prodMk contDiff_id))))

theorem measurableEmbedding_slice (t : ℝ) : MeasurableEmbedding (c.slice t) :=
  c.rotation.symm.toHomeomorph.measurableEmbedding.comp
    (continuous_measurableEmbedding_surfaceGraph (c.contDiff_scalarSlice t).continuous)

/-- The extension agrees with the actual inverse on the entire open slice
domain, not merely at a base point. -/
theorem slice_eq_symm (t : ℝ) (u : SurfacePlane) (hu : u ∈ c.sliceDomain t) :
    c.slice t u = c.chart.symm (surfaceGraph (fun _ => t) u) := by
  apply c.rotation.injective
  rw [slice, c.rotation.apply_symm_apply]
  have hb := c.base_symm _ (c.ball_subset hu)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change c.rotation (c.inverseExtension (surfaceGraph (fun _ => t) u)) 0 = _
    rw [c.extension_eq hu]
  · have he := congrArg (fun v : SurfacePlane => v j) hb
    exact he.symm

/-- The graph-area factor equals the tangential factor already used in the
ambient change of variables. This avoids two unrelated notions of Jacobian. -/
theorem scalarSlice_jacobian (t : ℝ) (u : SurfacePlane) (hu : u ∈ c.sliceDomain t) :
    surfaceGraphJacobian (c.scalarSlice t) u =
      c.sliceJacobian (surfaceGraph (fun _ => t) u) := by
  let p := surfaceGraph (fun _ => t) u
  let D := fderiv ℝ c.chart.symm p
  let G := surfaceGraphDerivative (fderiv ℝ (c.scalarSlice t) u)
  have hg : HasFDerivAt (c.slice t) (c.rotation.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp G) u :=
    c.rotation.symm.toContinuousLinearEquiv.hasFDerivAt.comp u
      (hasStrictFDerivAt_surfaceGraph _ _ _
        ((c.contDiff_scalarSlice t).contDiffAt.hasStrictFDerivAt (by norm_num))).hasFDerivAt
  have hi : HasFDerivAt (fun v => c.chart.symm (surfaceGraph (fun _ => t) v))
      (D.comp (surfaceGraphDerivative 0)) u :=
    (c.hasFDerivAt_symm p (c.ball_subset hu)).comp u
      (hasStrictFDerivAt_surfaceGraph _ _ _ (hasStrictFDerivAt_const t u)).hasFDerivAt
  have he : c.slice t =ᶠ[𝓝 u] (fun v => c.chart.symm (surfaceGraph (fun _ => t) v)) :=
    mem_of_superset ((c.isOpen_sliceDomain t).mem_nhds hu) (fun v hv => c.slice_eq_symm t v hv)
  have hD := (hg.congr_of_eventuallyEq he.symm).unique hi
  have hv (i : Fin 2) : c.rotation.symm (G (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      D (EuclideanSpace.basisFun (Fin 3) ℝ i.succ) := by
    have hd := congrArg (fun A : SurfacePlane →L[ℝ] JointSpace =>
      A (EuclideanSpace.basisFun (Fin 2) ℝ i)) hD
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, surfaceGraphDerivative_zero_basis] using hd
  change _ = graphAreaJacobian (D (EuclideanSpace.basisFun (Fin 3) ℝ 1))
    (D (EuclideanSpace.basisFun (Fin 3) ℝ 2))
  have h0 : c.rotation.symm (G (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
      D (EuclideanSpace.basisFun (Fin 3) ℝ 1) := by simpa using hv 0
  have h1 : c.rotation.symm (G (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      D (EuclideanSpace.basisFun (Fin 3) ℝ 2) := by simpa using hv 1
  rw [← h0, ← h1, graphAreaJacobian_isometry, surfaceGraphDerivative_areaJacobian]
  rfl

/-- The existing scalar-graph area formula transports the normalized canonical
ambient surface measure through the extended slice. -/
theorem normalizedHausdorffTwo_slice_image (t : ℝ) (s : Set SurfacePlane)
    (hs : MeasurableSet s) :
    normalizedHausdorffTwo.restrict (c.slice t '' s) =
      Measure.map (c.slice t) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (surfaceGraphJacobian (c.scalarSlice t) u))) := by
  change normalizedHausdorffTwo.restrict ((c.rotation.symm ∘ surfaceGraph (c.scalarSlice t)) '' s) = _
  rw [image_comp, normalizedHausdorffTwo_isometry_image,
    normalizedHausdorffTwo_restrict_surfaceGraph_image (c.contDiff_scalarSlice t) s hs,
    Measure.map_map c.rotation.symm.continuous.measurable
      (continuous_surfaceGraph (c.contDiff_scalarSlice t).continuous).measurable]
  rfl

/-- Nonnegative slices in the controlled domain are canonical graph levels. -/
theorem slice_mem_level (t : ℝ) (ht : 0 ≤ t) (u : SurfacePlane) (hu : u ∈ c.sliceDomain t) :
    c.slice t u ∈ graphLevel h t := by
  rw [c.slice_eq_symm t u hu]
  exact ⟨c.symm_mem_closedPositive _ (c.ball_subset hu) ht,
    c.height_symm _ (c.ball_subset hu)⟩

/-- Canonical level-measure transport with the *same* local Jacobian as the
ambient formula. The only restrictions are nonnegative height and a measurable
subset of the constructed open parameter domain. -/
theorem graphLevelMeasure_slice_image (t : ℝ) (ht : 0 ≤ t) (s : Set SurfacePlane)
    (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain t) :
    (graphLevelMeasure h t).restrict (c.slice t '' s) =
      Measure.map (c.slice t) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (c.sliceJacobian (surfaceGraph (fun _ => t) u)))) := by
  have hsub : c.slice t '' s ⊆ graphLevel h t := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_level t ht u (hsD hu)
  rw [graphLevelMeasure, Measure.restrict_restrict_of_subset hsub,
    c.normalizedHausdorffTwo_slice_image t s hs]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [c.scalarSlice_jacobian t u (hsD hu)]

/-- Signed slice integration against the canonical level measure. -/
theorem integral_graphLevelMeasure_slice_image (t : ℝ) (ht : 0 ≤ t) (s : Set SurfacePlane)
    (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain t) (f : JointSpace → ℝ) :
    (∫ x in c.slice t '' s, f x ∂graphLevelMeasure h t) =
      ∫ u in s, c.sliceJacobian (surfaceGraph (fun _ => t) u) * f (c.slice t u) := by
  have hsub : c.slice t '' s ⊆ graphLevel h t := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_level t ht u (hsD hu)
  rw [graphLevelMeasure, Measure.restrict_restrict_of_subset hsub,
    c.normalizedHausdorffTwo_slice_image t s hs, (c.measurableEmbedding_slice t).integral_map,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_surfaceGraphJacobian _).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun hs
  intro u hu
  dsimp only
  rw [ENNReal.toReal_ofReal (surfaceGraphJacobian_pos _ _).le, smul_eq_mul,
    c.scalarSlice_jacobian t u (hsD hu)]

/-- Absolute integrability for the same local canonical slice formula. -/
theorem integrableOn_graphLevelMeasure_slice_image_iff (t : ℝ) (ht : 0 ≤ t)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsD : s ⊆ c.sliceDomain t)
    (f : JointSpace → ℝ) :
    IntegrableOn f (c.slice t '' s) (graphLevelMeasure h t) ↔
      IntegrableOn (fun u => c.sliceJacobian (surfaceGraph (fun _ => t) u) * f (c.slice t u)) s := by
  have hsub : c.slice t '' s ⊆ graphLevel h t := by
    rintro _ ⟨u, hu, rfl⟩
    exact c.slice_mem_level t ht u (hsD hu)
  unfold IntegrableOn
  rw [graphLevelMeasure, Measure.restrict_restrict_of_subset hsub,
    c.normalizedHausdorffTwo_slice_image t s hs, (c.measurableEmbedding_slice t).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul'
      (measurable_surfaceGraphJacobian _).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [ENNReal.toReal_ofReal (surfaceGraphJacobian_pos _ _).le, smul_eq_mul,
    c.scalarSlice_jacobian t u (hsD hu)]
  rfl

end SliceHeightChart
end BoundaryDraft
