import BoundaryDraft.GraphSurface
import BoundaryDraft.HausdorffAreaLocal

/-!
# Canonical level measures and height density

The level sets are taken only inside the closed positive region. Their
normalized Hausdorff measures define a canonical density independently of
the action. Regular levels have finite measure and an absolutely integrable
reciprocal-gradient weight. At zero this is exactly the existing joint target.
This file does not yet prove coarea or continuity of the density in height.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- The level inside the closed positive region, excluding unrelated exterior
zeros and allowing critical levels away from the collar. -/
def graphLevel (h : Spatial → ℝ) (s : ℝ) : Set JointSpace :=
  graphClosedPositive h ∩ {x | h x = s}

/-- Canonical normalized Hausdorff measure on a height level. -/
def graphLevelMeasure (h : Spatial → ℝ) (s : ℝ) : Measure JointSpace :=
  normalizedHausdorffTwo.restrict (graphLevel h s)

/-- Canonical height density. Its definition contains no action, coarea,
or limiting equality. -/
def graphHeightDensity (h : Spatial → ℝ) (s : ℝ) : ℝ :=
  ∫ x, 1 / ‖graphGradient h x‖ ∂graphLevelMeasure h s

@[simp] theorem graphLevel_zero (h : Spatial → ℝ) : graphLevel h 0 = graphJoint h := rfl

@[simp] theorem graphLevelMeasure_zero (h : Spatial → ℝ) :
    graphLevelMeasure h 0 = graphSurfaceMeasure h := by
  simp only [graphLevelMeasure, graphLevel_zero, normalizedHausdorffTwo,
    Measure.restrict_smul, graphSurfaceMeasure]

@[simp] theorem graphHeightDensity_zero (h : Spatial → ℝ) :
    graphHeightDensity h 0 = graphBoundaryIntegral h := by
  simp only [graphHeightDensity, graphLevelMeasure_zero, graphBoundaryIntegral]

/-- A regular scalar level in Euclidean three-space has locally finite
Hausdorff two-measure. The implicit function theorem supplies a Lipschitz
parameterization over the two-dimensional differential kernel. -/
theorem hausdorff_finiteAt_regular_level (f : JointSpace → ℝ)
    (L : JointSpace →L[ℝ] ℝ) (x : JointSpace) (hf : HasStrictFDerivAt f L x)
    (hL : L ≠ 0) (S : Set JointSpace) (hS : ∀ y ∈ S, f y = f x) :
    (μH[2] : Measure JointSpace).FiniteAtFilter (𝓝[S] x) := by
  letI : MeasurableSpace (LinearMap.ker L) := borel _
  letI : BorelSpace (LinearMap.ker L) := ⟨rfl⟩
  have hn : L.toLinearMap ≠ 0 := by
    intro he
    apply hL
    ext y
    exact LinearMap.congr_fun he y
  have hrange : LinearMap.range L = ⊤ := Module.Dual.range_eq_top_of_ne_zero hn
  let e := hf.implicitToPartialHomeomorph f L hrange
  let φ := hf.implicitFunction f L hrange (f x)
  have hφ : HasStrictFDerivAt φ (LinearMap.ker L).subtypeL 0 := hf.to_implicitFunction hrange
  obtain ⟨K, U, hU, hLip⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hdim : Module.finrank ℝ (LinearMap.ker L) = 2 := by
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    have he : Module.finrank ℝ JointSpace = 3 := by simp [JointSpace]
    rw [he] at hd
    change Module.finrank ℝ (LinearMap.ker L) + 1 = 3 at hd
    omega
  have hballfinite : (μH[2] : Measure (LinearMap.ker L)) (Metric.ball 0 r) < ∞ := by
    have hd : (Module.finrank ℝ (LinearMap.ker L) : ℝ) = 2 := by exact_mod_cast hdim
    rw [← hd]
    exact Metric.isBounded_ball.measure_lt_top
  have himage : (μH[2] : Measure JointSpace) (φ '' Metric.ball 0 r) < ∞ := by
    apply ((hLip.mono hball).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 2)).trans_lt
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.coe_ne_top) hballfinite
  refine ⟨φ '' Metric.ball 0 r, ?_, himage⟩
  have hsource : x ∈ e.source := hf.mem_implicitToPartialHomeomorph_source hrange
  have he0 : e x = (f x, 0) := hf.implicitToPartialHomeomorph_self hrange
  have hc : Tendsto (fun y => (e y).2) (𝓝 x) (𝓝 0) := by
    simpa only [ContinuousAt, he0] using (e.continuousAt hsource).snd
  have hnball := hc.eventually (Metric.ball_mem_nhds (0 : LinearMap.ker L) hr)
  have hinv := hf.eq_implicitFunction hrange
  filter_upwards [nhdsWithin_le_nhds hnball, nhdsWithin_le_nhds hinv,
    self_mem_nhdsWithin] with y hy hinvy hyS
  refine ⟨(e y).2, hy, ?_⟩
  change hf.implicitFunction f L hrange (f x) (e y).2 = y
  rw [← hS y hyS]
  exact hinvy

/-- At a positive height, restricting to the closed positive region does not
remove any points of the actual level. This does not hold at height zero. -/
theorem graphLevel_eq_of_pos (h : Spatial → ℝ) (s : ℝ) (hs : 0 < s) :
    graphLevel h s = {x : JointSpace | h x = s} := by
  ext x
  constructor
  · exact And.right
  · intro hx
    exact ⟨subset_closure (show 0 < h x from hx ▸ hs), hx⟩

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

theorem isCompact_level (s : ℝ) : IsCompact (graphLevel h s) := by
  apply hh.toGraphCapData.isCompact_closedPositive.of_isClosed_subset _ inter_subset_left
  exact hh.continuousOn_closedPositive.preimage_isClosed_of_isClosed
    isClosed_closure (isClosed_singleton (x := s))

theorem measurableSet_level (s : ℝ) : MeasurableSet (graphLevel h s) :=
  (hh.isCompact_level s).isClosed.measurableSet

theorem graphLevel_eq_empty_of_neg (s : ℝ) (hs : s < 0) : graphLevel h s = ∅ := by
  apply eq_empty_iff_forall_not_mem.2
  intro x hx
  have hn := hh.nonneg_on_closedPositive x hx.1
  rw [hx.2] at hn
  exact (not_le_of_gt hs) hn

/-- Negative heights have no canonical surface mass: levels are restricted
to the closed positive region, not an ambient continuation of the profile. -/
theorem graphLevelMeasure_eq_zero_of_neg (s : ℝ) (hs : s < 0) :
    graphLevelMeasure h s = 0 := by
  simp only [graphLevelMeasure, hh.graphLevel_eq_empty_of_neg s hs, Measure.restrict_empty]

theorem graphHeightDensity_eq_zero_of_neg (s : ℝ) (hs : s < 0) :
    graphHeightDensity h s = 0 := by
  simp only [graphHeightDensity, hh.graphLevelMeasure_eq_zero_of_neg s hs, integral_zero_measure]

/-- Two-sided continuity of the canonical density would force the boundary
integral to vanish. The collar argument instead needs continuity from
nonnegative heights; it must not assume a continuous ambient extension is the
canonical density itself. -/
theorem graphBoundaryIntegral_eq_zero_of_continuousAt_heightDensity
    (hc : ContinuousAt (graphHeightDensity h) 0) : graphBoundaryIntegral h = 0 := by
  have hl : Tendsto (graphHeightDensity h) (𝓝[<] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hh.graphHeightDensity_eq_zero_of_neg s hs).symm
  have he := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hl
  simpa only [graphHeightDensity_zero] using he

/-- Finiteness at any regular level; no condition is imposed at other levels. -/
theorem hausdorff_level_lt_top (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    (μH[2] : Measure JointSpace) (graphLevel h s) < ∞ := by
  apply (hh.isCompact_level s).measure_lt_top_of_nhdsWithin
  intro x hx
  exact hausdorff_finiteAt_regular_level _ _ x
    ((hh.smooth_near x hx.1).hasStrictFDerivAt (by norm_num)) (hreg x hx) _
    (fun y hy => hy.2.trans hx.2.symm)

/-- Finite two-dimensional Hausdorff measure makes each regular level null
for three-dimensional volume. This is derived independently of coarea. -/
theorem volume_graphLevel_eq_zero (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    volume (graphLevel h s) = 0 := by
  have hz : (μH[3] : Measure JointSpace) (graphLevel h s) = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (2 : ℝ) < 3) _).resolve_right
      (hh.hausdorff_level_lt_top s hreg).ne
  have hz' : (μH[Module.finrank ℝ JointSpace] : Measure JointSpace) (graphLevel h s) = 0 := by
    simpa only [JointSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] using hz
  exact (Measure.absolutelyContinuous_isAddHaarMeasure volume
    (μH[Module.finrank ℝ JointSpace] : Measure JointSpace)) hz'

/-- Nullity in the original coordinate-product spatial measure, not merely
in the Euclidean coordinate model. Positive heights may be replaced as
integration endpoints whenever that particular level is regular. -/
theorem volume_spatial_level_eq_zero (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    volume {x : Spatial | h x = s} = 0 := by
  have he : (WithLp.equiv 2 (Fin 3 → ℝ)) '' graphLevel h s = {x : Spatial | h x = s} := by
    rw [graphLevel_eq_of_pos h s hs]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨(WithLp.equiv 2 _).symm x, hx, rfl⟩
  have hm : MeasurableSet {x : Spatial | h x = s} := by
    rw [← he]
    exact ((hh.isCompact_level s).image (PiLp.continuous_equiv 2 _)).isClosed.measurableSet
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).measure_preimage hm.nullMeasurableSet]
  change volume {x : JointSpace | h x = s} = 0
  rw [← graphLevel_eq_of_pos h s hs]
  exact hh.volume_graphLevel_eq_zero s hreg

/-- Strict and closed positive collar endpoints agree almost everywhere
when the endpoint level is regular. Unrelated exterior zeros are not removed. -/
theorem ae_collar_endpoint (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    {x : Spatial | 0 < h x ∧ h x < s} =ᶠ[ae volume] {x | 0 < h x ∧ h x ≤ s} := by
  have hn : ∀ᵐ x : Spatial, h x ≠ s := by
    apply ae_iff.2
    simpa only [not_not] using hh.volume_spatial_level_eq_zero s hs hreg
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · exact fun hy => ⟨hy.1, hy.2.le⟩
  · exact fun hy => ⟨hy.1, lt_of_le_of_ne hy.2 hx⟩

/-- Endpoint replacement in the original spatial integral follows from
proved nullity; it is not an assumed part of a coarea formula. -/
theorem integral_collar_eq_closed_endpoint (s : ℝ) (hs : 0 < s)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0)
    (f : Spatial → ℝ) :
    (∫ x in {x | 0 < h x ∧ h x < s}, f x) = ∫ x in {x | 0 < h x ∧ h x ≤ s}, f x :=
  setIntegral_congr_set (hh.ae_collar_endpoint s hs hreg)

theorem finite_graphLevelMeasure (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    IsFiniteMeasure (graphLevelMeasure h s) := by
  constructor
  simp only [graphLevelMeasure, normalizedHausdorffTwo, Measure.restrict_apply_univ,
    Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hh.hausdorff_level_lt_top s hreg)

theorem integrable_graphLevel_reciprocal_slope (s : ℝ)
    (hreg : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    Integrable (fun x => 1 / ‖graphGradient h x‖) (graphLevelMeasure h s) := by
  letI := hh.finite_graphLevelMeasure s hreg
  have hc : ContinuousOn (fun x => 1 / ‖graphGradient h x‖) (graphLevel h s) := by
    apply continuousOn_const.div (hh.continuousOn_graphSlope.mono inter_subset_left)
    intro x hx
    change graphSlope h x ≠ 0
    rw [graphSlope_eq_norm_fderiv]
    exact norm_ne_zero_iff.2 (hreg x hx)
  have hi := hc.integrableOn_compact (μ := graphLevelMeasure h s) (hh.isCompact_level s)
  simpa only [IntegrableOn, graphLevelMeasure, Measure.restrict_restrict_of_subset
    (Subset.refl (graphLevel h s))] using hi

/-- The existing band gives finite canonical level measures and genuine
absolute integrability on every collar level, including zero. Critical points
above the chosen band remain allowed. -/
theorem exists_integrable_level_band : ∃ δ : ℝ, 0 < δ ∧ ∀ s ≤ δ,
    IsFiniteMeasure (graphLevelMeasure h s) ∧
      Integrable (fun x => 1 / ‖graphGradient h x‖) (graphLevelMeasure h s) := by
  obtain ⟨δ, hδ, hreg⟩ := hh.exists_noncritical_band
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hr : ∀ x ∈ graphLevel h s, fderiv ℝ (fun y : JointSpace => h y) x ≠ 0 := by
    intro x hx
    exact hreg x hx.1 (hx.2.le.trans hs)
  exact ⟨hh.finite_graphLevelMeasure s hr, hh.integrable_graphLevel_reciprocal_slope s hr⟩

/-- One noncritical band supplies all spatial endpoint replacements at once,
without placing any restriction on levels above the band. -/
theorem exists_null_level_band : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioc (0 : ℝ) δ,
    volume {x : Spatial | h x = s} = 0 := by
  obtain ⟨δ, hδ, hreg⟩ := hh.exists_noncritical_band
  refine ⟨δ, hδ, fun s hs => hh.volume_spatial_level_eq_zero s hs.1 ?_⟩
  intro x hx
  exact hreg x hx.1 (hx.2.le.trans hs.2)

/-- Any open neighborhood of the whole joint contains a sufficiently thin
closed positive collar. Thus a finite collection of joint charts also covers
all levels of a smaller collar, not only the zero level. -/
theorem exists_band_subset_joint_neighborhood (U : Set JointSpace) (hU : IsOpen U)
    (hJU : graphJoint h ⊆ U) : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ graphClosedPositive h, h x ≤ δ → x ∈ U := by
  let K := graphClosedPositive h \ U
  have hK : IsCompact K := hh.toGraphCapData.isCompact_closedPositive.diff hU
  have hp : ∀ x ∈ K, 0 < h x := by
    intro x hx
    apply lt_of_le_of_ne (hh.nonneg_on_closedPositive x hx.1)
    intro he
    exact hx.2 (hJU ⟨hx.1, he.symm⟩)
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le'
    (hh.continuousOn_closedPositive.mono diff_subset) hp
  refine ⟨m / 2, half_pos hm, ?_⟩
  intro x hx hδ
  by_contra hxU
  have hle := hmin x (show x ∈ K from ⟨hx, hxU⟩)
  linarith

theorem graphHeightDensity_zero_eq_angle : graphHeightDensity h 0 =
    ∫ x, jointCoth (graphSlope h x) ∂graphSurfaceMeasure h := by
  rw [graphHeightDensity_zero, hh.graphBoundaryIntegral_eq_angle]

end AdmissibleGraphCap
end BoundaryDraft
