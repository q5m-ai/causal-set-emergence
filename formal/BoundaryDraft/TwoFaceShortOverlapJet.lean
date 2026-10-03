import BoundaryDraft.TwoFaceOverlap
import BoundaryDraft.GraphCoarea
import BoundaryDraft.MovingCollarIntegral
import BoundaryDraft.GraphDivergence
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The actual short-displacement gap and its moving collar

The original overlap statements use `AdmissibleTwoFace`. Pure fixed-domain
smoothness and moving-root helpers require only `RegularHeightPair` and are
shared with the independent-envelope producer. Displacements use the standard
product norm with a Euclidean spatial factor. Only the collar correction is
partitioned; no bilocal action is localized.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Time and Euclidean spatial translation, with the standard product norm. -/
abbrev Displacement := ℝ × JointSpace

/-- The original spacetime displacement, not a change of the causal cone. -/
def displacementSpacetime (z : Displacement) : Spacetime := Fin.cons z.1 z.2

/-- The lost vertical slice in the exact causal overlap formula. -/
def shortOverlapGap (f : Spatial → ℝ) (z : Displacement) (x : JointSpace) : ℝ :=
  z.1 - f (x + z.2) + f x

@[simp] theorem shortOverlapGap_zero (f : Spatial → ℝ) (x : JointSpace) :
    shortOverlapGap f 0 x = 0 := by simp [shortOverlapGap]

theorem displacementSpacetime_mem_causalFuture (z : Displacement) :
    displacementSpacetime z ∈ causalFuture 0 ↔ ‖z.2‖ ≤ z.1 := by
  have hs : spatialSeparationSq 0 (displacementSpacetime z) = ‖z.2‖ ^ 2 := by
    simp [spatialSeparationSq, displacementSpacetime, PiLp.norm_sq_eq_of_L2,
      Real.norm_eq_abs]
  simp only [causalFuture, mem_setOf_eq, Pi.zero_apply, sub_zero, hs]
  change (0 ≤ z.1 ∧ ‖z.2‖ ^ 2 ≤ z.1 ^ 2) ↔ _
  constructor
  · rintro ⟨ht, hb⟩
    exact (sq_le_sq₀ (norm_nonneg _) ht).mp hb
  · intro hb
    exact ⟨(norm_nonneg _).trans hb,
      (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hb)).mpr hb⟩

/-- The correction is integrated over the original positive spatial region.
In particular it never includes unrelated exterior zeros. -/
def shortOverlapCollarCorrection (h f : Spatial → ℝ) (z : Displacement) : ℝ :=
  ∫ x : JointSpace in {x : JointSpace | 0 < h x}, max 0 (shortOverlapGap f z x - h x)

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- A common translated-point neighborhood follows from the original local
C³ germs and compactness. No regularity of the raw exterior height is used. -/
theorem exists_smooth_future_thickening : ∃ ε : ℝ, 0 < ε ∧
    ∀ x ∈ Metric.cthickening ε (graphClosedPositive h),
      ContDiffAt ℝ 3 (fun y : JointSpace => f y) x := by
  let U := {x : JointSpace | ContDiffAt ℝ 3 (fun y : JointSpace => f y) x}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun x hx =>
    (show ContDiffAt ℝ 3 (fun y : JointSpace => f y) x from hx).eventually (by simp)
  obtain ⟨ε, hε, hsub⟩ := hf.toGraphCapData.isCompact_closedPositive.exists_cthickening_subset_open
    hU (fun x hx => hf.smooth_future x hx)
  exact ⟨ε, hε, hsub⟩

/-- The gap has a global causal bound even though the raw height need not be
smooth or continuous outside its positive region. -/
theorem shortOverlapGap_bounds : ∃ η : ℝ, 0 ≤ η ∧ η < 1 ∧
    ∀ (z : Displacement) (x : JointSpace), ‖z.2‖ ≤ z.1 →
      (1 - η) * z.1 ≤ shortOverlapGap f z x ∧
        shortOverlapGap f z x ≤ (1 + η) * z.1 := by
  obtain ⟨κ, η, hκ, hη, hbudget, _, hLip⟩ := hf.slope_budget
  refine ⟨η, hη, by linarith, ?_⟩
  intro z x hz
  have he : spatialDistance (x : Spatial) ((x + z.2 : JointSpace) : Spatial) = ‖z.2‖ := by
    change ‖(x + z.2) - x‖ = ‖z.2‖
    simp
  have hb := hLip x (x + z.2)
  rw [he] at hb
  have hB := mul_le_mul_of_nonneg_left hz hη
  have hab := abs_le.mp hb
  dsimp [shortOverlapGap]
  constructor <;> nlinarith

/-- A simple common norm bound, also for noncausal displacements. -/
theorem abs_shortOverlapGap_le (z : Displacement) (x : JointSpace) :
    |shortOverlapGap f z x| ≤ 2 * ‖z‖ := by
  obtain ⟨κ, η, hκ, hη, hbudget, _, hLip⟩ := hf.slope_budget
  have hb := hLip x (x + z.2)
  have he : spatialDistance (x : Spatial) ((x + z.2 : JointSpace) : Spatial) = ‖z.2‖ := by
    change ‖(x + z.2) - x‖ = ‖z.2‖
    simp
  rw [he] at hb
  have ht : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hs := norm_snd_le z
  have hη1 : η ≤ 1 := by linarith
  have hb' : |f x - f (x + z.2)| ≤ ‖z‖ :=
    hb.trans ((mul_le_of_le_one_left (norm_nonneg _) hη1).trans hs)
  calc
    |shortOverlapGap f z x| = |z.1 + (f x - f (x + z.2))| := by congr 1; dsimp [shortOverlapGap]; ring
    _ ≤ |z.1| + |f x - f (x + z.2)| := abs_add _ _
    _ ≤ 2 * ‖z‖ := by linarith

theorem shortOverlapGap_nonneg (z : Displacement) (hz : ‖z.2‖ ≤ z.1)
    (x : JointSpace) : 0 ≤ shortOverlapGap f z x := by
  obtain ⟨η, _, hη, hb⟩ := hf.shortOverlapGap_bounds
  exact (mul_nonneg (sub_nonneg.mpr hη.le) ((norm_nonneg _).trans hz)).trans (hb z x hz).1

omit hf in
/-- Joint C³ regularity of the actual translated gap at any pair whose two
spatial endpoints lie in the original future graph's C³ locus. -/
theorem contDiffAt_shortOverlapGap {z : Displacement} {x : JointSpace}
    (hx : ContDiffAt ℝ 3 (fun y : JointSpace => f y) x)
    (hxb : ContDiffAt ℝ 3 (fun y : JointSpace => f y) (x + z.2)) :
    ContDiffAt ℝ 3 (fun p : Displacement × JointSpace => shortOverlapGap f p.1 p.2) (z, x) := by
  exact (contDiffAt_fst.fst.sub (hxb.comp (z, x)
    (contDiffAt_snd.add contDiffAt_fst.snd))).add (hx.comp (z, x) contDiffAt_snd)

/-- Exact Euclidean-coordinate version of the causal overlap, restricted
only to the positive spatial region. Null vectors and the vertex are retained. -/
theorem translatedOverlap_eq_shortGap (z : Displacement) (hz : ‖z.2‖ ≤ z.1) :
    translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) =
      ∫ x : JointSpace in {x : JointSpace | 0 < h x}, max 0 (h x - shortOverlapGap f z x) := by
  change translatedOverlap (twoFaceRegion h f) (Fin.cons z.1 z.2) = _
  rw [hf.translatedOverlap_causal ((displacementSpacetime_mem_causalFuture z).mpr hz)]
  let e := WithLp.equiv 2 (Fin 3 → ℝ)
  have he : MeasurableEmbedding e := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_equiv (Fin 3)).integral_comp he]
  have hm : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  rw [← integral_indicator hm]
  apply integral_congr_ae
  filter_upwards with x
  change max 0 (f (x + z.2) - z.1 - (f x - max 0 (h x))) =
    ({x : JointSpace | 0 < h x}).indicator (fun x => max 0 (h x - shortOverlapGap f z x)) x
  by_cases hx : 0 < h x
  · rw [indicator_of_mem (show x ∈ {x : JointSpace | 0 < h x} from hx), max_eq_right hx.le]
    congr 1
    dsimp [shortOverlapGap, e]
    ring
  · rw [indicator_of_not_mem (show x ∉ {x : JointSpace | 0 < h x} from hx),
      max_eq_left (le_of_not_gt hx)]
    apply max_eq_left
    have hq := hf.shortOverlapGap_nonneg z hz x
    dsimp [shortOverlapGap] at hq
    change f (x + z.2) - z.1 - (f x - 0) ≤ 0
    linarith

/-- Integrability needed before splitting the signed actual overlap. -/
theorem integrableOn_shortOverlapGap (z : Displacement) :
    IntegrableOn (shortOverlapGap f z) {x : JointSpace | 0 < h x} := by
  have hc : Continuous (fun x : JointSpace => f x) :=
    hf.strictGraphLipschitz_upper.continuous.comp (PiLp.continuous_equiv 2 _)
  have hq : Continuous (shortOverlapGap f z) :=
    (continuous_const.sub (hc.comp (continuous_id.add continuous_const))).add hc
  exact (hq.continuousOn.integrableOn_compact
    hf.toGraphCapData.isCompact_closedPositive).mono_set subset_closure

/-- The source identity separating the fixed interior integral from the
moving collar, proved for the actual translated overlap. -/
theorem translatedOverlap_eq_fixed_sub_gap_add_collar (z : Displacement)
    (hz : ‖z.2‖ ≤ z.1) :
    translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) =
      (∫ x : JointSpace in {x : JointSpace | 0 < h x}, h x) -
      (∫ x : JointSpace in {x : JointSpace | 0 < h x}, shortOverlapGap f z x) +
        shortOverlapCollarCorrection h f z := by
  rw [hf.translatedOverlap_eq_shortGap z hz]
  have hh : IntegrableOn (fun x : JointSpace => h x) {x : JointSpace | 0 < h x} :=
    (hf.toAdmissibleGraphCap.continuousOn_closedPositive.integrableOn_compact
      hf.toGraphCapData.isCompact_closedPositive).mono_set subset_closure
  have hq := hf.integrableOn_shortOverlapGap z
  have he (x : JointSpace) : max 0 (h x - shortOverlapGap f z x) =
      h x - shortOverlapGap f z x + max 0 (shortOverlapGap f z x - h x) := by
    rcases le_total (h x) (shortOverlapGap f z x) with hl | hl
    · rw [max_eq_left (sub_nonpos.mpr hl), max_eq_right (sub_nonneg.mpr hl)]
      ring
    · rw [max_eq_right (sub_nonneg.mpr hl), max_eq_left (sub_nonpos.mpr hl)]
      ring
  simp_rw [he]
  have hc : IntegrableOn (fun x => max 0 (shortOverlapGap f z x - h x)) {x : JointSpace | 0 < h x} := by
    simpa only [Pi.sub_apply, max_comm] using (hq.sub hh).pos_part
  simpa only [Pi.sub_apply, shortOverlapCollarCorrection] using
    (integral_add (hh.sub hq) hc).trans
      (congrArg (fun a => a + shortOverlapCollarCorrection h f z) (integral_sub hh hq))

/-- Only a collar of width twice the displacement norm can contribute.
Positive-height critical points outside it are irrelevant to this correction. -/
theorem shortOverlapCollar_integrand_eq_zero (z : Displacement) (x : JointSpace)
    (hx : 2 * ‖z‖ ≤ h x) : max 0 (shortOverlapGap f z x - h x) = 0 := by
  apply max_eq_left
  have hb := (le_abs_self (shortOverlapGap f z x)).trans (hf.abs_shortOverlapGap_le z x)
  linarith

/-- Subtracting the planar cap cancels the volume and time-linear terms
exactly; the remaining fixed-domain integral involves only the future graph. -/
theorem translatedOverlap_sub_planar (z : Displacement) (hz : ‖z.2‖ ≤ z.1) :
    translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) -
      translatedOverlap (graphCapRegion h) (displacementSpacetime z) =
      (∫ x : JointSpace in {x : JointSpace | 0 < h x}, f (x + z.2) - f x) +
        shortOverlapCollarCorrection h f z - shortOverlapCollarCorrection h (fun _ => 0) z := by
  have hp := hf.toAdmissibleGraphCap.twoFace_planar
  rw [hf.translatedOverlap_eq_fixed_sub_gap_add_collar z hz,
    ← twoFaceRegion_planar h, hp.translatedOverlap_eq_fixed_sub_gap_add_collar z hz]
  have he : (∫ x : JointSpace in {x : JointSpace | 0 < h x}, f (x + z.2) - f x) =
      (∫ x : JointSpace in {x : JointSpace | 0 < h x}, shortOverlapGap (fun _ => 0) z x) -
        (∫ x : JointSpace in {x : JointSpace | 0 < h x}, shortOverlapGap f z x) := by
    calc
      _ = ∫ x : JointSpace in {x : JointSpace | 0 < h x},
          shortOverlapGap (fun _ => 0) z x - shortOverlapGap f z x := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [shortOverlapGap]
        ring
      _ = _ := integral_sub (hp.integrableOn_shortOverlapGap z) (hf.integrableOn_shortOverlapGap z)
  rw [he]
  ring

end AdmissibleTwoFace

namespace RegularHeightPair
variable {h f : Spatial → ℝ} (hf : RegularHeightPair h f)
include hf

/-- The single-face fixed-domain term is genuinely C³ from the raw germs,
independently of any slope bound or interior critical points. -/
theorem contDiffAt_shortOverlapBulk : ContDiffAt ℝ 3
    (fun z : Displacement => ∫ x : JointSpace in {x : JointSpace | 0 < h x}, f (x + z.2) - f x) 0 := by
  let μ : Measure JointSpace := volume.restrict {x : JointSpace | 0 < h x}
  have hs := hf.toRegularHeight.isCompact_closedPositive
  have he : (fun z : Displacement => ∫ x in graphClosedPositive h,
      f (x + z.2) - f x ∂μ) =
      (fun z : Displacement => ∫ x in {x : JointSpace | 0 < h x}, f (x + z.2) - f x) := by
    funext z
    have hm : μ.restrict (graphClosedPositive h) = μ := by
      dsimp [μ]
      rw [Measure.restrict_restrict hs.measurableSet,
        inter_eq_right.mpr (show {x : JointSpace | 0 < h x} ⊆ graphClosedPositive h from subset_closure)]
    change ∫ x, (f (x + z.2) - f x) ∂μ.restrict (graphClosedPositive h) = _
    rw [hm]
  rw [← he]
  apply MovingCollar.contDiffAt_integral_compact 3 hs
    (F := fun p : Displacement × JointSpace => f (p.2 + p.1.2) - f p.2)
  intro x hx
  have hfx := hf.smooth_future x hx
  have hfb : ContDiffAt ℝ 3 (fun x : JointSpace => f x) (x + (0 : Displacement).2) := by
    simpa using hfx
  exact (hfb.comp (0, x) (contDiffAt_snd.add contDiffAt_fst.snd)).sub
    (hfx.comp (0, x) contDiffAt_snd)

end RegularHeightPair

namespace AdmissibleTwoFace

/-- Compatibility with the original admissibility contract. -/
theorem contDiffAt_shortOverlapBulk {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) :
    ContDiffAt ℝ 3 (fun z : Displacement =>
      ∫ x : JointSpace in {x : JointSpace | 0 < h x}, f (x + z.2) - f x) 0 :=
  hf.toRegularHeightPair.contDiffAt_shortOverlapBulk

end AdmissibleTwoFace

namespace RegularHeightChart

/-- C³ inverse charts give C² weighted Jacobians. Nonvanishing justifies the
absolute determinant; no C³ regularity of the Jacobian is asserted. -/
theorem contDiffAt_weightedJacobian {h : Spatial → ℝ} (c : RegularHeightChart h)
    {w : JointSpace → ℝ} {p : JointSpace} (hp : p ∈ c.chart.target)
    (hw : ContDiffAt ℝ 2 w (c.chart.symm p)) :
    ContDiffAt ℝ 2 (c.weightedJacobian w) p := by
  have hi := c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)
  have hD := hi.fderiv_right (m := 2) (by norm_num)
  have he (i j : Fin 3) : ContDiffAt ℝ 2
      (fun u => (fderiv ℝ c.chart.symm u (EuclideanSpace.basisFun (Fin 3) ℝ j)) i) p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p
      (hD.clm_apply contDiffAt_const)
  have hdet : ContDiffAt ℝ 2 (fun u => (fderiv ℝ c.chart.symm u).toLinearMap.det) p := by
    simp_rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis,
      Matrix.det_fin_three, LinearMap.toMatrix_apply]
    exact (((((he 0 0).mul (he 1 1)).mul (he 2 2)).sub
      (((he 0 0).mul (he 1 2)).mul (he 2 1))).sub
      (((he 0 1).mul (he 1 0)).mul (he 2 2))).add
      (((he 0 1).mul (he 1 2)).mul (he 2 0)) |>.add
      (((he 0 2).mul (he 1 0)).mul (he 2 1)) |>.sub
      (((he 0 2).mul (he 1 1)).mul (he 2 0))
  have habs : ContDiffAt ℝ 2 (fun u => |(fderiv ℝ c.chart.symm u).toLinearMap.det|) p := by
    simpa only [Real.norm_eq_abs] using
      (contDiffAt_norm ℝ (c.det_fderiv_symm_ne_zero p hp)).comp p hdet
  exact (hw.comp p (hi.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide))).mul habs

end RegularHeightChart

namespace CollarHeightChart

variable {h f : Spatial → ℝ} (c : CollarHeightChart h)

/-- The actual C³ inverse, not the C¹ inverse extension used for area transport. -/
def movingPoint (p : (SurfacePlane × Displacement) × ℝ) : JointSpace :=
  c.chart.symm (jointHeightCoordinates.symm (p.2, p.1.1))

/-- Actual contact gap in a fixed collar chart. -/
def movingGap (f : Spatial → ℝ) (p : (SurfacePlane × Displacement) × ℝ) : ℝ :=
  shortOverlapGap f p.1.2 (c.movingPoint p)

/-- Joint smoothness of the actual chart gap on the zero-displacement
slice, at every point of the compact planar disk. -/
theorem contDiffAt_movingGap_zero (hf : RegularHeightPair h f)
    (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
    ContDiffAt ℝ 3 (c.movingGap f) ((y, 0), 0) := by
  have ht : jointHeightCoordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hx : c.movingPoint ((y, 0), 0) ∈ graphClosedPositive h :=
    c.symm_mem_closedPositive _ ht le_rfl
  have hφ : ContDiffAt ℝ 3 c.movingPoint ((y, 0), 0) :=
    (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds ht)).comp ((y, 0), 0)
      (jointHeightCoordinates.symm.contDiff.contDiffAt.comp ((y, 0), 0)
        (contDiffAt_snd.prodMk contDiffAt_fst.fst))
  have hfx := hf.smooth_future _ hx
  have hb : ContDiffAt ℝ 3 (fun u : JointSpace => f u)
      (c.movingPoint ((y, 0), 0) + (0 : Displacement).2) := by simpa using hfx
  exact (contDiffAt_fst.snd.fst.sub (hb.comp ((y, 0), 0)
    (hφ.add contDiffAt_fst.snd.snd))).add (hfx.comp ((y, 0), 0) hφ)

/-- The moving root is produced from regular height geometry and raw future
germs at EVERY point of the compact planar disk, not supplied as a premise.
It is jointly C³ in the planar coordinates and displacement. -/
theorem exists_contDiff_movingRoot (hf : RegularHeightPair h f)
    (y : SurfacePlane) (hy : y ∈ c.closedDisk) :
    ∃ η : SurfacePlane × Displacement → ℝ,
      η (y, 0) = 0 ∧ ContDiffAt ℝ 3 η (y, 0) ∧
      (∀ᶠ p in 𝓝 (y, (0 : Displacement)),
        η p = c.movingGap f (p, η p)) ∧
      (∀ᶠ a in 𝓝 ((y, (0 : Displacement)), (0 : ℝ)),
        a.2 = c.movingGap f a → a.2 = η a.1) := by
  let a : (SurfacePlane × Displacement) × ℝ := ((y, 0), 0)
  let x : JointSpace := c.movingPoint a
  have htarget : jointHeightCoordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hx : x ∈ graphClosedPositive h :=
    c.symm_mem_closedPositive _ htarget le_rfl
  have hφ : ContDiffAt ℝ 3 c.movingPoint a := by
    exact (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds htarget)).comp a
      (jointHeightCoordinates.symm.contDiff.contDiffAt.comp a
        (contDiffAt_snd.prodMk contDiffAt_fst.fst))
  have hfx := hf.smooth_future x hx
  have hq : ContDiffAt ℝ 3 (c.movingGap f) a := by
    have hb : ContDiffAt ℝ 3 (fun u : JointSpace => f u) (c.movingPoint a + a.1.2.2) := by
      simpa [a, x] using hfx
    exact (contDiffAt_fst.snd.fst.sub (hb.comp a
      (hφ.add contDiffAt_fst.snd.snd))).add (hfx.comp a hφ)
  let D := fderiv ℝ (fun u : JointSpace => f u) x
  let L : (SurfacePlane × Displacement) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ JointSpace).comp
      (ContinuousLinearMap.snd ℝ SurfacePlane Displacement) -
    D.comp ((ContinuousLinearMap.snd ℝ ℝ JointSpace).comp
      (ContinuousLinearMap.snd ℝ SurfacePlane Displacement))
  have hφD := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hfxD : HasFDerivAt (fun u : JointSpace => f u) D x :=
    (hfx.differentiableAt (by norm_num)).hasFDerivAt
  have hfxb : HasFDerivAt (fun u : JointSpace => f u) D (c.movingPoint a + a.1.2.2) := by
    simpa [a, x] using hfxD
  let S : ((SurfacePlane × Displacement) × ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ JointSpace).comp
      (ContinuousLinearMap.snd ℝ SurfacePlane Displacement)).comp
        (ContinuousLinearMap.fst ℝ (SurfacePlane × Displacement) ℝ)
  let B : ((SurfacePlane × Displacement) × ℝ) →L[ℝ] JointSpace :=
    ((ContinuousLinearMap.snd ℝ ℝ JointSpace).comp
      (ContinuousLinearMap.snd ℝ SurfacePlane Displacement)).comp
        (ContinuousLinearMap.fst ℝ (SurfacePlane × Displacement) ℝ)
  have hD : HasFDerivAt (c.movingGap f)
      (L.comp (ContinuousLinearMap.fst ℝ (SurfacePlane × Displacement) ℝ)) a := by
    have hd0 : HasFDerivAt (c.movingGap f)
        (S - D.comp (fderiv ℝ c.movingPoint a + B) + D.comp (fderiv ℝ c.movingPoint a)) a :=
      (S.hasFDerivAt.sub (hfxb.comp a (hφD.add B.hasFDerivAt))).add (hfxD.comp a hφD)
    apply hd0.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    change v.1.2.1 - D (fderiv ℝ c.movingPoint a v + v.1.2.2) +
      D (fderiv ℝ c.movingPoint a v) = v.1.2.1 - D v.1.2.2
    rw [map_add]
    ring
  exact MovingCollar.exists_contDiff_root hq (by simp [movingGap, a]) L hD

/-- One root function and one pair of positive radii work on the WHOLE
compact planar disk. These are derived from the actual gap and local IFT. -/
theorem exists_uniform_movingRoots (hf : RegularHeightPair h f) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ η : SurfacePlane × Displacement → ℝ,
      (∀ y ∈ c.closedDisk, η (y, 0) = 0) ∧
      ∀ y ∈ c.closedDisk, ∀ z ∈ Metric.ball (0 : Displacement) δ,
        ContDiffAt ℝ 3 η (y, z) ∧ |η (y, z)| < ε ∧
          η (y, z) = c.movingGap f ((y, z), η (y, z)) ∧
          ∀ t, |t| < ε → t = c.movingGap f ((y, z), t) → t = η (y, z) := by
  apply MovingCollar.exists_uniform_roots (isCompact_closedBall _ _)
  · intro y
    simp [movingGap]
  · exact c.exists_contDiff_movingRoot hf

end CollarHeightChart

namespace ControlledCollarAtlas

variable {h f : Spatial → ℝ} (A : ControlledCollarAtlas h)

/-- The actual oriented moving-collar integral in one fixed spatial fibre. -/
def movingFibre (i : Fin A.count) (f : Spatial → ℝ) (y : SurfacePlane)
    (η : Displacement → ℝ) (z : Displacement) : ℝ :=
  MovingCollar.fibre
    (fun t => (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)))
    (fun p : Displacement × ℝ => (A.charts i).movingGap f ((y, p.1), p.2)) η z

/-- An actual C³ fibre extension is constructed, with the original C³ future
and height germs and the derived C² weighted Jacobian. This statement is
local in the planar fibre; uniform gluing and planar integration are separate. -/
theorem exists_contDiff_movingFibre (hf : RegularHeightPair h f) (i : Fin A.count)
    (y : SurfacePlane) (hy : y ∈ (A.charts i).closedDisk) :
    ∃ η : Displacement → ℝ, η 0 = 0 ∧ ContDiffAt ℝ 3 η 0 ∧
      (∀ᶠ z in 𝓝 (0 : Displacement), η z = (A.charts i).movingGap f ((y, z), η z)) ∧
      ContDiffAt ℝ 3 (A.movingFibre i f y η) 0 := by
  let c := A.charts i
  obtain ⟨η, hη₀, hη, hr, _⟩ := c.exists_contDiff_movingRoot hf y hy
  let ηy : Displacement → ℝ := fun z => η (y, z)
  have hηy : ContDiffAt ℝ 3 ηy 0 := hη.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hry : ∀ᶠ z in 𝓝 (0 : Displacement), ηy z = c.movingGap f ((y, z), ηy z) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto.eventually hr
  refine ⟨ηy, hη₀, hηy, hry, ?_⟩
  have ht : jointHeightCoordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hw : ContDiffAt ℝ 2
      (fun t => c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y))) 0 := by
    have hweight : ContDiffAt ℝ 2 (A.weights i) (c.chart.symm (jointHeightCoordinates.symm (0, y))) :=
      (A.weights i).contMDiff.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (c.contDiffAt_weightedJacobian ht hweight).comp (0 : ℝ)
      (jointHeightCoordinates.symm.contDiff.contDiffAt.comp (0 : ℝ)
        (contDiffAt_id.prodMk contDiffAt_const))
  have hq : ContDiffAt ℝ 3
      (fun p : Displacement × ℝ => c.movingGap f ((y, p.1), p.2)) (0, 0) :=
    (c.contDiffAt_movingGap_zero hf y hy).comp (0, 0)
      ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)
  exact MovingCollar.contDiffAt_fibre hw hq hηy hη₀ hry

/-- A uniform moving-root representation of the ACTUAL positive-part
collar integral. This is not a conditional overlap-jet contract. -/
theorem exists_actual_collarFibre (hf : AdmissibleTwoFace h f) (i : Fin A.count) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : SurfacePlane × Displacement → ℝ,
      (∀ y ∈ (A.charts i).closedDisk, η (y, 0) = 0) ∧
      (∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Displacement) δ,
        ContDiffAt ℝ 3 η (y, z) ∧
          η (y, z) = (A.charts i).movingGap f ((y, z), η (y, z))) ∧
      ∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Displacement) δ,
        ‖z.2‖ ≤ z.1 →
        (∫ t in (0 : ℝ)..A.width,
          (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)) *
            max 0 ((A.charts i).movingGap f ((y, z), t) - t)) =
          A.movingFibre i f y (fun z => η (y, z)) z := by
  let c := A.charts i
  obtain ⟨ε, δ₀, hε, hδ₀, η, hη₀, hη⟩ := c.exists_uniform_movingRoots hf.toRegularHeightPair
  let δ := min δ₀ (min ε A.width / 4)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos (lt_min hε A.width_pos) (by norm_num))
  have hzδ (z : Displacement) (hz : z ∈ Metric.ball (0 : Displacement) δ) :
      z ∈ Metric.ball (0 : Displacement) δ₀ ∧ 2 * ‖z‖ < ε ∧ 2 * ‖z‖ < A.width := by
    have hz' : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have h1 := min_le_left δ₀ (min ε A.width / 4)
    have h2 := min_le_right δ₀ (min ε A.width / 4)
    have he := min_le_left ε A.width
    have hw := min_le_right ε A.width
    refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hz'.trans_le h1, ?_, ?_⟩ <;>
      dsimp only [δ] at hz' <;> nlinarith [norm_nonneg z]
  refine ⟨δ, hδ, η, hη₀, ?_, ?_⟩
  · intro y hy z hz
    exact ⟨(hη y hy z (hzδ z hz).1).1, (hη y hy z (hzδ z hz).1).2.2.1⟩
  · intro y hy z hz hcausal
    have hηp := hη y hy z (hzδ z hz).1
    have hroot := hηp.2.2.1
    have hbound (t : ℝ) : |c.movingGap f ((y, z), t)| ≤ 2 * ‖z‖ :=
      hf.abs_shortOverlapGap_le z (c.movingPoint ((y, z), t))
    have hnonneg (t : ℝ) : 0 ≤ c.movingGap f ((y, z), t) :=
      hf.shortOverlapGap_nonneg z hcausal _
    have hηpos : η (y, z) ∈ Icc 0 A.width := by
      rw [hroot]
      exact ⟨hnonneg _, ((le_abs_self _).trans (hbound _)).trans (hzδ z hz).2.2.le⟩
    have htarget (t : ℝ) (ht : t ∈ Icc 0 A.width) :
        jointHeightCoordinates.symm (t, y) ∈ c.chart.target :=
      c.ball_subset (c.rectangle_subset t
        ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩ y hy)
    have hΦ : ContinuousOn (fun t => c.movingPoint ((y, z), t)) (Icc 0 A.width) :=
      c.chart.symm.continuousOn.comp
        (jointHeightCoordinates.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
          htarget
    have hfc : Continuous (fun x : JointSpace => f x) :=
      hf.strictGraphLipschitz_upper.continuous.comp (PiLp.continuous_equiv 2 _)
    have hqc : ContinuousOn (fun t => c.movingGap f ((y, z), t)) (Icc 0 A.width) := by
      exact ((continuousOn_const (c := z.1)).sub
        (hfc.comp_continuousOn (hΦ.add (continuousOn_const (c := z.2))))).add
          (hfc.comp_continuousOn hΦ)
    have hwc : ContinuousOn
        (fun t => c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)))
        (Icc 0 A.width) :=
      (c.continuousOn_weightedJacobian (A.weights i) (A.weights i).contMDiff.continuous).comp
        (jointHeightCoordinates.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
          htarget
    apply MovingCollar.integral_positivePart_eq_root hηpos hqc hwc (hnonneg 0)
      (((le_abs_self _).trans (hbound A.width)).trans_lt (hzδ z hz).2.2) hroot
    intro t _ ht
    exact hηp.2.2.2 t (by rw [ht]; exact (hbound t).trans_lt (hzδ z hz).2.1) ht

/-- C³ displacement extension for the entire fixed planar disk in one
chart. The equality is with its actual positive-part collar contribution. -/
theorem exists_contDiff_chartCorrection (hf : AdmissibleTwoFace h f) (i : Fin A.count) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Displacement → ℝ, ContDiffAt ℝ 3 V 0 ∧ V 0 = 0 ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        V z = ∫ y in (A.charts i).disk, ∫ t in (0 : ℝ)..A.width,
          (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)) *
            max 0 ((A.charts i).movingGap f ((y, z), t) - t) := by
  let c := A.charts i
  obtain ⟨δ, hδ, η, hη₀, hη, heq⟩ := A.exists_actual_collarFibre hf i
  let W : SurfacePlane × ℝ → ℝ := fun p =>
    c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm (p.2, p.1))
  let V : Displacement → ℝ := fun z =>
    ∫ y in c.disk, MovingCollar.parametricFibre W (c.movingGap f) η (y, z)
  refine ⟨δ, hδ, V, ?_, ?_, ?_⟩
  · let μ : Measure SurfacePlane := volume.restrict c.disk
    have hm : μ.restrict c.closedDisk = μ := by
      dsimp only [μ, CollarHeightChart.disk, CollarHeightChart.closedDisk]
      rw [Measure.restrict_restrict measurableSet_closedBall,
        inter_eq_right.mpr Metric.ball_subset_closedBall]
    have hV : V = fun z =>
        ∫ y in c.closedDisk, MovingCollar.parametricFibre W (c.movingGap f) η (y, z) ∂μ := by
      funext z
      change _ = ∫ y, _ ∂μ.restrict c.closedDisk
      rw [hm]
    rw [hV]
    apply MovingCollar.contDiffAt_averagedFibre (isCompact_closedBall _ _) hδ
    · intro y hy
      have ht : jointHeightCoordinates.symm (0, y) ∈ c.chart.target :=
        c.ball_subset (c.rectangle_subset 0
          ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
      have hw : ContDiffAt ℝ 2 (A.weights i) (c.chart.symm (jointHeightCoordinates.symm (0, y))) :=
        (A.weights i).contMDiff.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      exact (c.contDiffAt_weightedJacobian ht hw).comp (y, 0)
        (jointHeightCoordinates.symm.contDiff.contDiffAt.comp (y, 0)
          (contDiffAt_snd.prodMk contDiffAt_fst))
    · exact c.contDiffAt_movingGap_zero hf.toRegularHeightPair
    · exact fun y hy => (hη y hy 0 (Metric.mem_ball_self hδ)).1
    · exact hη₀
    · exact fun y hy z hz => (hη y hy z hz).2
  · change (∫ y in c.disk, MovingCollar.parametricFibre W (c.movingGap f) η (y, 0)) = 0
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    simp [MovingCollar.parametricFibre, hη₀ y (Metric.ball_subset_closedBall hy)]
  · intro z hz hc
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact (heq y (Metric.ball_subset_closedBall hy) z hz hc).symm

/-- The actual correction in ambient coordinates is the common finite sum
of its weighted chart contributions. Only this correction is partitioned. -/
theorem shortOverlapCollarCorrection_eq_sum (hf : AdmissibleTwoFace h f)
    (z : Displacement) (hz : 2 * ‖z‖ < A.width) :
    shortOverlapCollarCorrection h f z =
      ∑ i, ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p *
          max 0 (shortOverlapGap f z ((A.charts i).chart.symm p) -
            h ((A.charts i).chart.symm p)) := by
  have hopen : MeasurableSet {x : JointSpace | 0 < h x} :=
    (hf.toGraphCapData.isOpen_positive.preimage (PiLp.continuous_equiv 2 _)).measurableSet
  have he : shortOverlapCollarCorrection h f z =
      ∫ x in {x : JointSpace | 0 < h x ∧ h x < A.width},
        max 0 (shortOverlapGap f z x - h x) := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hopen (fun _ hx => hx.1)
    intro x hx
    apply hf.shortOverlapCollar_integrand_eq_zero
    have hh : A.width ≤ h x := le_of_not_gt (fun ht => hx.2 ⟨hx.1, ht⟩)
    exact hz.le.trans hh
  rw [he, setIntegral_congr_set (hf.toAdmissibleGraphCap.ae_openCollar_eq_closedCollar A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩))]
  apply A.integral_closedCollar_eq_sum hf.toAdmissibleGraphCap
  have hfc : Continuous (fun x : JointSpace => f x) :=
    hf.strictGraphLipschitz_upper.continuous.comp (PiLp.continuous_equiv 2 _)
  have hq : Continuous (shortOverlapGap f z) :=
    ((continuous_const : Continuous (fun _ : JointSpace => z.1)).sub
      (hfc.comp (continuous_id.add continuous_const))).add hfc
  have hc : ContinuousOn (fun x => max 0 (shortOverlapGap f z x - h x)) (graphClosedCollar h A.width) :=
    continuousOn_const.sup (hq.continuousOn.sub
      (hf.toAdmissibleGraphCap.continuousOn_closedPositive.mono inter_subset_left))
  exact hc.integrableOn_compact (hf.toAdmissibleGraphCap.isCompact_closedCollar A.width)

/-- Signed Fubini in a collar chart, on its original fixed rectangle. -/
theorem integral_chart_correction (hf : AdmissibleTwoFace h f) (i : Fin A.count)
    (z : Displacement) :
    (∫ p in (A.charts i).parameterRegion A.width,
      (A.charts i).weightedJacobian (A.weights i) p *
        max 0 (shortOverlapGap f z ((A.charts i).chart.symm p) - h ((A.charts i).chart.symm p))) =
      ∫ y in (A.charts i).disk, ∫ t in (0 : ℝ)..A.width,
        (A.charts i).weightedJacobian (A.weights i) (jointHeightCoordinates.symm (t, y)) *
          max 0 ((A.charts i).movingGap f ((y, z), t) - t) := by
  let c := A.charts i
  let F : ℝ × SurfacePlane → ℝ := fun p =>
    c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm p) *
      max 0 (c.movingGap f ((p.2, z), p.1) - p.1)
  have htarget (p : ℝ × SurfacePlane) (hp : p ∈ Icc 0 A.width ×ˢ c.closedDisk) :
      jointHeightCoordinates.symm p ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset p.1
      ⟨(neg_nonpos.mpr c.width_pos.le).trans hp.1.1, hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)
  have hΦ : ContinuousOn (fun p : ℝ × SurfacePlane => c.chart.symm (jointHeightCoordinates.symm p))
      (Icc 0 A.width ×ˢ c.closedDisk) :=
    c.chart.symm.continuousOn.comp jointHeightCoordinates.symm.continuous.continuousOn htarget
  have hfc : Continuous (fun x : JointSpace => f x) :=
    hf.strictGraphLipschitz_upper.continuous.comp (PiLp.continuous_equiv 2 _)
  have hq : ContinuousOn (fun p : ℝ × SurfacePlane => c.movingGap f ((p.2, z), p.1))
      (Icc 0 A.width ×ˢ c.closedDisk) := by
    exact ((continuousOn_const (c := z.1)).sub
      (hfc.comp_continuousOn (hΦ.add (continuousOn_const (c := z.2))))).add
        (hfc.comp_continuousOn hΦ)
  have hF : ContinuousOn F (Icc 0 A.width ×ˢ c.closedDisk) :=
    ((c.continuousOn_weightedJacobian (A.weights i) (A.weights i).contMDiff.continuous).comp
      jointHeightCoordinates.symm.continuous.continuousOn htarget).mul
        (continuousOn_const.sup (hq.sub continuous_fst.continuousOn))
  have hi : IntegrableOn F (Icc 0 A.width ×ˢ c.disk) :=
    (hF.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
      (prod_mono Subset.rfl Metric.ball_subset_closedBall)
  have hpre : jointHeightCoordinates.symm ⁻¹' c.parameterRegion A.width = Icc 0 A.width ×ˢ c.disk := by
    ext p
    change jointHeightCoordinates (jointHeightCoordinates.symm p) ∈ Icc 0 A.width ×ˢ c.disk ↔
      p ∈ Icc 0 A.width ×ˢ c.disk
    rw [jointHeightCoordinates.apply_symm_apply]
  rw [← (jointHeightCoordinates_symm_measurePreserving.restrict_preimage_emb
    jointHeightCoordinates.symm.toHomeomorph.measurableEmbedding (c.parameterRegion A.width)).integral_comp
      jointHeightCoordinates.symm.toHomeomorph.measurableEmbedding, hpre]
  have heq : (∫ p : ℝ × SurfacePlane in Icc 0 A.width ×ˢ c.disk,
      c.weightedJacobian (A.weights i) (jointHeightCoordinates.symm p) *
        max 0 (shortOverlapGap f z (c.chart.symm (jointHeightCoordinates.symm p)) -
          h (c.chart.symm (jointHeightCoordinates.symm p)))) =
        ∫ p in Icc 0 A.width ×ˢ c.disk, F p := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_ball)
    intro p hp
    dsimp only
    rw [c.height_symm _ (htarget p ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩)]
    rfl
  rw [heq]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hi' : Integrable F ((volume.restrict (Icc 0 A.width)).prod (volume.restrict c.disk)) := by
    simpa only [Measure.volume_eq_prod, Measure.prod_restrict] using hi
  rw [integral_prod_symm F hi']
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  dsimp only
  rw [intervalIntegral.integral_of_le A.width_pos.le, ← integral_Icc_eq_integral_Ioc]

include A in
/-- C³ local extension of the complete actual collar correction, obtained
by the fixed finite atlas and signed planar integration. -/
theorem exists_contDiff_collarCorrection (hf : AdmissibleTwoFace h f) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ V : Displacement → ℝ, ContDiffAt ℝ 3 V 0 ∧ V 0 = 0 ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        V z = shortOverlapCollarCorrection h f z := by
  classical
  choose d hd V hV hV₀ heq using A.exists_contDiff_chartCorrection hf
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ δ < A.width / 4 ∧ ∀ i, δ < d i :=
    (show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
      (nhdsWithin_le_nhds ((gt_mem_nhds (div_pos A.width_pos (by norm_num))).and
        (eventually_all.mpr fun i => gt_mem_nhds (hd i))))
  obtain ⟨δ, hδ, hδw, hδd⟩ := hsmall.exists
  refine ⟨δ, hδ, fun z => ∑ i, V i z, ContDiffAt.sum (fun i _ => hV i), ?_, ?_⟩
  · simp [hV₀]
  · intro z hz hc
    have hzn : ‖z‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [A.shortOverlapCollarCorrection_eq_sum hf z (by nlinarith [norm_nonneg z])]
    apply Finset.sum_congr rfl
    intro i _
    rw [heq i z (by simpa only [Metric.mem_ball, dist_zero_right] using hzn.trans (hδd i)) hc,
      A.integral_chart_correction hf i z]

end ControlledCollarAtlas

namespace AdmissibleTwoFace

variable {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
include hf

/-- A local C³ extension of the ACTUAL overlap difference on a common
future-cone neighborhood. No overlap jet or analytic remainder premise is
inserted into admissibility. This theorem does not yet identify its two-jet. -/
theorem exists_contDiff_overlapDifference :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Displacement → ℝ, ContDiffAt ℝ 3 F 0 ∧ F 0 = 0 ∧
      ∀ z ∈ Metric.ball (0 : Displacement) δ, ‖z.2‖ ≤ z.1 →
        F z = translatedOverlap (twoFaceRegion h f) (displacementSpacetime z) -
          translatedOverlap (graphCapRegion h) (displacementSpacetime z) := by
  obtain ⟨A⟩ := hf.toAdmissibleGraphCap.exists_controlledCollarAtlas
  obtain ⟨d, hd, V, hV, hV₀, heV⟩ := A.exists_contDiff_collarCorrection hf
  obtain ⟨e, he, W, hW, hW₀, heW⟩ :=
    A.exists_contDiff_collarCorrection hf.toAdmissibleGraphCap.twoFace_planar
  let F : Displacement → ℝ := fun z =>
    (∫ x : JointSpace in {x : JointSpace | 0 < h x}, f (x + z.2) - f x) + V z - W z
  refine ⟨min d e, lt_min hd he, F, (hf.contDiffAt_shortOverlapBulk.add hV).sub hW, ?_, ?_⟩
  · simp [F, hV₀, hW₀]
  · intro z hz hc
    rw [hf.translatedOverlap_sub_planar z hc]
    change _ + V z - W z = _
    rw [heV z (Metric.ball_subset_ball (min_le_left d e) hz) hc,
      heW z (Metric.ball_subset_ball (min_le_right d e) hz) hc]

end AdmissibleTwoFace
end BoundaryDraft
