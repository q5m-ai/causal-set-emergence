import BoundaryDraft.Pilot3Overlap
import BoundaryDraft.Pilot3Endpoints
import BoundaryDraft.MovingCollarIntegral

/-!
# The actual short moving collar in the smooth three-dimensional pilot

Only the collar correction is partitioned, through the existing
`Pilot3CollarAtlas`. The original region, causal overlap, spatial coordinates
and canonical line measure are unchanged. Uniform roots are derived from the
actual contact equation. Signed Fubini uses compact fixed rectangles; all
partner components and positive-height critical points are retained.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

@[simp] theorem pilot3ShortGap_zero (f : Pilot3Space → ℝ) (x : Pilot3Space) :
    pilot3ShortGap f 0 x = 0 := by simp [pilot3ShortGap]

/-- The correction is supported in the original positive source region,
not in an extension containing unrelated exterior zeros. -/
def pilot3ShortCollarCorrection (h f : Pilot3Space → ℝ) (z : Pilot3Spacetime) : ℝ :=
  ∫ x in {x | 0 < h x}, max 0 (pilot3ShortGap f z x - h x)

namespace SmoothPilot3
variable {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f)
include hf

theorem future_contDiffAt_three (x : Pilot3Space) (hx : x ∈ pilot3ClosedPositive h) :
    ContDiffAt ℝ 3 f x := (hf.future_smoothAt x hx).of_le (WithTop.coe_le_coe.mpr le_top)

/-- A global bound for the actual short gap, including noncausal parameters. -/
theorem abs_shortGap_le (z : Pilot3Spacetime) (x : Pilot3Space) :
    |pilot3ShortGap f z x| ≤ 2 * ‖z‖ := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  have hb := C.future_increment x z.2
  have ht : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hη : η ≤ 1 := by linarith [C.budget, C.height_nonneg]
  have hb' : |f (x + z.2) - f x| ≤ ‖z‖ :=
    hb.trans ((mul_le_of_le_one_left (norm_nonneg _) hη).trans (norm_snd_le z))
  calc
    |pilot3ShortGap f z x| = |z.1 - (f (x + z.2) - f x)| := by congr 1; unfold pilot3ShortGap; ring
    _ ≤ |z.1| + |f (x + z.2) - f x| := abs_sub _ _
    _ ≤ 2 * ‖z‖ := by linarith

theorem shortGap_nonneg (z : Pilot3Spacetime) (hz : ‖z.2‖ ≤ z.1) (x : Pilot3Space) :
    0 ≤ pilot3ShortGap f z x := by
  obtain ⟨κ, η, C⟩ := hf.exists_slopeControl
  exact (mul_nonneg (by linarith [C.budget, C.height_nonneg])
    ((norm_nonneg _).trans hz)).trans (C.shortGap_bounds z hz x).1

theorem shortCollar_integrand_eq_zero (z : Pilot3Spacetime) (x : Pilot3Space)
    (hx : 2 * ‖z‖ ≤ h x) : max 0 (pilot3ShortGap f z x - h x) = 0 := by
  apply max_eq_left
  have hb := (le_abs_self (pilot3ShortGap f z x)).trans (hf.abs_shortGap_le z x)
  linarith

end SmoothPilot3

namespace Pilot3HeightChart
variable {h : Pilot3Space → ℝ} (c : Pilot3HeightChart h)

theorem contDiffAt_symm_three (p : Pilot3Space) (hp : p ∈ c.chart.target) :
    ContDiffAt ℝ 3 c.chart.symm p :=
  (c.contDiff_symm.contDiffAt (c.chart.open_target.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)

end Pilot3HeightChart
namespace Pilot3CollarChart
variable {h f : Pilot3Space → ℝ} (c : Pilot3CollarChart h)

/-- The actual smooth chart inverse, in base/displacement/height order. -/
def movingPoint (p : (ℝ × Pilot3Spacetime) × ℝ) : Pilot3Space :=
  c.chart.symm (pilot3Coordinates.symm (p.2, p.1.1))

/-- The actual lost vertical slice in a canonical height chart. -/
def movingGap (f : Pilot3Space → ℝ) (p : (ℝ × Pilot3Spacetime) × ℝ) : ℝ :=
  pilot3ShortGap f p.1.2 (c.movingPoint p)

/-- Smoothness at every point of the compact one-dimensional base disk. -/
theorem contDiffAt_movingGap_zero (hf : SmoothPilot3 h f)
    (y : ℝ) (hy : y ∈ c.closedDisk) :
    ContDiffAt ℝ 3 (c.movingGap f) ((y, 0), 0) := by
  have ht : pilot3Coordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hx : c.movingPoint ((y, 0), 0) ∈ pilot3ClosedPositive h :=
    c.symm_mem_closedPositive _ ht le_rfl
  have hφ : ContDiffAt ℝ 3 c.movingPoint ((y, 0), 0) :=
    (c.contDiffAt_symm_three _ ht).comp ((y, 0), 0)
      (pilot3Coordinates.symm.contDiff.contDiffAt.comp ((y, 0), 0)
        (contDiffAt_snd.prodMk contDiffAt_fst.fst))
  have hfx := hf.future_contDiffAt_three _ hx
  have hb : ContDiffAt ℝ 3 f
      (c.movingPoint ((y, 0), 0) + (0 : Pilot3Spacetime).2) := by simpa using hfx
  exact (contDiffAt_fst.snd.fst.sub (hb.comp ((y, 0), 0)
    (hφ.add contDiffAt_fst.snd.snd))).add (hfx.comp ((y, 0), 0) hφ)

/-- The actual contact equation supplies its root by the implicit function
theorem; no overlap-regularity or root-selection hypothesis is added. -/
theorem exists_contDiff_movingRoot (hf : SmoothPilot3 h f)
    (y : ℝ) (hy : y ∈ c.closedDisk) :
    ∃ η : ℝ × Pilot3Spacetime → ℝ,
      η (y, 0) = 0 ∧ ContDiffAt ℝ 3 η (y, 0) ∧
      (∀ᶠ p in 𝓝 (y, (0 : Pilot3Spacetime)),
        η p = c.movingGap f (p, η p)) ∧
      (∀ᶠ a in 𝓝 ((y, (0 : Pilot3Spacetime)), (0 : ℝ)),
        a.2 = c.movingGap f a → a.2 = η a.1) := by
  let a : (ℝ × Pilot3Spacetime) × ℝ := ((y, 0), 0)
  let x : Pilot3Space := c.movingPoint a
  have ht : pilot3Coordinates.symm (0, y) ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset 0
      ⟨neg_nonpos.mpr c.width_pos.le, c.width_pos.le⟩ y hy)
  have hx : x ∈ pilot3ClosedPositive h := c.symm_mem_closedPositive _ ht le_rfl
  have hφ : ContDiffAt ℝ 3 c.movingPoint a :=
    (c.contDiffAt_symm_three _ ht).comp a
      (pilot3Coordinates.symm.contDiff.contDiffAt.comp a
        (contDiffAt_snd.prodMk contDiffAt_fst.fst))
  have hfx := hf.future_contDiffAt_three x hx
  have hq : ContDiffAt ℝ 3 (c.movingGap f) a := c.contDiffAt_movingGap_zero hf y hy
  let D := fderiv ℝ f x
  let L : (ℝ × Pilot3Spacetime) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ Pilot3Space).comp
      (ContinuousLinearMap.snd ℝ ℝ Pilot3Spacetime) -
    D.comp ((ContinuousLinearMap.snd ℝ ℝ Pilot3Space).comp
      (ContinuousLinearMap.snd ℝ ℝ Pilot3Spacetime))
  have hφD := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hfxD : HasFDerivAt f D x := (hfx.differentiableAt (by norm_num)).hasFDerivAt
  have hfxb : HasFDerivAt f D (c.movingPoint a + a.1.2.2) := by simpa [a, x] using hfxD
  let S : ((ℝ × Pilot3Spacetime) × ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ Pilot3Space).comp
      (ContinuousLinearMap.snd ℝ ℝ Pilot3Spacetime)).comp
        (ContinuousLinearMap.fst ℝ (ℝ × Pilot3Spacetime) ℝ)
  let B : ((ℝ × Pilot3Spacetime) × ℝ) →L[ℝ] Pilot3Space :=
    ((ContinuousLinearMap.snd ℝ ℝ Pilot3Space).comp
      (ContinuousLinearMap.snd ℝ ℝ Pilot3Spacetime)).comp
        (ContinuousLinearMap.fst ℝ (ℝ × Pilot3Spacetime) ℝ)
  have hD : HasFDerivAt (c.movingGap f)
      (L.comp (ContinuousLinearMap.fst ℝ (ℝ × Pilot3Spacetime) ℝ)) a := by
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

/-- A single root function and two positive radii work on the entire compact
base disk, including overlaps and chart seams. -/
theorem exists_uniform_movingRoots (hf : SmoothPilot3 h f) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ∃ η : ℝ × Pilot3Spacetime → ℝ,
      (∀ y ∈ c.closedDisk, η (y, 0) = 0) ∧
      ∀ y ∈ c.closedDisk, ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ,
        ContDiffAt ℝ 3 η (y, z) ∧ |η (y, z)| < ε ∧
          η (y, z) = c.movingGap f ((y, z), η (y, z)) ∧
          ∀ t, |t| < ε → t = c.movingGap f ((y, z), t) → t = η (y, z) := by
  apply MovingCollar.exists_uniform_roots (isCompact_closedBall _ _)
  · intro y
    simp [movingGap]
  · exact c.exists_contDiff_movingRoot hf

end Pilot3CollarChart
namespace Pilot3CollarAtlas
variable {h f : Pilot3Space → ℝ} (A : Pilot3CollarAtlas h)

/-- The oriented integral extends the actual causal collar off the cone. -/
def movingFibre (i : Fin A.count) (f : Pilot3Space → ℝ) (y : ℝ)
    (η : Pilot3Spacetime → ℝ) (z : Pilot3Spacetime) : ℝ :=
  MovingCollar.fibre
    (fun t => (A.charts i).weightedJacobian (A.weights i) (pilot3Coordinates.symm (t, y)))
    (fun p : Pilot3Spacetime × ℝ => (A.charts i).movingGap f ((y, p.1), p.2)) η z

/-- Uniform roots represent the actual positive-part collar integral on the
causal ball, with the vertex and null displacements included. -/
theorem exists_actual_collarFibre (hf : SmoothPilot3 h f) (i : Fin A.count) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ × Pilot3Spacetime → ℝ,
      (∀ y ∈ (A.charts i).closedDisk, η (y, 0) = 0) ∧
      (∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ,
        ContDiffAt ℝ 3 η (y, z) ∧
          η (y, z) = (A.charts i).movingGap f ((y, z), η (y, z))) ∧
      ∀ y ∈ (A.charts i).closedDisk, ∀ z ∈ Metric.ball (0 : Pilot3Spacetime) δ,
        ‖z.2‖ ≤ z.1 →
        (∫ t in (0 : ℝ)..A.width,
          (A.charts i).weightedJacobian (A.weights i) (pilot3Coordinates.symm (t, y)) *
            max 0 ((A.charts i).movingGap f ((y, z), t) - t)) =
          A.movingFibre i f y (fun z => η (y, z)) z := by
  let c := A.charts i
  obtain ⟨ε, δ₀, hε, hδ₀, η, hη₀, hη⟩ := c.exists_uniform_movingRoots hf
  let δ := min δ₀ (min ε A.width / 4)
  have hδ : 0 < δ := lt_min hδ₀ (div_pos (lt_min hε A.width_pos) (by norm_num))
  have hzδ (z : Pilot3Spacetime) (hz : z ∈ Metric.ball (0 : Pilot3Spacetime) δ) :
      z ∈ Metric.ball (0 : Pilot3Spacetime) δ₀ ∧ 2 * ‖z‖ < ε ∧ 2 * ‖z‖ < A.width := by
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
      hf.abs_shortGap_le z (c.movingPoint ((y, z), t))
    have hnonneg (t : ℝ) : 0 ≤ c.movingGap f ((y, z), t) :=
      hf.shortGap_nonneg z hcausal _
    have hηpos : η (y, z) ∈ Icc 0 A.width := by
      rw [hroot]
      exact ⟨hnonneg _, ((le_abs_self _).trans (hbound _)).trans (hzδ z hz).2.2.le⟩
    have htarget (t : ℝ) (ht : t ∈ Icc 0 A.width) :
        pilot3Coordinates.symm (t, y) ∈ c.chart.target :=
      c.ball_subset (c.rectangle_subset t
        ⟨(neg_nonpos.mpr c.width_pos.le).trans ht.1, ht.2.trans (A.width_lt i).le⟩ y hy)
    have hΦ : ContinuousOn (fun t => c.movingPoint ((y, z), t)) (Icc 0 A.width) :=
      c.chart.symm.continuousOn.comp
        (pilot3Coordinates.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn htarget
    have hqc : ContinuousOn (fun t => c.movingGap f ((y, z), t)) (Icc 0 A.width) :=
      (hf.continuous_shortGap z).comp_continuousOn hΦ
    have hwc : ContinuousOn
        (fun t => c.weightedJacobian (A.weights i) (pilot3Coordinates.symm (t, y)))
        (Icc 0 A.width) :=
      (c.continuousOn_weightedJacobian (A.weights i) (A.weights i).contMDiff.continuous).comp
        (pilot3Coordinates.symm.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn htarget
    apply MovingCollar.integral_positivePart_eq_root hηpos hqc hwc (hnonneg 0)
      (((le_abs_self _).trans (hbound A.width)).trans_lt (hzδ z hz).2.2) hroot
    intro t _ ht
    exact hηp.2.2.2 t (by rw [ht]; exact (hbound t).trans_lt (hzδ z hz).2.1) ht

/-- Only the regular boundary collar is partitioned; the fixed positive-height
interior is not subjected to a noncriticality hypothesis. -/
theorem shortCollarCorrection_eq_sum (hf : SmoothPilot3 h f)
    (z : Pilot3Spacetime) (hz : 2 * ‖z‖ < A.width) :
    pilot3ShortCollarCorrection h f z =
      ∑ i, ∫ p in (A.charts i).parameterRegion A.width,
        (A.charts i).weightedJacobian (A.weights i) p *
          max 0 (pilot3ShortGap f z ((A.charts i).chart.symm p) -
            h ((A.charts i).chart.symm p)) := by
  have hopen : MeasurableSet {x : Pilot3Space | 0 < h x} :=
    hf.toPilot3RegularHeight.isOpen_positive.measurableSet
  have he : pilot3ShortCollarCorrection h f z =
      ∫ x in {x : Pilot3Space | 0 < h x ∧ h x < A.width},
        max 0 (pilot3ShortGap f z x - h x) := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hopen (fun _ hx => hx.1)
    intro x hx
    apply hf.shortCollar_integrand_eq_zero
    have hh : A.width ≤ h x := le_of_not_gt (fun ht => hx.2 ⟨hx.1, ht⟩)
    exact hz.le.trans hh
  rw [he, setIntegral_congr_set (hf.toPilot3RegularHeight.ae_openCollar_eq_closedCollar A.width
    (fun x hx => A.noncritical x ⟨hx.1, hx.2.le⟩))]
  apply A.integral_closedCollar_eq_sum hf.toPilot3RegularHeight
  have hc : ContinuousOn (fun x => max 0 (pilot3ShortGap f z x - h x)) (pilot3ClosedCollar h A.width) :=
    continuousOn_const.sup ((hf.continuous_shortGap z).continuousOn.sub
      (hf.toPilot3RegularHeight.continuousOn_closedPositive.mono inter_subset_left))
  exact hc.integrableOn_compact (hf.toPilot3RegularHeight.isCompact_closedCollar A.width)

/-- Signed Fubini in the canonical chart. The base has dimension ONE, with
ordinary Lebesgue measure and no angular or surface normalization factor. -/
theorem integral_chart_correction (hf : SmoothPilot3 h f) (i : Fin A.count)
    (z : Pilot3Spacetime) :
    (∫ p in (A.charts i).parameterRegion A.width,
      (A.charts i).weightedJacobian (A.weights i) p *
        max 0 (pilot3ShortGap f z ((A.charts i).chart.symm p) - h ((A.charts i).chart.symm p))) =
      ∫ y in (A.charts i).disk, ∫ t in (0 : ℝ)..A.width,
        (A.charts i).weightedJacobian (A.weights i) (pilot3Coordinates.symm (t, y)) *
          max 0 ((A.charts i).movingGap f ((y, z), t) - t) := by
  let c := A.charts i
  let F : ℝ × ℝ → ℝ := fun p =>
    c.weightedJacobian (A.weights i) (pilot3Coordinates.symm p) *
      max 0 (c.movingGap f ((p.2, z), p.1) - p.1)
  have htarget (p : ℝ × ℝ) (hp : p ∈ Icc 0 A.width ×ˢ c.closedDisk) :
      pilot3Coordinates.symm p ∈ c.chart.target :=
    c.ball_subset (c.rectangle_subset p.1
      ⟨(neg_nonpos.mpr c.width_pos.le).trans hp.1.1, hp.1.2.trans (A.width_lt i).le⟩ p.2 hp.2)
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => c.chart.symm (pilot3Coordinates.symm p))
      (Icc 0 A.width ×ˢ c.closedDisk) :=
    c.chart.symm.continuousOn.comp pilot3Coordinates.symm.continuous.continuousOn htarget
  have hq : ContinuousOn (fun p : ℝ × ℝ => c.movingGap f ((p.2, z), p.1))
      (Icc 0 A.width ×ˢ c.closedDisk) :=
    (hf.continuous_shortGap z).comp_continuousOn hΦ
  have hF : ContinuousOn F (Icc 0 A.width ×ˢ c.closedDisk) :=
    ((c.continuousOn_weightedJacobian (A.weights i) (A.weights i).contMDiff.continuous).comp
      pilot3Coordinates.symm.continuous.continuousOn htarget).mul
        (continuousOn_const.sup (hq.sub continuous_fst.continuousOn))
  have hi : IntegrableOn F (Icc 0 A.width ×ˢ c.disk) :=
    (hF.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
      (prod_mono Subset.rfl Metric.ball_subset_closedBall)
  have hpre : pilot3Coordinates.symm ⁻¹' c.parameterRegion A.width = Icc 0 A.width ×ˢ c.disk := by
    ext p
    change pilot3Coordinates (pilot3Coordinates.symm p) ∈ Icc 0 A.width ×ˢ c.disk ↔
      p ∈ Icc 0 A.width ×ˢ c.disk
    rw [pilot3Coordinates.apply_symm_apply]
  rw [← (pilot3Coordinates_symm_measurePreserving.restrict_preimage_emb
    pilot3Coordinates.symm.toHomeomorph.measurableEmbedding (c.parameterRegion A.width)).integral_comp
      pilot3Coordinates.symm.toHomeomorph.measurableEmbedding, hpre]
  have heq : (∫ p : ℝ × ℝ in Icc 0 A.width ×ˢ c.disk,
      c.weightedJacobian (A.weights i) (pilot3Coordinates.symm p) *
        max 0 (pilot3ShortGap f z (c.chart.symm (pilot3Coordinates.symm p)) -
          h (c.chart.symm (pilot3Coordinates.symm p)))) =
        ∫ p in Icc 0 A.width ×ˢ c.disk, F p := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_ball)
    intro p hp
    dsimp only
    rw [c.height_symm _ (htarget p ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩)]
    rfl
  rw [heq, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hi' : Integrable F ((volume.restrict (Icc 0 A.width)).prod (volume.restrict c.disk)) := by
    simpa only [Measure.volume_eq_prod, Measure.prod_restrict] using hi
  rw [integral_prod_symm F hi']
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  dsimp only
  rw [intervalIntegral.integral_of_le A.width_pos.le, ← integral_Icc_eq_integral_Ioc]

end Pilot3CollarAtlas
end BoundaryDraft
