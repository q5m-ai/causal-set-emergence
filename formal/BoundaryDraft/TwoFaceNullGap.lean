import BoundaryDraft.TwoFaceOverlap

/-!
# Near-null gap estimates for the unchanged two-face geometry

These are preparatory estimates for #61, NOT the quadratic expansion of the
averaged density. Long-coordinate integration must still be shown to regularize
the positive part with a uniformly dominated second-order remainder.

The estimates retain zero gaps (translated contacts). They use the causal
positive-part envelope, never global regularity of the raw height. At a fixed
positive cutoff both endpoints of a nonnegative gap lie strictly inside the
positive region, where the original smooth face germs are available.
-/

open MeasureTheory Set

noncomputable section
namespace BoundaryDraft

/-- The vertical gap whose positive part gives the causal translated overlap.
`x` and `y` are the two spatial endpoints, and `s` is elapsed coordinate time. -/
def twoFaceGap (h f : Spatial → ℝ) (x y : Spatial) (s : ℝ) : ℝ :=
  max 0 (h x) + f y - f x - s

/-- The SAME gap in the coordinates of `properTimeDisplacement`. This is not
a replacement density, overlap, region, or action. -/
def twoFaceRayGap (h f : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    (σ v : ℝ) : ℝ :=
  twoFaceGap h f x (x + spatialPolar ω ((v - σ / v) / 2)) ((v + σ / v) / 2)

/-- Exact compatibility with the already proved causal graph-overlap formula. -/
theorem AdmissibleTwoFace.translatedOverlap_eq_gap {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) {s : ℝ} {a : Spatial}
    (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoFaceRegion h f) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (twoFaceGap h f x (x + a) s) := by
  rw [hf.translatedOverlap_causal hz]
  congr 1
  funext x
  congr 1
  unfold twoFaceGap
  ring

/-- Euclidean, not coordinate-supremum, distance along one polar ray. -/
theorem spatialDistance_polar_ray (x : Spatial) (ω : OverlapSphere) (r t : ℝ) :
    spatialDistance (x + spatialPolar ω r) (x + spatialPolar ω t) = |t - r| := by
  have he : x + spatialPolar ω t - (x + spatialPolar ω r) = spatialPolar ω (t - r) := by
    ext i
    change x i + t * ω.val i - (x i + r * ω.val i) = (t - r) * ω.val i
    ring
  rw [spatialDistance, he]
  change ‖(t - r) • ω.val‖ = _
  rw [norm_smul, mem_sphere_zero_iff_norm.mp ω.property, mul_one, Real.norm_eq_abs]

/-- At the null cone the long coordinate is uniformly transverse to the gap
zero set, irrespective of tangencies in the spatial variables or direction. -/
theorem twoFaceRayGap_null_sub_le {f : Spatial → ℝ} {η : ℝ}
    (hlip : ∀ x y, |f x - f y| ≤ η * spatialDistance x y)
    (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere) {v w : ℝ} (hvw : v ≤ w) :
    twoFaceRayGap h f x ω 0 w - twoFaceRayGap h f x ω 0 v ≤
      -(1 - η) * (w - v) / 2 := by
  have hb := (abs_le.mp (hlip (x + spatialPolar ω (w / 2))
    (x + spatialPolar ω (v / 2)))).2
  rw [spatialDistance_polar_ray, abs_of_nonpos (by linarith : v / 2 - w / 2 ≤ 0)] at hb
  simp only [twoFaceRayGap, twoFaceGap, zero_div, sub_zero, add_zero]
  linarith

/-- Increasing proper-time square shrinks the gap at a controlled rate.
Both inequalities hold pointwise, including on the entire contact set. -/
theorem twoFaceRayGap_transverse_bounds {f : Spatial → ℝ} {η : ℝ}
    (hlip : ∀ x y, |f x - f y| ≤ η * spatialDistance x y)
    (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    {σ τ v : ℝ} (hv : 0 < v) (hst : σ ≤ τ) :
    -(1 + η) * (τ - σ) / (2 * v) ≤
      twoFaceRayGap h f x ω τ v - twoFaceRayGap h f x ω σ v ∧
    twoFaceRayGap h f x ω τ v - twoFaceRayGap h f x ω σ v ≤
      -(1 - η) * (τ - σ) / (2 * v) := by
  have hd : (v - σ / v) / 2 - (v - τ / v) / 2 = (τ - σ) / (2 * v) := by ring
  have hb := abs_le.mp (hlip (x + spatialPolar ω ((v - τ / v) / 2))
    (x + spatialPolar ω ((v - σ / v) / 2)))
  rw [spatialDistance_polar_ray, hd,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) (by positivity))] at hb
  have he : twoFaceRayGap h f x ω τ v - twoFaceRayGap h f x ω σ v =
      (f (x + spatialPolar ω ((v - τ / v) / 2)) -
        f (x + spatialPolar ω ((v - σ / v) / 2))) - (τ - σ) / (2 * v) := by
    unfold twoFaceRayGap twoFaceGap
    ring
  rw [he]
  constructor
  · calc
      _ = -(η * ((τ - σ) / (2 * v))) - (τ - σ) / (2 * v) := by ring
      _ ≤ _ := sub_le_sub_right hb.1 _
  · calc
      _ ≤ η * ((τ - σ) / (2 * v)) - (τ - σ) / (2 * v) := sub_le_sub_right hb.2 _
      _ = _ := by ring

/-- A contact exactly at the long cutoff never opens on the right. This does
not assume that the set of such spatial points or directions is null. -/
theorem twoFaceRayGap_nonpos_of_cutoff {f : Spatial → ℝ} {η : ℝ} (hη : η < 1)
    (hlip : ∀ x y, |f x - f y| ≤ η * spatialDistance x y)
    (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    {δ σ v : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) (hv : δ ≤ v)
    (hcontact : twoFaceRayGap h f x ω 0 δ ≤ 0) :
    twoFaceRayGap h f x ω σ v ≤ 0 := by
  have hv0 : 0 < v := hδ.trans_le hv
  have hlong := twoFaceRayGap_null_sub_le hlip h x ω hv
  have htrans := (twoFaceRayGap_transverse_bounds hlip h x ω hv0 hσ).2
  have hlong_nonpos : -(1 - η) * (v - δ) / 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hv)) (by norm_num)
  have htrans_nonpos : -(1 - η) * (σ - 0) / (2 * v) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

/-- Both spatial endpoints of EVERY nonnegative causal gap have a uniform
positive-height margin proportional to elapsed time. The bound includes zero
gaps, not just positive overlaps, and is derived from the unchanged budget. -/
theorem AdmissibleTwoFace.exists_gap_height_margin {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) :
    ∃ m : ℝ, 0 < m ∧ ∀ (x y : Spatial) (s : ℝ),
      spatialDistance x y ≤ s → 0 ≤ twoFaceGap h f x y s →
      m * s ≤ max 0 (h x) ∧ m * s ≤ max 0 (h y) := by
  obtain ⟨κ, η, hκ, hη, hbudget, hh, hfl⟩ := hf.slope_budget
  refine ⟨1 - κ - η, by linarith, ?_⟩
  intro x y s hds hgap
  have hs : 0 ≤ s := (spatialDistance_nonneg x y).trans hds
  have hfuture := (abs_le.mp (hfl y x)).2
  rw [spatialDistance_symm y x] at hfuture
  have hheight := (abs_le.mp (hh x y)).2
  have hηd := mul_le_mul_of_nonneg_left hds hη
  have hκd := mul_le_mul_of_nonneg_left hds hκ
  have hκs := mul_nonneg hκ hs
  dsimp only [twoFaceGap] at hgap
  constructor <;> nlinarith

/-- A positive causal separation puts both endpoints inside the original
positive region, even at a translated tangency. No smooth extension of the
raw height outside that region is required for these endpoints. -/
theorem AdmissibleTwoFace.gap_endpoints_positive {h f : Spatial → ℝ}
    (hf : AdmissibleTwoFace h f) {x y : Spatial} {s : ℝ} (hs : 0 < s)
    (hds : spatialDistance x y ≤ s) (hgap : 0 ≤ twoFaceGap h f x y s) :
    0 < h x ∧ 0 < h y := by
  obtain ⟨m, hm, hmargin⟩ := hf.exists_gap_height_margin
  have hb := hmargin x y s hds hgap
  have hx : 0 < max 0 (h x) := (mul_pos hm hs).trans_le hb.1
  have hy : 0 < max 0 (h y) := (mul_pos hm hs).trans_le hb.2
  simpa only [lt_max_iff, lt_self_iff_false, false_or] using And.intro hx hy

/-- A thin range of null-gap values occupies a quantitatively thin long-coordinate
layer. No regularity or null-set assumption on the contact locus is used. -/
theorem volume_twoFaceRayGap_null_layer {f : Spatial → ℝ} {η : ℝ} (hη : η < 1)
    (hlip : ∀ x y, |f x - f y| ≤ η * spatialDistance x y)
    (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere) (ε : ℝ) :
    volume {v : ℝ | 0 ≤ twoFaceRayGap h f x ω 0 v ∧
      twoFaceRayGap h f x ω 0 v ≤ ε} ≤ ENNReal.ofReal (2 * ε / (1 - η)) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro v hv w hw
  have hpos : 0 < 1 - η := sub_pos.mpr hη
  have hordered (a b : ℝ) (hab : a ≤ b)
      (ha : twoFaceRayGap h f x ω 0 a ≤ ε)
      (hb : 0 ≤ twoFaceRayGap h f x ω 0 b) : b - a ≤ 2 * ε / (1 - η) := by
    apply (le_div_iff₀ hpos).mpr
    have hg := twoFaceRayGap_null_sub_le hlip h x ω hab
    nlinarith
  rw [Real.dist_eq]
  rcases le_total v w with hvw | hwv
  · rw [abs_of_nonpos (sub_nonpos.mpr hvw)]
    linarith [hordered v w hvw hv.2 hw.1]
  · rw [abs_of_nonneg (sub_nonneg.mpr hwv)]
    exact hordered w v hwv hw.2 hv.1

/-- All points lost from the positive gap as proper time increases lie in a
controlled layer around the NULL contact. Its size is O(sigma), not merely
asserted to vanish. This estimate alone is not the required little-o jet. -/
theorem volume_twoFaceRayGap_crossing {f : Spatial → ℝ} {η : ℝ}
    (hη0 : 0 ≤ η) (hη : η < 1)
    (hlip : ∀ x y, |f x - f y| ≤ η * spatialDistance x y)
    (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere)
    {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 ≤ σ) :
    volume {v : ℝ | δ ≤ v ∧ 0 < twoFaceRayGap h f x ω 0 v ∧
      twoFaceRayGap h f x ω σ v ≤ 0} ≤
      ENNReal.ofReal ((1 + η) * σ / (δ * (1 - η))) := by
  let ε := (1 + η) * σ / (2 * δ)
  have hsub : {v : ℝ | δ ≤ v ∧ 0 < twoFaceRayGap h f x ω 0 v ∧
      twoFaceRayGap h f x ω σ v ≤ 0} ⊆
      {v : ℝ | 0 ≤ twoFaceRayGap h f x ω 0 v ∧
        twoFaceRayGap h f x ω 0 v ≤ ε} := by
    intro v hv
    have hv0 : 0 < v := hδ.trans_le hv.1
    have ht := (twoFaceRayGap_transverse_bounds hlip h x ω hv0 hσ).1
    have he : (1 + η) * σ / (2 * v) ≤ ε := by
      dsimp [ε]
      gcongr
      exact hv.1
    refine ⟨hv.2.1.le, ?_⟩
    simp only [sub_zero, neg_mul, neg_div] at ht
    linarith [hv.2.2]
  have he : 2 * ε / (1 - η) = (1 + η) * σ / (δ * (1 - η)) := by
    dsimp [ε]
    field_simp [hδ.ne', (sub_pos.mpr hη).ne']
    ring
  exact (measure_mono hsub).trans (by
    simpa only [he] using volume_twoFaceRayGap_null_layer hη hlip h x ω ε)

end BoundaryDraft
