import BoundaryDraft.HausdorffGraph
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The planar isodiametric inequality

Two perpendicular Steiner symmetrizations of a compact convex set preserve
Lebesgue measure and do not increase its Euclidean diameter. The resulting
centrally symmetric set lies in the disk of radius half the original diameter.
The measure-preserving coordinate chart is used for Fubini, not to transport a
supremum-norm metric estimate. Every norm and distance below is Euclidean.
For a bounded arbitrary set, its closed convex hull has the same diameter;
for an unbounded set the extended diameter makes the right-hand side infinite.
-/

open MeasureTheory Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace BoundaryDraft
namespace PlanarIsodiametric

private def vec (x y : ℝ) : SurfacePlane := (WithLp.equiv 2 _).symm ![x, y]

@[simp] private theorem vec_zero (x y : ℝ) : vec x y 0 = x := rfl
@[simp] private theorem vec_one (x y : ℝ) : vec x y 1 = y := rfl

private theorem vec_eta (v : SurfacePlane) : vec (v 0) (v 1) = v := by
  ext i
  fin_cases i <;> rfl

private theorem continuous_vec : Continuous (fun p : ℝ × ℝ => vec p.1 p.2) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

private theorem continuous_coord (i : Fin 2) : Continuous (fun v : SurfacePlane => v i) :=
  (continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).continuous

private def reflect (v : SurfacePlane) : SurfacePlane := vec (v 0) (-v 1)
private def swap (v : SurfacePlane) : SurfacePlane := vec (v 1) (v 0)

private theorem norm_sq (v : SurfacePlane) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs]

private theorem norm_reflect (v : SurfacePlane) : ‖reflect v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [norm_sq, reflect]

private theorem norm_swap (v : SurfacePlane) : ‖swap v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [norm_sq, swap, add_comm]

private theorem continuous_reflect : Continuous reflect :=
  continuous_vec.comp ((continuous_coord 0).prodMk (continuous_coord 1).neg)

private theorem continuous_swap : Continuous swap :=
  continuous_vec.comp ((continuous_coord 1).prodMk (continuous_coord 0))

private def pairs (K : Set SurfacePlane) : Set (SurfacePlane × SurfacePlane) :=
  (K ×ˢ K) ∩ {p | p.1 0 = p.2 0}

private def center (p : SurfacePlane × SurfacePlane) : SurfacePlane :=
  (1 / 2 : ℝ) • (p.1 + reflect p.2)

/-- On a convex set, replace each vertical interval by the centered interval
of the same length: `(x,a), (x,b)` produce `(x,(a-b)/2)`. -/
private def symm (K : Set SurfacePlane) : Set SurfacePlane := center '' pairs K

private theorem continuous_center : Continuous center :=
  (continuous_fst.add (continuous_reflect.comp continuous_snd)).const_smul _

private theorem compact_symm {K : Set SurfacePlane} (hK : IsCompact K) :
    IsCompact (symm K) := by
  apply (hK.prod hK |>.inter_right ?_).image continuous_center
  exact isClosed_eq ((continuous_coord 0).comp continuous_fst)
    ((continuous_coord 0).comp continuous_snd)

private theorem mem_symm {K : Set SurfacePlane} {x y : ℝ} :
    vec x y ∈ symm K ↔ ∃ a b : ℝ, vec x a ∈ K ∧ vec x b ∈ K ∧ y = (a - b) / 2 := by
  constructor
  · rintro ⟨⟨p, q⟩, ⟨⟨hp, hq⟩, hpq⟩, he⟩
    have hx := congrArg (fun v : SurfacePlane => v 0) he
    have hy := congrArg (fun v : SurfacePlane => v 1) he
    simp [center, reflect] at hx hy
    change p 0 = q 0 at hpq
    have hpx : p 0 = x := by linarith
    have hqx : q 0 = x := by linarith
    refine ⟨p 1, q 1, ?_, ?_, ?_⟩
    · simpa [← hpx, vec_eta] using hp
    · simpa [← hqx, vec_eta] using hq
    · linarith
  · rintro ⟨a, b, ha, hb, hy⟩
    refine ⟨(vec x a, vec x b), ⟨⟨ha, hb⟩, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [center, reflect, hy] <;> ring

-- A difference of symmetrized points is the average of an original difference
-- and a reflected original difference. The Euclidean triangle inequality applies.
private theorem symm_dist_le {K : Set SurfacePlane} {d : ℝ}
    (hK : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ d) :
    ∀ p ∈ symm K, ∀ q ∈ symm K, dist p q ≤ d := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have hlin : center p - center q =
      (1 / 2 : ℝ) • ((p.1 - q.1) + reflect (p.2 - q.2)) := by
    ext i
    fin_cases i <;> simp [center, reflect] <;> ring
  rw [dist_eq_norm, hlin, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) * ‖p.1 - q.1 + reflect (p.2 - q.2)‖ ≤
        (1 / 2 : ℝ) * (‖p.1 - q.1‖ + ‖reflect (p.2 - q.2)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ d := by
      rw [norm_reflect]
      have h1 := hK p.1 hp.1.1 q.1 hq.1.1
      have h2 := hK p.2 hp.1.2 q.2 hq.1.2
      rw [dist_eq_norm] at h1 h2
      linarith

private theorem convex_symm {K : Set SurfacePlane} (hK : Convex ℝ K) :
    Convex ℝ (symm K) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨(a • p.1 + b • q.1, a • p.2 + b • q.2),
    ⟨⟨hK hp.1.1 hq.1.1 ha hb hab, hK hp.1.2 hq.1.2 ha hb hab⟩, ?_⟩, ?_⟩
  · change a * p.1 0 + b * q.1 0 = a * p.2 0 + b * q.2 0
    rw [hp.2, hq.2]
  · ext i
    fin_cases i <;> simp [center, reflect] <;> ring

private def fiber (K : Set SurfacePlane) (x : ℝ) : Set ℝ := {y | vec x y ∈ K}

private theorem compact_fiber {K : Set SurfacePlane} (hK : IsCompact K) (x : ℝ) :
    IsCompact (fiber K x) := by
  have he : fiber K x = (fun p : SurfacePlane => p 1) '' (K ∩ {p | p 0 = x}) := by
    ext y
    constructor
    · intro hy
      exact ⟨vec x y, ⟨hy, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hx⟩, rfl⟩
      change vec x (p 1) ∈ K
      change p 0 = x at hx
      simpa [← hx, vec_eta] using hp
  rw [he]
  exact (hK.inter_right (isClosed_eq (continuous_coord 0) continuous_const)).image
    (continuous_coord 1)

private theorem convex_fiber {K : Set SurfacePlane} (hK : Convex ℝ K) (x : ℝ) :
    Convex ℝ (fiber K x) := by
  intro y hy z hz a b ha hb hab
  have he : vec x (a • y + b • z) = a • vec x y + b • vec x z := by
    ext i
    fin_cases i <;> simp [← add_mul, hab]
  change vec x (a • y + b • z) ∈ K
  rw [he]
  exact hK hy hz ha hb hab

private theorem volume_fiber_symm {K : Set SurfacePlane} (hk : IsCompact K)
    (hc : Convex ℝ K) (x : ℝ) : volume (fiber (symm K) x) = volume (fiber K x) := by
  by_cases hn : (fiber K x).Nonempty
  · have hf := eq_Icc_of_connected_compact ⟨hn, (convex_fiber hc x).isPreconnected⟩
      (compact_fiber hk x)
    let l := sInf (fiber K x)
    let u := sSup (fiber K x)
    have he : fiber (symm K) x = Icc ((l - u) / 2) ((u - l) / 2) := by
      ext y
      change vec x y ∈ symm K ↔ _
      rw [mem_symm]
      constructor
      · rintro ⟨a, b, ha, hb, rfl⟩
        have ha' : a ∈ Icc l u := by rw [← hf]; exact ha
        have hb' : b ∈ Icc l u := by rw [← hf]; exact hb
        constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
      · intro hy
        refine ⟨(l + u) / 2 + y, (l + u) / 2 - y, ?_, ?_, by ring⟩
        · change (l + u) / 2 + y ∈ fiber K x
          rw [hf]
          change l ≤ _ ∧ _ ≤ u
          constructor <;> linarith [hy.1, hy.2]
        · change (l + u) / 2 - y ∈ fiber K x
          rw [hf]
          change l ≤ _ ∧ _ ≤ u
          constructor <;> linarith [hy.1, hy.2]
    rw [he, hf, Real.volume_Icc, Real.volume_Icc]
    congr 1
    change (u - l) / 2 - (l - u) / 2 = u - l
    ring
  · have hf : fiber K x = ∅ := not_nonempty_iff_eq_empty.mp hn
    have he : fiber (symm K) x = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro y hy
      obtain ⟨a, _, ha, _, _⟩ := mem_symm.mp hy
      exact hn ⟨a, ha⟩
    rw [he, hf]

-- This is a measure equivalence only, not a claimed isometry.
private def chart : SurfacePlane ≃ᵐ ℝ × ℝ :=
  (EuclideanSpace.measurableEquiv (Fin 2)).trans MeasurableEquiv.finTwoArrow

private theorem chart_preserving : MeasurePreserving chart :=
  (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2))

private theorem volume_eq_lintegral_fiber {K : Set SurfacePlane} (hK : MeasurableSet K) :
    volume K = ∫⁻ x : ℝ, volume (fiber K x) := by
  rw [← (MeasurePreserving.symm chart chart_preserving).measure_preimage_equiv K]
  exact Measure.prod_apply (chart.symm.measurable hK)

private theorem volume_symm {K : Set SurfacePlane} (hk : IsCompact K) (hc : Convex ℝ K) :
    volume (symm K) = volume K := by
  rw [volume_eq_lintegral_fiber (compact_symm hk).measurableSet,
    volume_eq_lintegral_fiber hk.measurableSet]
  exact lintegral_congr (volume_fiber_symm hk hc)

private def swapEquiv : SurfacePlane ≃ᵐ SurfacePlane :=
  (chart.trans MeasurableEquiv.prodComm).trans chart.symm

private theorem swap_preserving : MeasurePreserving swapEquiv :=
  (MeasurePreserving.symm chart chart_preserving).comp
    (Measure.measurePreserving_swap.comp chart_preserving)

private theorem swap_involutive (p : SurfacePlane) : swap (swap p) = p := by
  simpa [swap] using vec_eta p

private theorem volume_swap (K : Set SurfacePlane) : volume (swap '' K) = volume K := by
  have he : swap '' K = swapEquiv ⁻¹' K := by
    ext p
    change (∃ q ∈ K, swap q = p) ↔ swap p ∈ K
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [swap_involutive] using hq
    · intro hp
      exact ⟨swap p, hp, swap_involutive p⟩
  rw [he]
  exact swap_preserving.measure_preimage_equiv K

private theorem convex_swap {K : Set SurfacePlane} (hK : Convex ℝ K) :
    Convex ℝ (swap '' K) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, hK hp hq ha hb hab, ?_⟩
  ext i
  fin_cases i <;> simp [swap]

private theorem swap_dist_le {K : Set SurfacePlane} {d : ℝ}
    (hK : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ d) :
    ∀ p ∈ swap '' K, ∀ q ∈ swap '' K, dist p q ≤ d := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have he : swap p - swap q = swap (p - q) := by
    ext i
    fin_cases i <;> rfl
  simpa only [dist_eq_norm, he, norm_swap] using hK p hp q hq

private theorem reflect_mem_symm {K : Set SurfacePlane} {p : SurfacePlane}
    (hp : p ∈ symm K) : reflect p ∈ symm K := by
  rw [← vec_eta p, mem_symm] at hp
  obtain ⟨a, b, ha, hb, he⟩ := hp
  apply mem_symm.mpr
  exact ⟨b, a, hb, ha, by linarith⟩

private theorem neg_mem_symm_swap_symm {K : Set SurfacePlane} {p : SurfacePlane}
    (hp : p ∈ symm (swap '' symm K)) : -p ∈ symm (swap '' symm K) := by
  rw [← vec_eta p, mem_symm] at hp
  obtain ⟨a, b, ⟨q, hq, hqa⟩, ⟨r, hr, hrb⟩, he⟩ := hp
  rw [← vec_eta (-p), mem_symm]
  refine ⟨b, a, ?_, ?_, by simpa using (show -p 1 = (b - a) / 2 by linarith)⟩
  · refine ⟨reflect r, reflect_mem_symm hr, ?_⟩
    have h0 := congrArg (fun v : SurfacePlane => v 0) hrb
    have h1 := congrArg (fun v : SurfacePlane => v 1) hrb
    ext i
    fin_cases i <;> simp_all [swap, reflect]
  · refine ⟨reflect q, reflect_mem_symm hq, ?_⟩
    have h0 := congrArg (fun v : SurfacePlane => v 0) hqa
    have h1 := congrArg (fun v : SurfacePlane => v 1) hqa
    ext i
    fin_cases i <;> simp_all [swap, reflect]

/-- The compact convex case, with an explicit Euclidean pairwise distance bound. -/
theorem volume_le_of_compact_convex {K : Set SurfacePlane} (hk : IsCompact K)
    (hc : Convex ℝ K) {d : ℝ} (hd : 0 ≤ d)
    (hdiam : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ d) :
    volume K ≤ ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal d ^ 2 := by
  -- Swapping coordinates makes the second symmetrization perpendicular to
  -- the first; their reflection symmetries imply central symmetry.
  let T := symm (swap '' symm K)
  have hTdiam := symm_dist_le (swap_dist_le (symm_dist_le hdiam))
  have hTball : T ⊆ closedBall (0 : SurfacePlane) (d / 2) := by
    intro p hp
    have h := hTdiam p hp (-p) (neg_mem_symm_swap_symm hp)
    have he : p - -p = (2 : ℝ) • p := by simp [two_smul]
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs] at h
    norm_num at h
    simpa only [mem_closedBall, dist_zero_right] using (show ‖p‖ ≤ d / 2 by linarith)
  calc
    volume K = volume T := by
      dsimp [T]
      rw [volume_symm ((compact_symm hk).image continuous_swap) (convex_swap (convex_symm hc)),
        volume_swap, volume_symm hk hc]
    _ ≤ volume (closedBall (0 : SurfacePlane) (d / 2)) := measure_mono hTball
    _ = ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal d ^ 2 := by
      rw [EuclideanSpace.volume_closedBall_fin_two]
      rw [← ENNReal.ofReal_pow hd, ← ENNReal.ofReal_pow (by positivity : 0 ≤ d / 2),
        ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end PlanarIsodiametric

/-- The sharp planar isodiametric inequality, for every subset of the Euclidean
plane. No measurability or finiteness hypothesis is needed. -/
theorem volume_le_pi_div_four_mul_ediam_sq (s : Set SurfacePlane) :
    volume s ≤ ENNReal.ofReal (Real.pi / 4) * EMetric.diam s ^ (2 : ℝ) := by
  by_cases hb : Bornology.IsBounded s
  · let K := closure (convexHull ℝ s)
    have hk : IsCompact K := isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, (isBounded_convexHull.mpr hb).closure⟩
    have hc : Convex ℝ K := (convex_convexHull ℝ s).closure
    have hdiam : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ diam s := by
      intro p hp q hq
      simpa only [K, diam_closure, convexHull_diam] using
        dist_le_diam_of_mem hk.isBounded hp hq
    have hle := PlanarIsodiametric.volume_le_of_compact_convex hk hc diam_nonneg hdiam
    have hsubset : s ⊆ K := (subset_convexHull ℝ s).trans subset_closure
    refine (measure_mono hsubset).trans (hle.trans_eq ?_)
    rw [Metric.diam, ENNReal.ofReal_toReal hb.ediam_ne_top, ENNReal.rpow_two]
  · rw [ediam_of_unbounded hb, ENNReal.top_rpow_of_pos (by norm_num),
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity : 0 < Real.pi / 4)))]
    exact le_top

end BoundaryDraft
