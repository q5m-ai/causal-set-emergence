import BoundaryDraft.LorentzReflection
import BoundaryDraft.IntervalMoments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Rest-frame transport and arbitrary causal intervals

The rank-one reflection is now specialized to a future timelike displacement.
A Cauchy--Schwarz argument proves that it preserves the future cone (not only
the quadratic form).  Translation and the determinant-one-in-absolute-value
linear change of variables then transport the standard interval identity to
arbitrary timelike endpoints.
-/

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

noncomputable section
namespace BoundaryDraft

private def spatialEuclidean (x : Spacetime) : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.equiv 2 _).symm (spatialPart x)

private theorem norm_spatialEuclidean (x : Spacetime) :
    ‖spatialEuclidean x‖ = spatialDistance (spatialPart 0) (spatialPart x) := by
  unfold spatialEuclidean spatialDistance spatialPart
  congr 2
  ext i
  simp

private theorem inner_spatialEuclidean (x y : Spacetime) :
    ⟪spatialEuclidean x, spatialEuclidean y⟫_ℝ =
      ∑ i : Fin 3, x i.succ * y i.succ := by
  simp [spatialEuclidean, spatialPart]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem spatialNorm_sq (x : Spacetime) :
    ‖spatialEuclidean x‖ ^ 2 = ∑ i : Fin 3, x i.succ ^ 2 := by
  rw [norm_spatialEuclidean, spatialDistance_sq]
  simp [spatialPart]

private theorem spatialNorm_le_abs_time {x : Spacetime}
    (hx : 0 ≤ minkowskiInner x x) :
    ‖spatialEuclidean x‖ ≤ |x 0| := by
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, spatialNorm_sq]
  have hx' : 0 ≤ x 0 ^ 2 - ∑ i : Fin 3, x i.succ ^ 2 := by
    simpa only [minkowskiInner, pow_two] using hx
  linarith

private theorem spatialNorm_lt_time {x : Spacetime}
    (ht : 0 < x 0) (hx : 0 < minkowskiInner x x) :
    ‖spatialEuclidean x‖ < x 0 := by
  apply (sq_lt_sq₀ (norm_nonneg _) ht.le).mp
  rw [spatialNorm_sq]
  have hx' : 0 < x 0 ^ 2 - ∑ i : Fin 3, x i.succ ^ 2 := by
    simpa only [minkowskiInner, pow_two] using hx
  linarith

/-- A causal vector whose Minkowski product with a future timelike vector is
nonnegative is itself future-directed.  This is the time-orientation step
which cannot be recovered from preservation of the quadratic form alone. -/
theorem time_nonneg_of_minkowskiInner_nonneg {v d : Spacetime}
    (hv : 0 ≤ minkowskiInner v v) (hd0 : 0 < d 0)
    (hd : 0 < minkowskiInner d d) (hvd : 0 ≤ minkowskiInner v d) :
    0 ≤ v 0 := by
  by_contra h
  have hv0 : v 0 < 0 := lt_of_not_ge h
  have hvnorm : ‖spatialEuclidean v‖ ≤ -v 0 := by
    simpa [abs_of_neg hv0] using spatialNorm_le_abs_time hv
  have hdnorm : ‖spatialEuclidean d‖ < d 0 := spatialNorm_lt_time hd0 hd
  have hcs : -(∑ i : Fin 3, v i.succ * d i.succ) ≤
      ‖spatialEuclidean v‖ * ‖spatialEuclidean d‖ := by
    calc
      -(∑ i : Fin 3, v i.succ * d i.succ) ≤
          |∑ i : Fin 3, v i.succ * d i.succ| := neg_le_abs _
      _ = |⟪spatialEuclidean v, spatialEuclidean d⟫_ℝ| := by
        rw [inner_spatialEuclidean]
      _ ≤ _ := abs_real_inner_le_norm _ _
  have hmul : ‖spatialEuclidean v‖ * ‖spatialEuclidean d‖ <
      (-v 0) * d 0 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hvnorm (norm_nonneg _))
      (mul_lt_mul_of_pos_left hdnorm (neg_pos.mpr hv0))
  unfold minkowskiInner at hvd
  linarith

/-- Data of a checked, volume-preserving rest-frame map. -/
structure TimelikeFrame (d : Spacetime) (H : ℝ) where
  map : Spacetime →ₗ[ℝ] Spacetime
  map_axis : map (timeAxis H) = d
  preserves_inner : ∀ y z, minkowskiInner (map y) (map z) = minkowskiInner y z
  measurePreserving : MeasurePreserving map
  involutive : Function.Involutive map

private theorem timeAxis_inner_self (H : ℝ) :
    minkowskiInner (timeAxis H) (timeAxis H) = H ^ 2 := by
  simp [minkowskiInner, pow_two]

private theorem timeAxis_inner (H : ℝ) (x : Spacetime) :
    minkowskiInner (timeAxis H) x = H * x 0 := by
  simp [minkowskiInner]

/-- Every future timelike vector of proper duration `H` admits an explicit
rest frame.  The degenerate no-boost case uses the identity; all other cases
use the audited Lorentz reflection. -/
theorem exists_timelikeFrame (d : Spacetime) (H : ℝ)
    (hH : 0 < H) (hd0 : 0 < d 0)
    (hdH : minkowskiInner d d = H ^ 2) : Nonempty (TimelikeFrame d H) := by
  by_cases he : d = timeAxis H
  · subst d
    exact ⟨{
      map := LinearMap.id
      map_axis := rfl
      preserves_inner := by intro y z; rfl
      measurePreserving := MeasurePreserving.id volume
      involutive := fun _ => rfl }⟩
  · let e := timeAxis H
    let n := d - e
    have hsum : ∑ i : Fin 3, d i.succ ^ 2 = d 0 ^ 2 - H ^ 2 := by
      have hdH' : d 0 ^ 2 - ∑ i : Fin 3, d i.succ ^ 2 = H ^ 2 := by
        simpa only [minkowskiInner, pow_two] using hdH
      linarith
    have hd_ge : H ≤ d 0 := by
      apply (sq_le_sq₀ hH.le hd0.le).mp
      rw [← hdH]
      unfold minkowskiInner
      have hs : 0 ≤ ∑ i : Fin 3, d i.succ * d i.succ :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg _
      linarith
    have hd_ne : d 0 ≠ H := by
      intro hEq
      have hzero : ∑ i : Fin 3, d i.succ ^ 2 = 0 := by rw [hsum, hEq]; ring
      apply he
      ext i
      refine Fin.cases (by simpa [e, timeAxis] using hEq) (fun j => ?_) i
      have hj : d j.succ ^ 2 ≤ ∑ k : Fin 3, d k.succ ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (d k.succ)) (Finset.mem_univ j)
      have : d j.succ ^ 2 = 0 := le_antisymm (by simpa [hzero] using hj) (sq_nonneg _)
      simpa [e, timeAxis] using (sq_eq_zero_iff.mp this)
    have hd_gt : H < d 0 := lt_of_le_of_ne hd_ge (Ne.symm hd_ne)
    have hnn : minkowskiInner n n = 2 * H * (H - d 0) := by
      dsimp [n, e]
      rw [minkowskiInner_sub_left, minkowskiInner_sub_right,
        minkowskiInner_sub_right, hdH, timeAxis_inner,
        minkowskiInner_symm d (timeAxis H), timeAxis_inner,
        timeAxis_inner_self]
      ring
    have hnn0 : minkowskiInner n n ≠ 0 := by
      rw [hnn]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hH.ne')
        (sub_ne_zero.mpr (Ne.symm hd_ne))
    have hmap : lorentzReflection n (timeAxis H) = d := by
      rw [lorentzReflection_apply]
      have hen : minkowskiInner (timeAxis H) n = H * (d 0 - H) := by
        dsimp [n, e]
        rw [minkowskiInner_sub_right, timeAxis_inner, timeAxis_inner_self]
        ring
      rw [hen, hnn]
      have hden : 2 * H * (H - d 0) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) hH.ne')
          (sub_ne_zero.mpr (Ne.symm hd_ne))
      have hc : 2 * (H * (d 0 - H)) / (2 * H * (H - d 0)) = -1 := by
        apply (div_eq_iff hden).2
        ring
      rw [hc, neg_one_smul, sub_neg_eq_add]
      dsimp [n, e]
      abel
    exact ⟨{
      map := lorentzReflection n
      map_axis := hmap
      preserves_inner := fun y z => lorentzReflection_minkowskiInner n y z hnn0
      measurePreserving := lorentzReflection_measurePreserving n hnn0
      involutive := fun y => lorentzReflection_involutive n y hnn0 }⟩

private theorem timelikeFrame_injective {d : Spacetime} {H : ℝ}
    (L : TimelikeFrame d H) : Function.Injective L.map :=
  L.involutive.injective

private theorem timelikeFrame_measurableEmbedding {d : Spacetime} {H : ℝ}
    (L : TimelikeFrame d H) : MeasurableEmbedding L.map :=
  L.map.continuous_of_finiteDimensional.measurableEmbedding L.involutive.injective

private theorem timelikeFrame_maps_futureCone {d : Spacetime} {H : ℝ}
    (hH : 0 < H) (hd0 : 0 < d 0) (hd : 0 < minkowskiInner d d)
    (L : TimelikeFrame d H) (y : Spacetime) :
    y ∈ causalFuture 0 ↔ L.map y ∈ causalFuture 0 := by
  have forward : ∀ z : Spacetime, z ∈ causalFuture 0 → L.map z ∈ causalFuture 0 := by
    intro z hz
    have hzq : 0 ≤ minkowskiInner z z := by
      rw [minkowskiInner_self]
      unfold intervalSq
      simpa [causalFuture] using hz.2
    have hLq : 0 ≤ minkowskiInner (L.map z) (L.map z) := by
      rw [L.preserves_inner]
      exact hzq
    have hprod : 0 ≤ minkowskiInner (L.map z) d := by
      calc
        0 ≤ H * z 0 := mul_nonneg hH.le hz.1
        _ = minkowskiInner z (timeAxis H) := by
          rw [minkowskiInner_symm, timeAxis_inner]
        _ = minkowskiInner (L.map z) (L.map (timeAxis H)) :=
          (L.preserves_inner z (timeAxis H)).symm
        _ = minkowskiInner (L.map z) d := by rw [L.map_axis]
    have ht := time_nonneg_of_minkowskiInner_nonneg hLq hd0 hd hprod
    constructor
    · simpa [causalFuture] using ht
    · have hLq' : ∑ i : Fin 3, L.map z i.succ ^ 2 ≤ L.map z 0 ^ 2 := by
        have hq := hLq
        unfold minkowskiInner at hq
        simp_rw [← pow_two] at hq
        linarith
      simpa [causalFuture, spatialSeparationSq] using hLq'
  constructor
  · exact forward y
  · intro hy
    have := forward (L.map y) hy
    simpa only [L.involutive y] using this

private theorem causalFuture_iff_sub (a b : Spacetime) :
    a ∈ causalFuture b ↔ a - b ∈ causalFuture 0 := by
  unfold causalFuture spatialSeparationSq
  constructor
  · intro h
    constructor
    · simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, sub_nonneg] using h.1
    · simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using h.2
  · intro h
    constructor
    · simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, sub_nonneg] using h.1
    · simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using h.2

private theorem measurableSet_causalPast (q : Spacetime) :
    MeasurableSet (causalPast q) := by
  unfold causalPast causalFuture
  apply MeasurableSet.inter
  · exact (isClosed_le (continuous_apply 0) continuous_const).measurableSet
  · exact (isClosed_le
      (continuous_spatialSeparationSq.comp (continuous_id.prodMk continuous_const))
      ((continuous_const.sub (continuous_apply 0)).pow 2)).measurableSet

private theorem measurableSet_causalInterval (x q : Spacetime) :
    MeasurableSet (causalInterval x q) :=
  (isClosed_causalFuture x).measurableSet.inter (measurableSet_causalPast q)

private theorem causalInterval_preimage_frame (p d : Spacetime) (H : ℝ)
    (hH : 0 < H) (hd0 : 0 < d 0) (hd : 0 < minkowskiInner d d)
    (L : TimelikeFrame d H) :
    (fun y => p + L.map y) ⁻¹' causalInterval p (p + d) =
      causalInterval 0 (timeAxis H) := by
  have hcone := timelikeFrame_maps_futureCone hH hd0 hd L
  ext y
  simp only [mem_preimage, causalInterval, mem_inter_iff, causalPast]
  have hfirst : p + L.map y ∈ causalFuture p ↔ y ∈ causalFuture 0 := by
    rw [causalFuture_iff_sub]
    have hsub : p + L.map y - p = L.map y := by abel
    rw [hsub, ← hcone]
  have hpast : p + d ∈ causalFuture (p + L.map y) ↔
      timeAxis H ∈ causalFuture y := by
    rw [causalFuture_iff_sub]
    have hsub : p + d - (p + L.map y) = L.map (timeAxis H - y) := by
      rw [map_sub, L.map_axis]
      abel
    rw [hsub, ← hcone, ← causalFuture_iff_sub]
  change (p + L.map y ∈ causalFuture p ∧
      p + d ∈ causalFuture (p + L.map y)) ↔
    (y ∈ causalFuture 0 ∧ timeAxis H ∈ causalFuture y)
  rw [hfirst, hpast]

/-- Exact interval identity for arbitrary timelike endpoints.  The duration is
`sqrt (intervalSq x q)` and the proof includes the affine Jacobian. -/
theorem causalInterval_kernel_identity (ρ : ℝ) (x q : Spacetime)
    (hρ : 0 < ρ) (hxq : q ∈ chronologicalFuture x) :
    ρ * (∫ y in causalInterval x q,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
      1 - Real.exp (-(Real.pi / 24) * ρ * intervalSq x q ^ 2) := by
  let d := q - x
  let H := Real.sqrt (intervalSq x q)
  have hsq : 0 < intervalSq x q := by
    unfold intervalSq
    exact sub_pos.mpr hxq.2
  have hH : 0 < H := Real.sqrt_pos.2 hsq
  have hd0 : 0 < d 0 := by dsimp [d]; exact sub_pos.mpr hxq.1
  have hdH : minkowskiInner d d = H ^ 2 := by
    rw [← intervalSq_eq_minkowski_sub, Real.sq_sqrt hsq.le]
  obtain ⟨L⟩ := exists_timelikeFrame d H hH hd0 hdH
  have hm : MeasurableSet (causalInterval x q) :=
    measurableSet_causalInterval x q
  let F := fun y : Spacetime => (causalInterval x q).indicator
    (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) y
  have htranslate : (∫ y, F y) = ∫ y, F (x + y) := by
    exact (integral_add_left_eq_self F x).symm
  rw [← integral_indicator hm]
  change ρ * (∫ y, F y) = _
  rw [htranslate, ← L.measurePreserving.integral_comp
    (timelikeFrame_measurableEmbedding L) (fun y => F (x + y))]
  have hpre : (fun y => x + L.map y) ⁻¹' causalInterval x q =
      causalInterval 0 (timeAxis H) := by
    have h := causalInterval_preimage_frame x d H hH hd0
      (by rw [hdH]; positivity) L
    simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have he (y : Spacetime) : F (x + L.map y) =
      (causalInterval 0 (timeAxis H)).indicator
        (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq 0 y ^ 2)) y := by
    have hmem : x + L.map y ∈ causalInterval x q ↔
        y ∈ causalInterval 0 (timeAxis H) := by
      change y ∈ (fun y => x + L.map y) ⁻¹' causalInterval x q ↔ _
      rw [hpre]
    dsimp only [F]
    by_cases hy : y ∈ causalInterval 0 (timeAxis H)
    · have hxy := hmem.mpr hy
      rw [Set.indicator_of_mem hxy, Set.indicator_of_mem hy]
      congr 2
      rw [intervalSq_eq_minkowski_sub, intervalSq_eq_minkowski_sub]
      have hsub : x + L.map y - x = L.map y := by abel
      rw [hsub, L.preserves_inner]
      simp
    · have hxy : x + L.map y ∉ causalInterval x q := by
        exact fun h => hy (hmem.mp h)
      rw [Set.indicator_of_not_mem hxy, Set.indicator_of_not_mem hy]
  simp_rw [he]
  have hmstd : MeasurableSet (causalInterval 0 (timeAxis H)) :=
    measurableSet_causalInterval 0 (timeAxis H)
  rw [integral_indicator hmstd]
  rw [standard_causalInterval_kernel_identity ρ H hρ hH]
  have hHs : H ^ 2 = intervalSq x q := Real.sq_sqrt hsq.le
  rw [show H ^ 4 = (H ^ 2) ^ 2 by ring, hHs]

/-- Four-dimensional Alexandrov volume for arbitrary future-timelike
endpoints, obtained from the zeroth moment and the checked rest-frame map. -/
theorem volume_causalInterval_timelike (x q : Spacetime)
    (hxq : q ∈ chronologicalFuture x) :
    (volume (causalInterval x q)).toReal = (Real.pi / 24) * intervalSq x q ^ 2 := by
  let d := q - x
  let H := Real.sqrt (intervalSq x q)
  have hsq : 0 < intervalSq x q := sub_pos.mpr hxq.2
  have hH : 0 < H := Real.sqrt_pos.2 hsq
  have hd0 : 0 < d 0 := sub_pos.mpr hxq.1
  have hdH : minkowskiInner d d = H ^ 2 := by
    rw [← intervalSq_eq_minkowski_sub, Real.sq_sqrt hsq.le]
  obtain ⟨L⟩ := exists_timelikeFrame d H hH hd0 hdH
  have hpre : (fun y => x + L.map y) ⁻¹' causalInterval x q =
      causalInterval 0 (timeAxis H) := by
    simpa [d, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      causalInterval_preimage_frame x d H hH hd0 (by rw [hdH]; positivity) L
  have hv := ((measurePreserving_add_left volume x).comp L.measurePreserving).measure_preimage
    (measurableSet_causalInterval x q).nullMeasurableSet
  change volume ((fun y => x + L.map y) ⁻¹' causalInterval x q) = _ at hv
  rw [hpre] at hv
  rw [← hv]
  have hm := standard_causalInterval_moment H hH 0
  simp only [mul_zero, pow_zero, integral_const, measureReal_def, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one, Nat.cast_zero, zero_add, zero_mul] at hm
  rw [hm]
  have hHs : H ^ 2 = intervalSq x q := Real.sq_sqrt hsq.le
  rw [show H ^ 4 = (H ^ 2) ^ 2 by ring, hHs]
  ring

/-- Extended-real form of Alexandrov volume. Finiteness follows from the
strictly positive real volume just computed, not from totalising an infinite
measure to zero. -/
theorem volume_causalInterval_timelike_eq_ofReal (x q : Spacetime)
    (hxq : q ∈ chronologicalFuture x) :
    volume (causalInterval x q) = ENNReal.ofReal ((Real.pi / 24) * intervalSq x q ^ 2) := by
  have hpos : 0 < (volume (causalInterval x q)).toReal := by
    rw [volume_causalInterval_timelike x q hxq]
    have hs : 0 < intervalSq x q := sub_pos.mpr hxq.2
    positivity
  have hn : volume (causalInterval x q) ≠ ⊤ := by
    intro h
    simp [h] at hpos
  rw [← ENNReal.ofReal_toReal hn, volume_causalInterval_timelike x q hxq]

end BoundaryDraft
