import BoundaryDraft.Pilot3Disconnected

/-!
# Admissible annular curved pilot with both boundary components

The raw height is a smooth quartic in the spatial coordinates. Only its
positive part must be globally Lipschitz. An explicit clipped-radial estimate
proves the original combined budget, rather than assuming bounded raw slope.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace BoundaryDraft

/-- A genuinely regular raw zero has positive-height points nearby. This
lemma does not assume in advance that the zero belongs to the cap closure. -/
theorem pilot3_mem_closedPositive_of_regular_zero {h : Pilot3Space → ℝ} {x : Pilot3Space}
    (hs : ContDiffAt ℝ ∞ h x) (hz : h x = 0) (hr : fderiv ℝ h x ≠ 0) : x ∈ pilot3ClosedPositive h := by
  have hn : (fderiv ℝ h x).toLinearMap ≠ 0 := by
    intro he
    apply hr
    ext y
    exact LinearMap.congr_fun he y
  have hm := (hs.hasStrictFDerivAt (by simp)).map_nhds_eq_of_surj
    (Module.Dual.range_eq_top_of_ne_zero hn)
  rw [hz] at hm
  have hc : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; norm_num
  have hf := mem_closure_iff_frequently.mp hc
  rw [← hm, frequently_map] at hf
  exact mem_closure_iff_frequently.mpr hf

private def annularPolynomial (r : ℝ) : ℝ := ((r ^ 2 - 1) * (4 - r ^ 2)) / 64
private def annularClamp (r : ℝ) : ℝ := max 1 (min r 2)

private theorem annularClamp_mem (r : ℝ) : annularClamp r ∈ Icc (1 : ℝ) 2 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

private theorem annularClamp_lipschitz (r s : ℝ) : |annularClamp r - annularClamp s| ≤ |r - s| := by
  unfold annularClamp
  rw [max_comm 1 (min r 2), max_comm 1 (min s 2)]
  apply (abs_max_sub_max_le_abs _ _ _).trans
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (r - s))] using abs_min_sub_min_le_max r 2 s 2

private theorem annularPolynomial_nonneg {r : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) : 0 ≤ annularPolynomial r :=
  div_nonneg (mul_nonneg (by nlinarith [hr.1, hr.2]) (by nlinarith [hr.1, hr.2])) (by norm_num)

private theorem annularPolynomial_clipped {r : ℝ} (hr : 0 ≤ r) :
    max 0 (annularPolynomial r) = annularPolynomial (annularClamp r) := by
  by_cases h1 : r ≤ 1
  · have he : annularClamp r = 1 := by
      rw [annularClamp, min_eq_left (h1.trans (by norm_num)), max_eq_left h1]
    have hn : annularPolynomial r ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by nlinarith)) (by norm_num)
    rw [he, max_eq_left hn]
    norm_num [annularPolynomial]
  · by_cases h2 : 2 ≤ r
    · have he : annularClamp r = 2 := by simp [annularClamp, min_eq_right h2]
      have hn : annularPolynomial r ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)) (by norm_num)
      rw [he, max_eq_left hn]
      norm_num [annularPolynomial]
    · have hm : r ∈ Icc (1 : ℝ) 2 := ⟨(lt_of_not_ge h1).le, (lt_of_not_ge h2).le⟩
      rw [annularClamp, min_eq_left hm.2, max_eq_right hm.1, max_eq_right (annularPolynomial_nonneg hm)]

private theorem annularPolynomial_lipschitz {r s : ℝ} (hr : r ∈ Icc (1 : ℝ) 2) (hs : s ∈ Icc (1 : ℝ) 2) :
    |annularPolynomial r - annularPolynomial s| ≤ (3 / 16 : ℝ) * |r - s| := by
  have h1 : |r + s| ≤ 4 := abs_le.mpr ⟨by linarith [hr.1, hs.1], by linarith [hr.2, hs.2]⟩
  have h2 : |5 - r ^ 2 - s ^ 2| ≤ 3 := abs_le.mpr
    ⟨by nlinarith [hr.1, hr.2, hs.1, hs.2], by nlinarith [hr.1, hr.2, hs.1, hs.2]⟩
  have he : (r ^ 2 - 1) * (4 - r ^ 2) - (s ^ 2 - 1) * (4 - s ^ 2) =
      (r - s) * (r + s) * (5 - r ^ 2 - s ^ 2) := by ring
  rw [annularPolynomial, annularPolynomial, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 64), he, abs_mul, abs_mul]
  calc
    _ ≤ (|r - s| * 4 * 3) / 64 := by gcongr
    _ = _ := by ring

def pilot3AnnularHeight (x : Pilot3Space) : ℝ := ((‖x‖ ^ 2 - 1) * (4 - ‖x‖ ^ 2)) / 64

theorem pilot3Annular_smooth : ContDiff ℝ ∞ pilot3AnnularHeight :=
  ((contDiff_norm_sq ℝ).sub contDiff_const |>.mul (contDiff_const.sub (contDiff_norm_sq ℝ))).div_const 64

theorem pilot3Annular_lipschitz (x y : Pilot3Space) :
    |max 0 (pilot3AnnularHeight x) - max 0 (pilot3AnnularHeight y)| ≤ (3 / 16 : ℝ) * ‖y - x‖ := by
  change |max 0 (annularPolynomial ‖x‖) - max 0 (annularPolynomial ‖y‖)| ≤ _
  rw [annularPolynomial_clipped (norm_nonneg x), annularPolynomial_clipped (norm_nonneg y)]
  have hb := annularPolynomial_lipschitz (annularClamp_mem ‖x‖) (annularClamp_mem ‖y‖)
  have hn : |‖x‖ - ‖y‖| ≤ ‖y - x‖ := by simpa only [norm_sub_rev] using abs_norm_sub_norm_le x y
  exact hb.trans (mul_le_mul_of_nonneg_left ((annularClamp_lipschitz _ _).trans hn) (by norm_num))

theorem pilot3Annular_positive (x : Pilot3Space) : 0 < pilot3AnnularHeight x ↔ 1 < ‖x‖ ∧ ‖x‖ < 2 := by
  change 0 < ((‖x‖ ^ 2 - 1) * (4 - ‖x‖ ^ 2)) / 64 ↔ _
  rw [div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 64), mul_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · constructor <;> nlinarith [norm_nonneg x]
    · exfalso
      linarith
  · rintro ⟨h1, h2⟩
    left
    constructor <;> nlinarith [norm_nonneg x]

theorem pilot3Annular_zero_sq (x : Pilot3Space) : pilot3AnnularHeight x = 0 ↔ ‖x‖ ^ 2 = 1 ∨ ‖x‖ ^ 2 = 4 := by
  simp only [pilot3AnnularHeight, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
  norm_num
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm

theorem pilot3Annular_zero (x : Pilot3Space) : pilot3AnnularHeight x = 0 ↔ ‖x‖ = 1 ∨ ‖x‖ = 2 := by
  rw [pilot3Annular_zero_sq]
  constructor
  · rintro (h | h)
    · left; nlinarith [norm_nonneg x]
    · right; nlinarith [norm_nonneg x]
  · rintro (h | h) <;> norm_num [h]

theorem pilot3Annular_fderiv (x v : Pilot3Space) :
    fderiv ℝ pilot3AnnularHeight x v = ((5 - 2 * ‖x‖ ^ 2) / 32) * inner (𝕜 := ℝ) x v := by
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := ((hq.sub_const 1).mul (hq.const_sub 4)).const_smul (1 / 64 : ℝ)
  have he : pilot3AnnularHeight = fun y => (1 / 64 : ℝ) • ((‖y‖ ^ 2 - 1) * (4 - ‖y‖ ^ 2)) := by
    ext y
    simp only [pilot3AnnularHeight, smul_eq_mul]
    ring
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply, innerSL_apply, smul_eq_mul]
  ring

theorem pilot3Annular_regular_zero (x : Pilot3Space) (hz : pilot3AnnularHeight x = 0) : fderiv ℝ pilot3AnnularHeight x ≠ 0 := by
  intro hd
  have he := pilot3Annular_fderiv x x
  rw [hd, ContinuousLinearMap.zero_apply, real_inner_self_eq_norm_sq] at he
  rcases (pilot3Annular_zero_sq x).mp hz with h | h <;> rw [h] at he <;> norm_num at he

theorem pilot3Annular_regular : Pilot3RegularHeight pilot3AnnularHeight where
  bounded_positive := Metric.isBounded_ball.subset (fun x hx => by
    rw [Metric.mem_ball, dist_zero_right]
    exact ((pilot3Annular_positive x).mp hx).2)
  smooth_near := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, pilot3Annular_smooth.contDiffOn⟩
  zero_frontier := fun x hx => (frontier_lt_subset_eq continuous_const pilot3Annular_smooth.continuous hx).symm
  regular_zero := fun x _ hx => pilot3Annular_regular_zero x hx

theorem pilot3AnnularSine_admissible : SmoothPilot3 pilot3AnnularHeight pilot3SineFuture where
  toPilot3RegularHeight := pilot3Annular_regular
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, pilot3SineFuture_smooth.contDiffOn⟩
  slope_budget := ⟨3 / 16, 1 / 8, by norm_num, by norm_num, by norm_num,
    pilot3Annular_lipschitz, pilot3SineFuture_lipschitz⟩

theorem pilot3AnnularPlanar_admissible : SmoothPilot3 pilot3AnnularHeight (fun _ => 0) where
  toPilot3RegularHeight := pilot3Annular_regular
  smooth_future := fun _ _ => ⟨univ, isOpen_univ, mem_univ _, contDiff_const.contDiffOn⟩
  slope_budget := ⟨3 / 16, 0, by norm_num, by norm_num, by norm_num, pilot3Annular_lipschitz, by simp⟩

theorem pilot3Annular_joint : pilot3SpatialJoint pilot3AnnularHeight =
    Metric.sphere (0 : Pilot3Space) 1 ∪ Metric.sphere (0 : Pilot3Space) 2 := by
  ext x
  simp only [mem_union, Metric.mem_sphere, dist_zero_right]
  constructor
  · exact fun hx => (pilot3Annular_zero x).mp hx.2
  · intro hx
    have hz := (pilot3Annular_zero x).mpr hx
    exact ⟨pilot3_mem_closedPositive_of_regular_zero pilot3Annular_smooth.contDiffAt hz (pilot3Annular_regular_zero x hz), hz⟩

/-- A whole retained critical circle lies strictly inside the positive annulus. -/
theorem pilot3Annular_critical (x : Pilot3Space) (hx : ‖x‖ ^ 2 = 5 / 2) :
    0 < pilot3AnnularHeight x ∧ fderiv ℝ pilot3AnnularHeight x = 0 := by
  constructor
  · norm_num [pilot3AnnularHeight, hx]
  · ext v
    rw [pilot3Annular_fderiv, hx]
    norm_num

theorem pilot3Annular_critical_nonempty : ∃ x : Pilot3Space,
    0 < pilot3AnnularHeight x ∧ fderiv ℝ pilot3AnnularHeight x = 0 := by
  refine ⟨pilot3Coordinates.symm (Real.sqrt (5 / 2), 0), pilot3Annular_critical _ ?_⟩
  rw [pilot3Coordinates_norm_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)]
  norm_num

theorem pilot3Annular_curved :
    deriv (deriv (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0]))) (3 / 2) ≠ 0 ∧
    0 < pilot3AnnularHeight ((WithLp.equiv 2 _).symm ![(3 / 2 : ℝ), 0]) := by
  have he : (fun s : ℝ => pilot3SineFuture ((WithLp.equiv 2 _).symm ![s, 0])) = fun s : ℝ => Real.sin s / 8 := rfl
  have hd : deriv (fun s : ℝ => Real.sin s / 8) = fun s => Real.cos s / 8 := by
    ext s
    exact ((Real.hasDerivAt_sin s).div_const 8).deriv
  rw [he, hd, ((Real.hasDerivAt_cos (3 / 2)).div_const 8).deriv]
  constructor
  · exact div_ne_zero (neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi (by norm_num)
      (by linarith [Real.pi_gt_three] : (3 / 2 : ℝ) < Real.pi)).ne') (by norm_num)
  · norm_num [pilot3AnnularHeight, ← real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

/-- Proved integration on the actual annulus, not a disconnected-set diagnostic. -/
theorem pilot3Annular_collar_coarea : ∃ δ : ℝ, 0 < δ ∧
    ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 δ) →
      IntegrableOn (fun x => g (pilot3AnnularHeight x)) (pilot3ClosedCollar pilot3AnnularHeight δ) ∧
      (∫ x in pilot3ClosedCollar pilot3AnnularHeight δ, g (pilot3AnnularHeight x)) =
        ∫ t in Icc 0 δ, g t * pilot3HeightDensity pilot3AnnularHeight t := by
  obtain ⟨δ, hδ, _, hco⟩ := pilot3Annular_regular.exists_collar_coarea
  refine ⟨δ, hδ, fun g hg => ?_⟩
  obtain ⟨hi, _, he⟩ := hco (fun _ => 1) continuousOn_const g hg
  simpa only [mul_one, pilot3WeightedHeightDensity_one] using And.intro hi he

theorem pilot3Annular_spatial_divergence :
    (∫ x in {x | 0 < pilot3AnnularHeight x}, pilot3Laplacian pilot3SineFuture x) =
      -(∫ x, inner (𝕜 := ℝ) (pilot3Gradient pilot3SineFuture x) (pilot3Gradient pilot3AnnularHeight x) /
        ‖pilot3Gradient pilot3AnnularHeight x‖ ∂pilot3SurfaceMeasure pilot3AnnularHeight) :=
  pilot3AnnularSine_admissible.spatial_divergence

end BoundaryDraft
