import BoundaryDraft.ActionTransport
import BoundaryDraft.ExpectedLimits

/-!
Independent finite-density contracts, concrete inverse-coordinate checks, and
calibration on the original unequal-axis ellipsoid. A boost is not a genuinely
curved future face; no new geometric boundary target is asserted here.
-/

open BoundaryDraft MeasureTheory Set Filter
open scoped Topology BigOperators Pointwise

noncomputable section
namespace ActionTransportRegression

-- No determinant, measure, action or boundary-limit identity is a premise.
example (L : Spacetime ≃ₗ[ℝ] Spacetime) (a : Spacetime)
    (hg : ∀ x y, minkowskiInner (L x) (L y) = minkowskiInner x y)
    (ht : 0 < L (timeAxis 1) 0) (M : Set Spacetime)
    (hM : BoundedCausalRegion M) (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ ((fun x => L x + a) '' M) = continuumMean ρ M ∧
      expectedBDGAction ρ ((fun x => L x + a) '' M) = expectedBDGAction ρ M := by
  let F : PoincareEquiv := ⟨L, a, hg, ht⟩
  exact ⟨F.continuumMean_image ρ M, F.expectedBDGAction_image hM hρ⟩

-- Expand the original bilocal action, independently of its name.
example (F : PoincareEquiv) (M : Set Spacetime) (ρ : ℝ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ * ((∫ _x in F '' M, (1 : ℝ)) - ρ *
      ∫ x in F '' M, ∫ y in F '' M ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
    (4 / Real.sqrt 6) * Real.sqrt ρ * ((∫ _x in M, (1 : ℝ)) - ρ *
      ∫ x in M, ∫ y in M ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) :=
  F.continuumMean_image ρ M

-- Compact domination on BOTH sides, at both integral levels, is available.
example (F : PoincareEquiv) (M : Set Spacetime) (hM : BoundedCausalRegion M)
    (ρ : ℝ) (x : Spacetime) :
    IntegrableOn (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2))
        (M ∩ causalFuture x) ∧
      IntegrableOn (fun y => bdgKernel ((Real.pi / 24) * ρ * intervalSq (F x) y ^ 2))
        (F '' M ∩ causalFuture (F x)) ∧
      IntegrableOn (fun x => ∫ y in F '' M ∩ causalFuture x,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) (F '' M) :=
  ⟨integrableOn_bdg_future_of_bounded hM.bounded ρ x,
    integrableOn_bdg_future_of_bounded (hM.poincare_image F).bounded ρ (F x),
    integrableOn_bdg_outer (hM.poincare_image F).measurable (hM.poincare_image F).bounded ρ⟩

/-- A genuine boost with velocity 3/5, written in independent coordinates. -/
def boostForward (x : Spacetime) : Spacetime :=
  ![5 / 4 * x 0 + 3 / 4 * x 1, 3 / 4 * x 0 + 5 / 4 * x 1, x 2, x 3]

def boostBackward (x : Spacetime) : Spacetime :=
  ![5 / 4 * x 0 - 3 / 4 * x 1, -3 / 4 * x 0 + 5 / 4 * x 1, x 2, x 3]

theorem boost_left_inverse (x : Spacetime) : boostBackward (boostForward x) = x := by
  ext i
  fin_cases i <;> simp [boostForward, boostBackward] <;> ring

theorem boost_right_inverse (x : Spacetime) : boostForward (boostBackward x) = x := by
  ext i
  fin_cases i <;> simp [boostForward, boostBackward] <;> ring

def boostLinear : Spacetime ≃ₗ[ℝ] Spacetime where
  toFun := boostForward
  invFun := boostBackward
  left_inv := boost_left_inverse
  right_inv := boost_right_inverse
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [boostForward] <;> ring
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp [boostForward] <;> ring

def shiftedBoost : PoincareEquiv where
  linear := boostLinear
  translation := ![2, -1, 3, 0]
  preserves_inner := by
    intro x y
    change minkowskiInner (boostForward x) (boostForward y) = _
    simp [minkowskiInner, boostForward, Fin.sum_univ_succ]
    ring
  future_time := by norm_num [boostLinear, boostForward, timeAxis]

example : boostForward ![1, 0, 0, 0] = ![5 / 4, 3 / 4, 0, 0] := by
  norm_num [boostForward, Matrix.cons_val_two, Matrix.cons_val_three]

-- Check the API's inverse against the independent inverse formula, including
-- the nonzero translation (which must be subtracted BEFORE the inverse boost).
example (z : Spacetime) :
    shiftedBoost.symm z = boostBackward (z - ![2, -1, 3, 0]) := by
  change boostLinear.symm z - boostLinear.symm ![2, -1, 3, 0] = _
  rw [← map_sub]
  rfl

example (z : Spacetime) : shiftedBoost (shiftedBoost.symm z) = z :=
  shiftedBoost.apply_symm_apply z

example (x : Spacetime) : shiftedBoost.symm (shiftedBoost x) = x :=
  shiftedBoost.symm_apply_apply x

-- A null pair and the diagonal survive the affine transport, not only the
-- strictly timelike set used to compute Alexandrov volume.
example : shiftedBoost ![1, 1, 0, 0] ∈ causalFuture (shiftedBoost 0) := by
  rw [shiftedBoost.causalFuture_map]
  norm_num [causalFuture, spatialSeparationSq, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.cons_val_three]

example (x : Spacetime) : shiftedBoost x ∈ causalFuture (shiftedBoost x) := by
  simp [causalFuture, spatialSeparationSq]

/-- Spatial parity, constructed from the existing audited Lorentz reflection. -/
def parity : PoincareEquiv where
  linear := LinearEquiv.ofInvolutive (lorentzReflection ![0, 1, 0, 0])
    (fun y => lorentzReflection_involutive _ y (by
      norm_num [minkowskiInner, Fin.sum_univ_succ]))
  translation := 0
  preserves_inner := fun x y => lorentzReflection_minkowskiInner _ x y (by
    norm_num [minkowskiInner, Fin.sum_univ_succ])
  future_time := by
    change 0 < lorentzReflection ![0, 1, 0, 0] (timeAxis 1) 0
    norm_num [lorentzReflection_apply, minkowskiInner, Fin.sum_univ_succ, timeAxis]

example : LinearMap.det parity.linear.toLinearMap = -1 := by
  change LinearMap.det (Matrix.toLin' (lorentzReflectionMatrix ![0, 1, 0, 0])) = -1
  rw [LinearMap.det_toLin']
  exact det_lorentzReflectionMatrix _ (by norm_num [minkowskiInner, Fin.sum_univ_succ])

example (x : Spacetime) : parity x = ![x 0, -x 1, x 2, x 3] := by
  change lorentzReflection ![0, 1, 0, 0] x + 0 = _
  ext i
  fin_cases i <;> norm_num [lorentzReflection_apply, minkowskiInner, Fin.sum_univ_succ,
    Matrix.vecHead, Matrix.vecTail] <;> first | rfl | ring

example (M : Set Spacetime) : volume (parity '' M) = volume M := parity.volume_image M

example (M : Set Spacetime) (ρ : ℝ) : continuumMean ρ (parity '' M) = continuumMean ρ M :=
  parity.continuumMean_image ρ M

/-- The same connected variable-angle base case, with the original hypotheses. -/
def unequalEllipsoid : Set Spacetime :=
  graphCapRegion (ellipsoidProfile (1 / 4) ![1, 2, 3])

theorem unequalEllipsoid_region : BoundedCausalRegion unequalEllipsoid := by
  apply GraphCapData.boundedCausalRegion
  apply ellipsoid_graphCapData (1 / 4) ![1, 2, 3] (by norm_num)
  intro i
  fin_cases i <;> norm_num

-- Membership in the transported set is checked using explicit inverse
-- coordinates, not by postulating a second geometric ellipsoid formula.
example (z : Spacetime) : z ∈ shiftedBoost '' unequalEllipsoid ↔
    boostBackward (z - ![2, -1, 3, 0]) ∈ unequalEllipsoid := by
  have hi : shiftedBoost.symm z = boostBackward (z - ![2, -1, 3, 0]) := by
    change boostLinear.symm z - boostLinear.symm ![2, -1, 3, 0] = _
    rw [← map_sub]
    rfl
  rw [← hi]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    exact ⟨shiftedBoost.symm z, hz, shiftedBoost.apply_symm_apply z⟩

example (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (shiftedBoost '' unequalEllipsoid) = continuumMean ρ unequalEllipsoid ∧
      expectedBDGAction ρ (shiftedBoost '' unequalEllipsoid) = expectedBDGAction ρ unequalEllipsoid :=
  ⟨shiftedBoost.continuumMean_image ρ unequalEllipsoid,
    shiftedBoost.expectedBDGAction_image unequalEllipsoid_region hρ⟩

-- Covariance calibration only: the boosted future boundary is still a plane.
example : Tendsto (fun ρ => continuumMean ρ (shiftedBoost '' unequalEllipsoid)) atTop
    (𝓝 (48 * Real.pi)) := by
  have h := ellipsoidLimitGoal (1 / 4) ![1, 2, 3] (by norm_num) (by
    intro i; fin_cases i <;> norm_num)
  simp only [shiftedBoost.continuumMean_image]
  convert h using 1
  norm_num [unequalEllipsoid, Fin.prod_univ_succ]
  ring

-- Four coordinates are dilated: volume gets 16, action 4, density 16.
example : volume (dilateRegion 2 unequalEllipsoid) = 16 * volume unequalEllipsoid := by
  rw [volume_dilateRegion (by norm_num)]
  norm_num

example (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ ((fun x : Spacetime => (2 : ℝ) • x) '' unequalEllipsoid) =
      4 * continuumMean (ρ * 16) unequalEllipsoid := by
  convert continuumMean_dilate (by norm_num : (0 : ℝ) < 2) hρ unequalEllipsoid using 1
  norm_num

example (ρ : ℝ) (hρ : 0 < ρ) :
    expectedBDGAction ρ (dilateRegion 2 unequalEllipsoid) =
      4 * expectedBDGAction (ρ * 16) unequalEllipsoid := by
  convert expectedBDGAction_dilate unequalEllipsoid_region
    (by norm_num : (0 : ℝ) < 2) hρ using 1
  norm_num

-- Reciprocal scaling catches the opposite density convention as well.
example (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (dilateRegion (1 / 2) unequalEllipsoid) =
      (1 / 4) * continuumMean (ρ * (1 / 16)) unequalEllipsoid := by
  convert continuumMean_dilate (by norm_num : (0 : ℝ) < 1 / 2) hρ unequalEllipsoid using 1
  norm_num

example (z : Spacetime) :
    (dilationHomeomorph 2 (by norm_num)).symm z = (1 / 2 : ℝ) • z := by
  simp [dilationHomeomorph_symm_apply, one_div]

example (x : Spacetime) : (1 / 2 : ℝ) • ((2 : ℝ) • x) = x := by
  rw [smul_smul]
  norm_num

example (M : Set Spacetime) : dilateRegion (1 / 2) (dilateRegion 2 M) = M := by
  rw [dilateRegion, dilateRegion, Set.image_image]
  have he : (fun x : Spacetime => (1 / 2 : ℝ) • ((2 : ℝ) • x)) = id := by
    funext x
    rw [smul_smul]
    norm_num
  rw [he, image_id]

-- The expected-action target is the original probability integral, not an
-- observable or probability law defined through the deterministic action.
example (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ c, discreteBDGAction ρ c ∂FinitePoisson.law
      (ENNReal.ofReal ρ • volume.restrict (shiftedBoost '' unequalEllipsoid))) =
    ∫ c, discreteBDGAction ρ c ∂FinitePoisson.law
      (ENNReal.ofReal ρ • volume.restrict unequalEllipsoid) :=
  shiftedBoost.expectedBDGAction_image unequalEllipsoid_region hρ

-- Empty and nonempty null-volume sets are not excluded by the deterministic API.
example (F : PoincareEquiv) (ρ : ℝ) : continuumMean ρ (F '' ∅) = 0 := by
  simp [continuumMean]

example (s : ℝ) (hs : 0 < s) (x : Spacetime) (ρ : ℝ) (hρ : 0 < ρ) :
    continuumMean ρ (dilateRegion s {x}) = 0 := by
  rw [continuumMean_dilate hs hρ]
  simp [continuumMean]

end ActionTransportRegression
