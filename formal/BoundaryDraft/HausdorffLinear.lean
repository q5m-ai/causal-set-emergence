import BoundaryDraft.HausdorffDensity
import BoundaryDraft.GraphJacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Area of an injective linear image of the Euclidean plane

The range is given its intrinsic Euclidean metric. An orthonormal coordinate
map reduces its Hausdorff measure to the already normalized Euclidean plane,
where the Haar determinant transformation applies on arbitrary sets. No
ambient three-dimensional volume restricted to a plane is used.
-/

open MeasureTheory Set
open scoped ENNReal Topology Matrix
noncomputable section
namespace BoundaryDraft

private theorem plane_det_sq (T : SurfacePlane →L[ℝ] SurfacePlane) :
    T.toLinearMap.det ^ 2 =
      ‖T (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ ^ 2 *
        ‖T (EuclideanSpace.basisFun (Fin 2) ℝ 1)‖ ^ 2 -
      inner (𝕜 := ℝ) (T (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (T (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  simp only [Matrix.det_fin_two, LinearMap.toMatrix_apply,
    EuclideanSpace.basisFun_repr, PiLp.norm_sq_eq_of_L2,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  change (T (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0 *
      T (EuclideanSpace.basisFun (Fin 2) ℝ 1) 1 -
      T (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 *
      T (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1) ^ 2 = _
  ring!

/-- The normalized Hausdorff area of an injective linear image, on every
parameter set. The Jacobian is the positive Euclidean Gram factor. -/
theorem normalizedHausdorffTwo_linear_image (A : SurfacePlane →L[ℝ] JointSpace)
    (hA : Function.Injective A) (s : Set SurfacePlane) :
    normalizedHausdorffTwo (A '' s) =
      ENNReal.ofReal (graphAreaJacobian (A (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (A (EuclideanSpace.basisFun (Fin 2) ℝ 1))) * volume s := by
  let R := LinearMap.range A.toLinearMap
  letI : MeasurableSpace R := borel R
  letI : BorelSpace R := ⟨rfl⟩
  have hdim : Module.finrank ℝ R = 2 := by
    rw [LinearMap.finrank_range_of_inj hA]
    simp
  let b : OrthonormalBasis (Fin 2) ℝ R :=
    (stdOrthonormalBasis ℝ R).reindex (finCongr hdim)
  let e : SurfacePlane ≃L[ℝ] R := (LinearEquiv.ofInjective A.toLinearMap hA).toContinuousLinearEquiv
  let T : SurfacePlane →L[ℝ] SurfacePlane := b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    e.toContinuousLinearMap
  have hnorm (v : SurfacePlane) : ‖T v‖ = ‖A v‖ := b.repr.norm_map (e v)
  have hinner (v w : SurfacePlane) : inner (𝕜 := ℝ) (T v) (T w) = inner (𝕜 := ℝ) (A v) (A w) :=
    b.repr.inner_map_map (e v) (e w)
  have hdet : |T.toLinearMap.det| =
      graphAreaJacobian (A (EuclideanSpace.basisFun (Fin 2) ℝ 0))
        (A (EuclideanSpace.basisFun (Fin 2) ℝ 1)) := by
    rw [graphAreaJacobian_eq_sqrt_gram, ← hnorm, ← hnorm, ← hinner,
      ← plane_det_sq, Real.sqrt_sq_eq_abs]
  have himage : A '' s = Subtype.val '' (e '' s) := by
    rw [← image_comp]
    rfl
  change ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure JointSpace) (A '' s) = _
  have hsub : (μH[2] : Measure JointSpace) (Subtype.val '' (e '' s)) =
      (μH[2] : Measure R) (e '' s) :=
    R.subtypeₗᵢ.isometry.hausdorffMeasure_image (Or.inl (by norm_num)) (e '' s)
  rw [himage, hsub]
  have hrepr : (μH[2] : Measure SurfacePlane) (b.repr '' (e '' s)) =
      (μH[2] : Measure R) (e '' s) :=
    b.repr.isometry.hausdorffMeasure_image (Or.inl (by norm_num)) (e '' s)
  rw [← hrepr, ← image_comp]
  change ENNReal.ofReal (Real.pi / 4) * (μH[2] : Measure SurfacePlane) (T '' s) = _
  rw [normalized_hausdorff_plane_eq_volume_apply,
    Measure.addHaar_image_continuousLinearMap, hdet]

private theorem plane_dual_norm_sq (L : SurfacePlane →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = L (EuclideanSpace.basisFun (Fin 2) ℝ 0) ^ 2 +
      L (EuclideanSpace.basisFun (Fin 2) ℝ 1) ^ 2 := by
  let v := (InnerProductSpace.toDual ℝ SurfacePlane).symm L
  have hn : ‖v‖ = ‖L‖ := (InnerProductSpace.toDual ℝ SurfacePlane).symm.norm_map L
  have he (i : Fin 2) : L (EuclideanSpace.basisFun (Fin 2) ℝ i) = v i := by
    have h := (InnerProductSpace.toDual ℝ SurfacePlane).apply_symm_apply L
    have hh := congrArg (fun f : SurfacePlane →L[ℝ] ℝ => f (EuclideanSpace.basisFun (Fin 2) ℝ i)) h
    calc
      L (EuclideanSpace.basisFun (Fin 2) ℝ i) = inner (𝕜 := ℝ) v
          (EuclideanSpace.basisFun (Fin 2) ℝ i) := hh.symm
      _ = v i := by simp [EuclideanSpace.basisFun_apply, real_inner_comm]
  rw [← hn, he 0, he 1]
  simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The graph's tangential Gram factor is the familiar scalar-graph Jacobian,
with the operator norm computed for the Euclidean base metric. -/
theorem surfaceGraphDerivative_areaJacobian (L : SurfacePlane →L[ℝ] ℝ) :
    graphAreaJacobian
      (surfaceGraphDerivative L (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (surfaceGraphDerivative L (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      Real.sqrt (1 + ‖L‖ ^ 2) := by
  rw [graphAreaJacobian_eq_sqrt_gram, plane_dual_norm_sq]
  congr 1
  simp only [surfaceGraphDerivative_norm_sq]
  have hi : inner (𝕜 := ℝ)
      (surfaceGraphDerivative L (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (surfaceGraphDerivative L (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      L (EuclideanSpace.basisFun (Fin 2) ℝ 0) * L (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    simp [surfaceGraphDerivative, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_succ, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply, mul_comm]
  rw [hi]
  simp only [OrthonormalBasis.norm_eq_one, one_pow]
  ring

/-- Exact normalized Hausdorff measure of the tangent graph image. The
statement includes nonmeasurable sets and sets of infinite measure. -/
theorem normalizedHausdorffTwo_surfaceGraphDerivative_image
    (L : SurfacePlane →L[ℝ] ℝ) (s : Set SurfacePlane) :
    normalizedHausdorffTwo (surfaceGraphDerivative L '' s) =
      ENNReal.ofReal (Real.sqrt (1 + ‖L‖ ^ 2)) * volume s := by
  rw [normalizedHausdorffTwo_linear_image _ (surfaceGraphDerivative_injective L),
    surfaceGraphDerivative_areaJacobian]

end BoundaryDraft
