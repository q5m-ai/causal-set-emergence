import BoundaryDraft

/-!
Independent contracts for Euclidean tangent-to-graph distortion and the
covering half of planar normalization. Full planar normalization is tested in
`HausdorffPlaneRegression.lean`, and scalar-graph area is tested separately in
`HausdorffAreaRegression.lean`. The general graph-cap limit remains open.
-/

open BoundaryDraft MeasureTheory Set
open scoped Topology MeasureTheory ENNReal NNReal
noncomputable section

-- A coordinate supremum norm would give 1 here, not 2.
example : ‖surfaceGraphDerivative (0 : SurfacePlane →L[ℝ] ℝ)
    ((WithLp.equiv 2 _).symm ![1, 1])‖ ^ 2 = 2 := by
  rw [surfaceGraphDerivative_norm_sq]
  norm_num [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

-- The graph derivative is the actual derivative, including tilted graphs.
example (L : SurfacePlane →L[ℝ] ℝ) (a : SurfacePlane) :
    HasStrictFDerivAt (surfaceGraph L) (surfaceGraphDerivative L) a :=
  hasStrictFDerivAt_surfaceGraph L L a L.hasStrictFDerivAt

-- Zero approximation error is allowed in the uniform estimate. No finiteness
-- assumption is needed, so this also tests the infinite-measure contract.
example (f : SurfacePlane → JointSpace) (L : SurfacePlane →L[ℝ] ℝ) (s : Set SurfacePlane)
    (hf : ApproximatesLinearOn f (surfaceGraphDerivative L) s 0) :
    (μH[2] : Measure JointSpace) (f '' s) = μH[2] (surfaceGraphDerivative L '' s) := by
  have hb := approximatesLinearOn_hausdorff_bounds f (surfaceGraphDerivative L) s 0
    (by norm_num) (surfaceGraphDerivative_noncontracting L) hf
  have hb' : μH[2] (surfaceGraphDerivative L '' s) ≤ μH[2] (f '' s) ∧
      μH[2] (f '' s) ≤ μH[2] (surfaceGraphDerivative L '' s) := by simpa using hb
  exact le_antisymm hb'.2 hb'.1

-- A genuinely nonlinear C¹ graph: both bounds apply to every subset, without
-- an additional measurability premise, at an arbitrary base point.
example (a : SurfacePlane) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ⊆ Metric.ball a r,
      (1 / 4 : ℝ≥0∞) * μH[2]
        (surfaceGraphDerivative (fderiv ℝ (fun x : SurfacePlane => x 0 ^ 2 + x 1 ^ 2) a) '' s) ≤
          μH[2] (surfaceGraph (fun x : SurfacePlane => x 0 ^ 2 + x 1 ^ 2) '' s) ∧
      μH[2] (surfaceGraph (fun x : SurfacePlane => x 0 ^ 2 + x 1 ^ 2) '' s) ≤
        (9 / 4 : ℝ≥0∞) * μH[2]
          (surfaceGraphDerivative (fderiv ℝ (fun x : SurfacePlane => x 0 ^ 2 + x 1 ^ 2) a) '' s) := by
  obtain ⟨r, hr, _, hb⟩ := surfaceGraph_local_hausdorff_bounds
    (fun x : SurfacePlane => x 0 ^ 2 + x 1 ^ 2) univ isOpen_univ
    (by
      have hi (i : Fin 2) : ContDiff ℝ 1 (fun x : SurfacePlane => x i) :=
        (contDiff_apply ℝ ℝ i).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).contDiff
      exact ((hi 0).pow 2 |>.add ((hi 1).pow 2)).contDiffOn) a
    (mem_univ a) (1 / 2) (by norm_num) (by norm_num [← NNReal.coe_lt_coe])
  have hlow : ((1 - (1 / 2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ^ 2 = 1 / 4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).mp
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div, NNReal.coe_sub
      (show (1 / 2 : ℝ≥0) ≤ 1 by norm_num [← NNReal.coe_le_coe])]
  have hupp : ((1 + (1 / 2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ^ 2 = 9 / 4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne).mp
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal]
    norm_num [ENNReal.toReal_div]
  exact ⟨r, hr, fun s hs => by simpa only [hlow, hupp] using hb s hs⟩

-- A one-sided bound, not an assertion of normalized equality on a disk.
example (x : SurfacePlane) :
    ENNReal.ofReal (Real.pi / 4) * μH[2] (Metric.closedBall x 1) ≤ ENNReal.ofReal Real.pi := by
  simpa using normalized_hausdorff_plane_le_volume (Metric.closedBall x 1)

-- Arbitrary Lebesgue-null sets can be discarded in disk-covering arguments.
example (s : Set SurfacePlane) (hs : volume s = 0) :
    (μH[2] : Measure SurfacePlane) s = 0 :=
  hausdorff_plane_zero_of_volume_zero s hs
