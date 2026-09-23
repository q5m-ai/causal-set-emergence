import BoundaryDraft.EllipsoidJoint
import BoundaryDraft.LorentzReflection

/-! # The strictly positive Lorentzian angle of an ellipsoid joint

The boost is chosen on the positive branch. Its cosh and sinh are established
separately, including signs; no unsigned square-root inference is used.
-/

open scoped BigOperators
noncomputable section
namespace BoundaryDraft

/-- Positive rapidity when `0 < k < 1`. -/
def jointRapidity (k : ℝ) : ℝ := Real.log ((1 + k) / Real.sqrt (1 - k ^ 2))

/-- `coth` is represented by the quotient of the actual hyperbolic functions. -/
def jointCoth (k : ℝ) : ℝ := Real.cosh (jointRapidity k) / Real.sinh (jointRapidity k)

theorem jointRapidity_identities (k : ℝ) (hk : 0 < k) (hk1 : k < 1) :
    0 < jointRapidity k ∧
    Real.cosh (jointRapidity k) = 1 / Real.sqrt (1 - k ^ 2) ∧
    Real.sinh (jointRapidity k) = k / Real.sqrt (1 - k ^ 2) ∧
    Real.tanh (jointRapidity k) = k ∧ jointCoth k = 1 / k := by
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  have hs := Real.sqrt_pos.mpr hd
  have hs2 := Real.sq_sqrt hd.le
  have hu : 0 < (1 + k) / Real.sqrt (1 - k ^ 2) := by positivity
  have hi : ((1 + k) / Real.sqrt (1 - k ^ 2))⁻¹ =
      (1 - k) / Real.sqrt (1 - k ^ 2) := by
    rw [inv_div]
    apply (div_eq_div_iff (by positivity) hs.ne').mpr
    nlinarith
  have hc : Real.cosh (jointRapidity k) = 1 / Real.sqrt (1 - k ^ 2) := by
    rw [jointRapidity, Real.cosh_log hu, hi]
    ring
  have hh : Real.sinh (jointRapidity k) = k / Real.sqrt (1 - k ^ 2) := by
    rw [jointRapidity, Real.sinh_log hu, hi]
    ring
  refine ⟨?_, hc, hh, ?_, ?_⟩
  · apply Real.log_pos
    apply (one_lt_div hs).mpr
    nlinarith [Real.sqrt_nonneg (1 - k ^ 2)]
  · rw [Real.tanh_eq_sinh_div_cosh, hc, hh]
    field_simp
  · rw [jointCoth, hc, hh]
    field_simp

/-- Two face-tangent vectors orthogonal to the joint, pointing inward as in
the proof notes: `(0,n)` and `(-k,n)`. Signature is `(+---)`. -/
theorem joint_face_vectors (n : JointSpace) (hn : ‖n‖ = 1) (k : ℝ) :
    minkowskiInner (Fin.cons 0 n) (Fin.cons 0 n) = -1 ∧
    minkowskiInner (Fin.cons (-k) n) (Fin.cons (-k) n) = -(1 - k ^ 2) ∧
    minkowskiInner (Fin.cons 0 n) (Fin.cons (-k) n) = -1 := by
  have hn2 : ∑ i : Fin 3, n i ^ 2 = 1 := by
    have := congrArg (fun r : ℝ => r ^ 2) hn
    simpa [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs] using this
  simp [minkowskiInner, ← pow_two, hn2]

/-- The normalized spacelike face tangents have Lorentzian inner product
`-cosh θ`. The raw graph-face vector has positive length squared `1-k²`
in the opposite-sign convention, justified by strict spacelikeness. -/
theorem joint_face_cosh (n : JointSpace) (hn : ‖n‖ = 1) (k : ℝ)
    (hk : 0 < k) (hk1 : k < 1) :
    -minkowskiInner (Fin.cons 0 n)
      ((Real.sqrt (1 - k ^ 2))⁻¹ • (Fin.cons (-k) n : Spacetime)) =
        Real.cosh (jointRapidity k) := by
  rw [minkowskiInner_smul_right, (joint_face_vectors n hn k).2.2,
    (jointRapidity_identities k hk hk1).2.1]
  ring

/-- The concrete strict positive-branch angle weight at every joint point. -/
theorem ellipsoid_coth_eq (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a)
    (hb : ∀ i, 2 * a < b i) (x : JointSpace) (hx : x ∈ ellipsoidJoint b) :
    jointCoth (ellipsoidSlope a b x) = 1 / ‖ellipsoidGradient a b x‖ := by
  exact (jointRapidity_identities _
    (ellipsoidSlope_pos a b ha (fun i => by linarith [hb i]) x hx)
    (ellipsoidSlope_lt_one a b ha hb x hx)).2.2.2.2

/-- Both face tangents are orthogonal to every tangent of the regular joint,
where joint tangency is expressed by the kernel of the actual differential. -/
theorem ellipsoid_face_joint_orthogonal (a : ℝ) (b : Fin 3 → ℝ) (x v : JointSpace)
    (hv : fderiv ℝ (fun y : JointSpace => ellipsoidProfile a b y) x v = 0) :
    minkowskiInner (Fin.cons 0 (ellipsoidInward a b x)) (Fin.cons 0 v) = 0 ∧
    minkowskiInner (Fin.cons (-ellipsoidSlope a b x) (ellipsoidInward a b x))
      (Fin.cons 0 v) = 0 := by
  rw [(hasGradientAt_ellipsoidProfile a b x).hasFDerivAt.fderiv] at hv
  have hi : inner (𝕜 := ℝ) (ellipsoidInward a b x) v = 0 := by
    simp only [ellipsoidInward, inner_smul_left, RCLike.conj_to_real]
    change (ellipsoidSlope a b x)⁻¹ *
      ((InnerProductSpace.toDual ℝ JointSpace) (ellipsoidGradient a b x)) v = 0
    rw [hv, mul_zero]
  have hs : ∑ i : Fin 3, ellipsoidInward a b x i * v i = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hi
  simp [minkowskiInner, hs]

/-- The graph-face tangent is genuinely unit spacelike after normalization. -/
theorem joint_graph_unit (n : JointSpace) (hn : ‖n‖ = 1) (k : ℝ)
    (hk : 0 < k) (hk1 : k < 1) :
    minkowskiInner ((Real.sqrt (1 - k ^ 2))⁻¹ • (Fin.cons (-k) n : Spacetime))
      ((Real.sqrt (1 - k ^ 2))⁻¹ • (Fin.cons (-k) n : Spacetime)) = -1 := by
  have hd : 0 < 1 - k ^ 2 := by nlinarith
  rw [minkowskiInner_smul_left, minkowskiInner_smul_right,
    (joint_face_vectors n hn k).2.1]
  have hs := Real.sq_sqrt hd.le
  have hnz := (Real.sqrt_pos.mpr hd).ne'
  field_simp

end BoundaryDraft
