import BoundaryDraft.TwoFaceLongGeometry
import BoundaryDraft.TwoFaceExamples

/-!
Independent regressions of the GEOMETRIC fibre theorem. No jet, derivative
bound, contact transversality or minimum root-to-cutoff distance is a premise.
These are not regressions of spatial/directional averaging or cancellation.
-/

open BoundaryDraft BoundaryDraft.TwoFaceLongGeometry
open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval

noncomputable section
namespace TwoFaceLongGeometryRegression

/-- The actual fibre minus its canonical quadratic polynomial. -/
def remainder (g : ℝ → ℝ → ℝ) (δ V σ : ℝ) : ℝ :=
  MonotoneHinge.fibre g weight δ V σ -
    (MonotoneHinge.F0 g weight δ V + MonotoneHinge.F1 g weight δ V * σ +
      MonotoneHinge.F2 g weight δ V * σ ^ 2)

private theorem bound_nonneg {δ V c A M B : ℝ} (hV : δ < V) (hc : 0 < c)
    (hM : 0 ≤ M) (hB : 0 ≤ B) : 0 ≤ MonotoneHinge.remainderBound δ V c A M B := by
  have hd : 0 < V - δ := sub_pos.mpr hV
  unfold MonotoneHinge.remainderBound
  positivity

/-- Regression helper: one neighborhood and one bound precede all fibres. -/
def UniformFibres (h f : Spatial → ℝ) (δ : ℝ) : Prop :=
  ∃ V ε C : ℝ, δ < V ∧ 0 < ε ∧ 0 ≤ C ∧ ∀ (x : Spatial) (ω : OverlapSphere),
    (remainder (twoFaceRayGap h f x ω) δ V =o[𝓝[>] 0] (fun σ => σ ^ 2)) ∧
    ∀ σ ∈ Ioc 0 ε, |remainder (twoFaceRayGap h f x ω) δ V σ| / σ ^ 2 ≤ C

private theorem uniform_from_admissible {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {δ : ℝ} (hδ : 0 < δ) : UniformFibres h f δ := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, hc, _, hM, hB, hall⟩ := geometric_specialization hf hδ
  exact ⟨V, ε, MonotoneHinge.remainderBound δ V c A M B, hV, hε,
    bound_nonneg hV hc hM hB, fun x ω => ⟨(hall x ω).2.2.1, (hall x ω).2.2.2.1⟩⟩

-- Every original planar cap, not a smoother or restricted replacement.
theorem original_planar {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    {δ : ℝ} (hδ : 0 < δ) : UniformFibres h (fun _ => 0) δ :=
  uniform_from_admissible hh.twoFace_planar hδ

private def cap : Spatial → ℝ := ellipsoidProfile (1 / 4) ![1, 2, 3]

private theorem cap_admissible : AdmissibleGraphCap cap :=
  ellipsoid_admissible _ _ (by norm_num) (fun i => by fin_cases i <;> norm_num)

private theorem planar_gap (h : Spatial → ℝ) (x : Spatial) (ω : OverlapSphere) (σ v : ℝ) :
    twoFaceRayGap h (fun _ => 0) x ω σ v = max 0 (h x) - (v + σ / v) / 2 := by
  simp [twoFaceRayGap, twoFaceGap]

-- The same unequal-axis cap includes its positive-height critical point.
theorem unequal_axis_critical_point :
    cap 0 = 1 / 4 ∧ fderiv ℝ (fun x : JointSpace => cap x) 0 = 0 ∧
      UniformFibres cap (fun _ => 0) (1 / 4) := by
  refine ⟨by norm_num [cap, ellipsoidProfile], ?_, original_planar cap_admissible (by norm_num)⟩
  have hd := (hasGradientAt_ellipsoidProfile (1 / 4) ![1, 2, 3] 0).hasFDerivAt
  have hz : ellipsoidGradient (1 / 4) ![1, 2, 3] 0 = 0 := by
    ext i
    simp [ellipsoidGradient]
  change fderiv ℝ (fun x : JointSpace => ellipsoidProfile (1 / 4) ![1, 2, 3] x) 0 = _
  rw [hd.fderiv, hz]
  simp

-- Exact cutoff contact: all right fibres and all three coefficients vanish,
-- while the theorem still supplies the same neighborhood for every direction.
theorem exact_cutoff_contact : ∃ V ε : ℝ, 1 / 2 < V ∧ 0 < ε ∧
    ∀ ω : OverlapSphere,
      MonotoneHinge.F0 (twoFaceRayGap cap (fun _ => 0) 0 ω) weight (1 / 2) V = 0 ∧
      MonotoneHinge.F1 (twoFaceRayGap cap (fun _ => 0) 0 ω) weight (1 / 2) V = 0 ∧
      MonotoneHinge.F2 (twoFaceRayGap cap (fun _ => 0) 0 ω) weight (1 / 2) V = 0 ∧
      ∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre (twoFaceRayGap cap (fun _ => 0) 0 ω)
        weight (1 / 2) V σ = 0 := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, _, _, _, _, hall⟩ :=
    exists_hypotheses cap_admissible.twoFace_planar (δ := 1 / 2) (by norm_num)
  refine ⟨V, ε, hV, hε, ?_⟩
  intro ω
  have hz : twoFaceRayGap cap (fun _ => 0) 0 ω 0 (1 / 2) = 0 := by
    norm_num [planar_gap, cap, ellipsoidProfile]
  obtain ⟨h0, h1, h2⟩ := MonotoneHinge.coefficients_zero (J := weight) (V := V) hz.le
  exact ⟨h0, h1, h2, fun _ hσ => (hall 0 ω).fibre_zero hz.le hσ⟩

-- Inactive fibres are handled pointwise, not deleted as an exceptional set.
theorem inactive_fibre : ∃ V ε : ℝ, 1 / 4 < V ∧ 0 < ε ∧
    ∀ ω : OverlapSphere,
      twoFaceRayGap cap (fun _ => 0) ![2, 0, 0] ω 0 (1 / 4) < 0 ∧
      ∀ σ ∈ Icc 0 ε, MonotoneHinge.fibre (twoFaceRayGap cap (fun _ => 0) ![2, 0, 0] ω)
        weight (1 / 4) V σ = 0 := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, _, _, _, _, hall⟩ :=
    exists_hypotheses cap_admissible.twoFace_planar (δ := 1 / 4) (by norm_num)
  refine ⟨V, ε, hV, hε, ?_⟩
  intro ω
  have hn : twoFaceRayGap cap (fun _ => 0) ![2, 0, 0] ω 0 (1 / 4) < 0 := by
    norm_num [planar_gap, cap, ellipsoidProfile, Fin.sum_univ_succ]
  exact ⟨hn, fun _ hσ => (hall _ ω).fibre_zero hn.le hσ⟩

-- Genuine future curvature is retained along with its nonaffinity witness.
theorem curved_sine_future : ∃ c : ℝ, 0 < c ∧
    AdmissibleTwoFace (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) ∧
    twoFaceSine c ![Real.pi / 2, 0, 0] ≠
      (twoFaceSine c ![0, 0, 0] + twoFaceSine c ![Real.pi, 0, 0]) / 2 ∧
    ∀ δ : ℝ, 0 < δ → UniformFibres (ellipsoidProfile (1 / 4) (fun _ => 4)) (twoFaceSine c) δ := by
  obtain ⟨c, hc, hf, _, hcurve⟩ := twoFace_curved_nonvacuity
  exact ⟨c, hc, hf, hcurve, fun _ hδ => uniform_from_admissible hf hδ⟩

/-- A family inside ONE fixed cap, with old roots `1/4 + t`. -/
def approachingPoint (t : ℝ) : Spatial := ![Real.sqrt (1 / 2 - 2 * t), 0, 0]

private theorem approaching_height {t : ℝ} (ht : t ∈ Ioc 0 (1 / 4)) :
    cap (approachingPoint t) = 1 / 8 + t / 2 := by
  have hs : 0 ≤ (1 : ℝ) / 2 - 2 * t := by linarith [ht.2]
  norm_num [cap, approachingPoint, ellipsoidProfile, Fin.sum_univ_succ, Real.sq_sqrt hs]
  ring

-- The root-to-cutoff distance tends to zero. The bound below nevertheless
-- holds on ONE common interval, including fibres already closed at that sigma.
theorem roots_approach_cutoff : ∃ V ε C : ℝ, 1 / 4 < V ∧ 0 < ε ∧ 0 ≤ C ∧
    (∀ t ∈ Ioc 0 (1 / 4), ∀ ω : OverlapSphere,
      MonotoneHinge.oldRoot (twoFaceRayGap cap (fun _ => 0) (approachingPoint t) ω) (1 / 4) V =
        1 / 4 + t ∧
      (remainder (twoFaceRayGap cap (fun _ => 0) (approachingPoint t) ω) (1 / 4) V
        =o[𝓝[>] 0] (fun σ => σ ^ 2)) ∧
      ∀ σ ∈ Ioc 0 ε,
        |remainder (twoFaceRayGap cap (fun _ => 0) (approachingPoint t) ω) (1 / 4) V σ| / σ ^ 2 ≤ C) ∧
    ∀ ω : OverlapSphere,
      Tendsto (fun t => MonotoneHinge.oldRoot
        (twoFaceRayGap cap (fun _ => 0) (approachingPoint t) ω) (1 / 4) V)
        (𝓝[>] 0) (𝓝 (1 / 4)) := by
  obtain ⟨V, ε, c, A, M, B, hV, hε, hc, _, hM, hB, hall⟩ :=
    exists_hypotheses cap_admissible.twoFace_planar (δ := 1 / 4) (by norm_num)
  have hroot (t : ℝ) (ht : t ∈ Ioc 0 (1 / 4)) (ω : OverlapSphere) :
      MonotoneHinge.oldRoot (twoFaceRayGap cap (fun _ => 0) (approachingPoint t) ω) (1 / 4) V =
        1 / 4 + t := by
    have hh := hall (approachingPoint t) ω
    have hp : 0 ≤ (1 : ℝ) / 8 + t / 2 := by linarith [ht.1]
    have hg (v : ℝ) : twoFaceRayGap cap (fun _ => 0) (approachingPoint t) ω 0 v =
        1 / 8 + t / 2 - v / 2 := by
      simp only [planar_gap, approaching_height ht, max_eq_right hp, zero_div, add_zero]
    have hclear := hh.clearance
    rw [hg] at hclear
    exact hh.oldRoot_eq ⟨by linarith [ht.1], by linarith⟩ (by rw [hg]; ring)
  refine ⟨V, ε, MonotoneHinge.remainderBound (1 / 4) V c A M B,
    hV, hε, bound_nonneg hV hc hM hB, ?_, ?_⟩
  · intro t ht ω
    exact ⟨hroot t ht ω, (hall _ ω).right_quadratic_jet,
      fun _ hσ => (hall _ ω).normalized_remainder_bound hσ⟩
  · intro ω
    have hl : Tendsto (fun t : ℝ => 1 / 4 + t) (𝓝[>] 0) (𝓝 (1 / 4)) := by
      have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds (x := (1 : ℝ) / 4)).add hi
    apply hl.congr'
    filter_upwards [MonotoneHinge.eventually_right (by norm_num : (0 : ℝ) < 1 / 4)] with t ht
    exact (hroot t ht ω).symm

-- The Jacobian is not replaced by its null value when differentiating.
example (σ : ℝ) {v : ℝ} (hv : 0 < v) :
    deriv (fun s => weight s v) σ = -(v - σ / v) / (4 * v ^ 2) :=
  (weight_derivative σ hv.ne').deriv

-- Check the full product's second derivative at the critical fibre, including
-- the Jacobian derivatives and cross terms (not just `J * g''`).
theorem actual_product_second (ω : OverlapSphere) {v : ℝ} (hv : 0 < v) :
    MonotoneHinge.productD2 (twoFaceRayGap cap (fun _ => 0) 0 ω) weight 0 v =
      1 / (16 * v ^ 3) + 1 / (8 * v ^ 2) := by
  have he (s : ℝ) : twoFaceRayGap cap (fun _ => 0) 0 ω s v =
      1 / 4 - (v + s / v) / 2 := by
    norm_num [planar_gap, cap, ellipsoidProfile]
  have hg : ContDiffAt ℝ 3 (fun s => twoFaceRayGap cap (fun _ => 0) 0 ω s v) 0 := by
    simp_rw [he]
    exact contDiffAt_const.sub ((contDiffAt_const.add (contDiffAt_id.div_const v)).div_const 2)
  have hd (s : ℝ) : HasDerivAt (fun t => twoFaceRayGap cap (fun _ => 0) 0 ω t v)
      (-1 / (2 * v)) s := by
    simp_rw [he]
    convert ((((hasDerivAt_id s).div_const v).const_add v).div_const 2).const_sub (1 / 4) using 1
    ring
  have hd1 : (fun s => deriv (fun t => twoFaceRayGap cap (fun _ => 0) 0 ω t v) s) =
      (fun _ => -1 / (2 * v)) := funext (fun s => (hd s).deriv)
  rw [productD2_formula hv.ne' hg, he, (hd 0).deriv, hd1]
  simp only [deriv_const, mul_zero, add_zero, zero_div, sub_zero, weight]
  field_simp
  ring

-- The public result elaborates with the unchanged literal Jacobian.
example {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ε c A M B : ℝ, δ < V ∧ 0 < ε ∧ 0 < c ∧ 0 ≤ A ∧ 0 ≤ M ∧ 0 ≤ B ∧
      ∀ (x : Spatial) (ω : OverlapSphere),
        MonotoneHinge.Hypotheses (twoFaceRayGap h f x ω)
          (fun σ v => (v - σ / v) ^ 2 / (8 * v)) δ V ε c A M B :=
  exists_hypotheses hf hδ

end TwoFaceLongGeometryRegression
