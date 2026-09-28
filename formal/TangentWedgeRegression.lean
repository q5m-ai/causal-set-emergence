import BoundaryDraft.TangentWedge
import BoundaryDraft.JointTransport

/-! Independent contracts: the first endpoint is weighted but the second is
not restricted to the source patch. These are not curved-face limit tests. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
open BoundaryDraft

example (ρ : ℝ) (M : Set Spacetime) :
    weightedContinuumMean ρ M (fun _ => 1) = continuumMean ρ M :=
  weightedContinuumMean_one ρ M

example (h : Spatial → ℝ) (hh : GraphCapData h) (a : Spatial → ℝ)
    (ha : Continuous a) (ρ : ℝ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ x in graphCapRegion h, a (spatialPart x)) - ρ *
        ∫ x in graphCapRegion h, a (spatialPart x) *
          ∫ y in graphCapRegion h ∩ causalFuture x,
            bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) =
      ∫ x in {x | 0 < h x}, a x * planeKernel ρ (h x) :=
  weighted_graphCap_reduction h hh a ha ρ

example {k H R : ℝ} (hk : 0 < k) (hk1 : k < 1) (hH : 2 * k * R ≤ H)
    (a : Spatial → ℝ) (ha : Continuous a) (hs : ∀ x, R < ‖x‖ → a x = 0) :
    Tendsto (fun ρ => weightedContinuumMean ρ
      (graphCapRegion (wedgeRegulatorProfile k H)) (fun p => a (spatialPart p)))
      atTop (𝓝 ((Real.cosh (jointRapidity k) / Real.sinh (jointRapidity k)) *
        ∫ z : Fin 2 → ℝ, a (Fin.cons 0 z))) :=
  weighted_wedgeRegulator_limit hk hk1 hH a ha hs

-- A genuine bounded regulator and a nonzero signed compact test weight.
private def testWeight (x : Spatial) : ℝ := -max 0 (1 - ‖x‖)
private theorem testWeight_continuous : Continuous testWeight := by
  unfold testWeight
  fun_prop
private theorem testWeight_support (x : Spatial) (hx : 1 < ‖x‖) : testWeight x = 0 := by
  simp [testWeight, max_eq_left (by linarith : 1 - ‖x‖ ≤ 0)]

example : testWeight 0 = -1 := by simp [testWeight]
example : ![-(1/8 : ℝ), 1/2, 0, 0] ∈ graphCapRegion (wedgeRegulatorProfile (1/2) 2) := by
  have hn : ‖spatialPart ![-(1/8 : ℝ), 1/2, 0, 0]‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    fin_cases i <;> norm_num [spatialPart, Fin.cons]
    change |(0 : ℝ)| ≤ 1
    norm_num
  norm_num [graphCapRegion, wedgeRegulatorProfile, spatialPart]
  linarith

example : Tendsto (fun ρ => weightedContinuumMean ρ
    (graphCapRegion (wedgeRegulatorProfile (1/2) 2)) (fun p => testWeight (spatialPart p)))
    atTop (𝓝 (2 * ∫ z : Fin 2 → ℝ, testWeight (Fin.cons 0 z))) := by
  have h := weighted_wedgeRegulator_limit (k := 1/2) (H := 2) (R := 1)
    (by norm_num) (by norm_num) (by norm_num) testWeight testWeight_continuous testWeight_support
  have hc := (jointRapidity_identities (1/2) (by norm_num) (by norm_num)).2.2.2.2
  norm_num at hc
  simpa only [hc] using h

-- Every causal partner remains, even when the source weight has ended.
example (ρ : ℝ) (x : Spacetime)
    (hx : x ∈ graphCapRegion (wedgeRegulatorProfile (1/2) 2)) :
    (∫ y in graphCapRegion (wedgeRegulatorProfile (1/2) 2) ∩ causalFuture x,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq x y ^ 2)) = coneIntegral ρ (-x 0) :=
  graphCap_future_integral _ (wedgeRegulator_data (by norm_num) (by norm_num) 2) ρ x hx

example (F : PoincareEquiv) (ρ : ℝ) (M : Set Spacetime) (w : Spacetime → ℝ) :
    weightedContinuumMean ρ (F '' M) (fun x => w (F.symm x)) = weightedContinuumMean ρ M w :=
  F.weightedContinuumMean_image ρ M w

example (M : Set Spacetime) (w : Spacetime → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    weightedContinuumMean ρ (dilateRegion 2 M) (fun x => w ((2 : ℝ)⁻¹ • x)) =
      4 * weightedContinuumMean (16 * ρ) M w := by
  have ht := weightedContinuumMean_dilate (s := 2) (by norm_num) hρ M w
  norm_num at ht ⊢
  simpa [mul_comm] using ht
