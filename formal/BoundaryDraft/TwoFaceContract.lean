import BoundaryDraft.GraphSurface
import BoundaryDraft.ExpectationBridge

/-!
# An open two-spacelike-face contract

A deliberately restricted global two-graph class: the thickness retains the
unchanged `AdmissibleGraphCap` API; an independently chosen future graph uses
part of the remaining strict Lipschitz budget. Smooth germs `f - h, f` are
separate from causal envelopes `f - max 0 h, f`. No analytic conclusion is a
field. All `Goal` declarations below are proposition definitions, not proofs.
`TwoFaceGeometry` supplies the separate proof of `TwoFaceRegionGoal`; the area
and asymptotic goals remain open here.

The area candidate is defined independently by the Lorentzian Gram density
on the projected joint. Its identification with intrinsic joint area, and its
transport/normalization, belong to work package C (#51).
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace BoundaryDraft

/-- Sufficient coordinate geometry, not the class of all two-face regions.
The height may have positive-height critical points and arbitrary irrelevant
exterior behavior. The extra global Lipschitz bound is on the future envelope. -/
structure AdmissibleTwoFace (h f : Spatial → ℝ) : Prop extends AdmissibleGraphCap h where
  smooth_future : ∀ x ∈ graphClosedPositive h,
    ContDiffAt ℝ 3 (fun y : JointSpace => f y) x
  slope_budget : ∃ κ η : ℝ, 0 ≤ κ ∧ 0 ≤ η ∧ κ + η < 1 ∧
    (∀ x y : Spatial, |max 0 (h x) - max 0 (h y)| ≤ κ * spatialDistance x y) ∧
    (∀ x y : Spatial, |f x - f y| ≤ η * spatialDistance x y)

/-- The actual open region to be sprinkled, not a transformed action. -/
def twoFaceRegion (h f : Spatial → ℝ) : Set Spacetime :=
  {p | f (spatialPart p) - h (spatialPart p) < p 0 ∧ p 0 < f (spatialPart p)}

/-- The graph embedding used for the future face and the joint. -/
def twoFaceLift (f : Spatial → ℝ) (x : JointSpace) : Spacetime := Fin.cons (f x) x

/-- Closed faces; their only common stratum is intended to be the joint. -/
def twoFacePast (h f : Spatial → ℝ) : Set Spacetime :=
  twoFaceLift (fun x => f x - h x) '' graphClosedPositive h

def twoFaceFuture (h f : Spatial → ℝ) : Set Spacetime :=
  twoFaceLift f '' graphClosedPositive h

def twoFaceJoint (h f : Spatial → ℝ) : Set Spacetime :=
  twoFaceLift f '' graphJoint h

/-- Both normals are future directed, including the past face's INWARD normal.
`minkowskiInner` uses signature (+---), opposite to the paper's (-+++). -/
def twoFaceNormal (f : Spatial → ℝ) (x : JointSpace) : Spacetime :=
  (Real.sqrt (1 - ‖graphGradient f x‖ ^ 2))⁻¹ •
    (Fin.cons 1 (graphGradient f x) : Spacetime)

/-- Intended to equal cosh of the positive angle; strictness is a goal below,
not an assumption or a consequence of Lean's total square root/division. -/
def twoFaceCosh (h f : Spatial → ℝ) (x : JointSpace) : ℝ :=
  minkowskiInner (twoFaceNormal (fun y => f y - h y) x) (twoFaceNormal f x)

def twoFaceWeight (h f : Spatial → ℝ) (x : JointSpace) : ℝ :=
  twoFaceCosh h f x / Real.sqrt (twoFaceCosh h f x ^ 2 - 1)

/-- Project the future gradient onto ker dh using the actual unit normal.
This is used only on the regular joint in the proposed geometric meaning. -/
def twoFaceTangentialGradient (h f : Spatial → ℝ) (x : JointSpace) : JointSpace :=
  graphGradient f x -
    inner (𝕜 := ℝ) (graphGradient f x) (graphInward h x) • graphInward h x

/-- sqrt(det(I - a aᵀ)), NOT the ambient Euclidean graph factor sqrt(1+|a|²). -/
def twoFaceAreaDensity (h f : Spatial → ℝ) (x : JointSpace) : ℝ :=
  Real.sqrt (1 - ‖twoFaceTangentialGradient h f x‖ ^ 2)

/-- Coordinate candidate for induced Lorentzian area, with the existing π/4
Hausdorff normalization on the spatial joint. No action enters this definition. -/
def twoFaceProjectedArea (h f : Spatial → ℝ) : Measure JointSpace :=
  (graphSurfaceMeasure h).withDensity (fun x => ENNReal.ofReal (twoFaceAreaDensity h f x))

/-- The same candidate pushed to the actual spacetime joint. Work package C
must prove its intrinsic chart meaning and covariance; these are not fields. -/
def twoFaceJointArea (h f : Spatial → ℝ) : Measure Spacetime :=
  Measure.map (twoFaceLift f) (twoFaceProjectedArea h f)

def twoFaceBoundaryIntegral (h f : Spatial → ℝ) : ℝ :=
  ∫ x, twoFaceWeight h f x ∂twoFaceProjectedArea h f

/-- Exact constructor/stratum contract, proved separately in `TwoFaceGeometry`.
Ambient causal convexity is NOT replaced by intrinsic global hyperbolicity. -/
def TwoFaceRegionGoal : Prop :=
  ∀ h f, AdmissibleTwoFace h f →
    IsOpen (twoFaceRegion h f) ∧ BoundedCausalRegion (twoFaceRegion h f) ∧
    IsCompact (twoFacePast h f) ∧ IsCompact (twoFaceFuture h f) ∧
    IsCompact (twoFaceJoint h f) ∧
    frontier (twoFaceRegion h f) = twoFacePast h f ∪ twoFaceFuture h f ∧
    twoFacePast h f ∩ twoFaceFuture h f = twoFaceJoint h f

/-- Finiteness and nondegeneracy are geometric goals, not admissibility fields.
This does not replace #51's intrinsic-area and transport obligations. -/
def TwoFaceAreaGoal : Prop :=
  ∀ h f, AdmissibleTwoFace h f →
    (∀ x ∈ graphJoint h, 1 < twoFaceCosh h f x ∧ 0 < twoFaceAreaDensity h f x) ∧
    IsFiniteMeasure (twoFaceProjectedArea h f) ∧
    Integrable (twoFaceWeight h f) (twoFaceProjectedArea h f)

/-- Recovery of the original target is itself an explicit geometric goal. -/
def TwoFacePlanarTargetGoal : Prop :=
  ∀ h, AdmissibleGraphCap h →
    twoFaceProjectedArea h (fun _ => 0) = graphSurfaceMeasure h ∧
    twoFaceBoundaryIntegral h (fun _ => 0) = graphBoundaryIntegral h

/-- OPEN deterministic asymptotic contract at fixed geometry. -/
def TwoFaceLimitGoal : Prop :=
  ∀ h f, AdmissibleTwoFace h f →
    Tendsto (fun ρ => continuumMean ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f))

/-- OPEN expectation-only contract for the unchanged unsmeared discrete action.
No assertion is made about individual sprinklings or rates. -/
def TwoFaceExpectedLimitGoal : Prop :=
  ∀ h f, AdmissibleTwoFace h f →
    Tendsto (fun ρ => expectedBDGAction ρ (twoFaceRegion h f)) atTop
      (𝓝 (twoFaceBoundaryIntegral h f))

/-- No stronger hypothesis is imposed on ANY old admissible cap. -/
theorem AdmissibleGraphCap.twoFace_planar {h : Spatial → ℝ} (hh : AdmissibleGraphCap h) :
    AdmissibleTwoFace h (fun _ => 0) := by
  refine { hh with smooth_future := fun _ _ => contDiffAt_const, slope_budget := ?_ }
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hh.lipschitz_positivePart
  exact ⟨κ, 0, hκ, le_rfl, by simpa using hκ1, hLip, by simp⟩

@[simp] theorem twoFaceRegion_planar (h : Spatial → ℝ) :
    twoFaceRegion h (fun _ => 0) = graphCapRegion h := by
  ext p
  simp [twoFaceRegion, graphCapRegion]

/-- Raw face germs need not be globally Lipschitz. The causal envelopes give
exactly the same region, even when the raw height is negative outside. -/
theorem twoFaceRegion_eq_envelopes (h f : Spatial → ℝ) :
    twoFaceRegion h f =
      {p | f (spatialPart p) - max 0 (h (spatialPart p)) < p 0 ∧
        p 0 < f (spatialPart p)} := by
  ext p
  by_cases hp : 0 < h (spatialPart p)
  · simp [twoFaceRegion, max_eq_right hp.le]
  · have hn := le_of_not_gt hp
    simp only [twoFaceRegion, mem_setOf_eq, max_eq_left hn, sub_zero]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Reuse, rather than reconstruct, the proved four-dimensional bridge.
This conditional implication proves neither of its two open input goals. -/
theorem twoFace_expectedLimit_of_region_and_limit
    (hregion : TwoFaceRegionGoal) (hlimit : TwoFaceLimitGoal) :
    TwoFaceExpectedLimitGoal := by
  intro h f hf
  apply (hlimit h f hf).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact ((hregion h f hf).2.1.expectedBDGAction_eq hρ).symm

end BoundaryDraft
