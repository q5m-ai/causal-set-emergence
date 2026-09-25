import BoundaryDraft.GraphDensity
import BoundaryDraft.GraphJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Neighborhood regularity of height charts

The implicit-function chart used for local surface finiteness initially gives
only a strict derivative at its center. Here the inverse-function theorem
upgrades the same chart to C³ on an open neighborhood, on both sides.
This is local preparatory data, not a collar atlas or a measure transport law.
-/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft
/-- Split Euclidean coordinates without identifying the Euclidean norm with
any product supremum norm. This is only a continuous linear equivalence. -/
def jointHeightCoordinates : JointSpace ≃L[ℝ] ℝ × SurfacePlane :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => (y 0, surfaceGraphBase y)
      invFun := fun p => surfaceGraph (fun _ => p.1) p.2
      left_inv := by
        intro y
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      right_inv := by intro p; rfl
      map_add' := by intro y z; rfl
      map_smul' := by intro c y; rfl }

@[simp] theorem surfaceGraph_height_base (p : JointSpace) :
    surfaceGraph (fun _ => p 0) (surfaceGraphBase p) = p :=
  jointHeightCoordinates.symm_apply_apply p

/-- Geometric data only: a C³ diffeomorphism flattening height. Measure
transformation laws are derived from these fields, never stored as premises. -/
structure RegularHeightChart (h : Spatial → ℝ) where
  chart : PartialHomeomorph JointSpace JointSpace
  height : ∀ y, chart y 0 = h y
  contDiff : ContDiffOn ℝ 3 chart chart.source
  contDiff_symm : ContDiffOn ℝ 3 chart.symm chart.target
  contDiff_height : ContDiffOn ℝ 3 (fun y : JointSpace => h y) chart.source
  regular : ∀ y ∈ chart.source, fderiv ℝ (fun z : JointSpace => h z) y ≠ 0

namespace AdmissibleGraphCap

variable {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
include hh

/-- The existing implicit chart can be shrunk to a genuine C³ height chart.
Both regularity assertions hold throughout open domains, not just at the
base point. No assumption is made on critical points outside this chart. -/
theorem exists_contDiff_level_chart (x : JointSpace) (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    ∃ e : PartialHomeomorph JointSpace (ℝ × graphTangentSpace h x),
      x ∈ e.source ∧ e x = (h x, 0) ∧ (∀ y, (e y).1 = h y) ∧
      ContDiffOn ℝ 3 e e.source ∧ ContDiffOn ℝ 3 e.symm e.target ∧
      ContDiffOn ℝ 3 (fun y : JointSpace => h y) e.source ∧
      (∀ y ∈ e.source, fderiv ℝ (fun z : JointSpace => h z) y ≠ 0) ∧
      HasStrictFDerivAt (fun z => e.symm (h x, z)) (graphTangentSpace h x).subtypeL 0 := by
  let f := fun y : JointSpace => h y
  let L := fderiv ℝ f x
  have hd : HasStrictFDerivAt f L x :=
    (hh.smooth_near x hx).hasStrictFDerivAt (by norm_num)
  have hn : L.toLinearMap ≠ 0 := by
    intro he
    apply hr
    ext y
    exact LinearMap.congr_fun he y
  have hrange : LinearMap.range L = ⊤ := Module.Dual.range_eq_top_of_ne_zero hn
  let P := L.ker_closedComplemented_of_finiteDimensional_range
  let d := hd.implicitFunctionDataOfComplemented f L hrange P
  let e := d.toPartialHomeomorph
  have he : e = hd.implicitToPartialHomeomorph f L hrange := rfl
  have hsource : x ∈ e.source := hd.mem_implicitToPartialHomeomorph_source hrange
  have he0 : e x = (h x, 0) := hd.implicitToPartialHomeomorph_self hrange
  have hforward : ContDiffAt ℝ 3 e x := by
    change ContDiffAt ℝ 3 (fun y => (f y, Classical.choose P (y - x))) x
    exact (hh.smooth_near x hx).prodMk
      ((Classical.choose P).contDiff.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const))
  have hinverse : ContDiffAt ℝ 3 e.symm (e x) := by
    apply e.contDiffAt_symm (e.map_source hsource)
    · simpa only [e.left_inv hsource] using d.hasStrictFDerivAt.hasFDerivAt
    · simpa only [e.left_inv hsource] using hforward
  obtain ⟨W, hW, hxW, hsW⟩ := hinverse.contDiffOn' le_rfl (by simp)
  simp only [insert_eq_of_mem (mem_univ (e x)), univ_inter] at hsW
  obtain ⟨U, hU, hxU, hsU, hrU⟩ := hh.exists_regular_neighborhood x hx hr
  let e' := (e.restrOpen U hU).symm.restrOpen W hW
  refine ⟨e'.symm, ?_, he0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨hsource, hxU⟩, hxW⟩
  · intro y
    exact hd.implicitToPartialHomeomorph_fst hrange y
  · intro y hy
    change ContDiffWithinAt ℝ 3 (fun z => (f z, Classical.choose P (z - x))) _ y
    exact ((hsU.contDiffAt (hU.mem_nhds hy.1.2)).prodMk
      ((Classical.choose P).contDiff.contDiffAt.comp y
        (contDiffAt_id.sub (contDiffAt_const (c := x))))).contDiffWithinAt
  · exact hsW.mono inter_subset_right
  · exact hsU.mono (fun _ hy => hy.1.2)
  · exact fun y hy => hrU y hy.1.2
  · exact hd.to_implicitFunction hrange

/-- The C³ chart in fixed Euclidean coordinates. Its first coordinate is
exactly height; the remaining two coordinates identify the tangent kernel
with the Euclidean plane. This does not assert a surface-area law. -/
theorem exists_regularHeightChart (x : JointSpace) (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    ∃ c : RegularHeightChart h, x ∈ c.chart.source ∧
      c.chart x = surfaceGraph (fun _ => h x) 0 := by
  obtain ⟨e, hxE, he0, heh, hs, ht, hf, hreg, _⟩ :=
    hh.exists_contDiff_level_chart x hx hr
  have hdim : Module.finrank ℝ (graphTangentSpace h x) = 2 := by
    have hn : (fderiv ℝ (fun y : JointSpace => h y) x).toLinearMap ≠ 0 := by
      intro he
      apply hr
      ext y
      exact LinearMap.congr_fun he y
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    have he : Module.finrank ℝ JointSpace = 3 := by simp [JointSpace]
    rw [he] at hd
    change Module.finrank ℝ (graphTangentSpace h x) + 1 = 3 at hd
    omega
  let k : graphTangentSpace h x ≃L[ℝ] SurfacePlane :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  let a : (ℝ × graphTangentSpace h x) ≃L[ℝ] JointSpace :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prod k).trans
      jointHeightCoordinates.symm
  let E := e.trans a.toHomeomorph.toPartialHomeomorph
  have hsource : E.source = e.source := by simp [E]
  have htarget : E.target = a.symm ⁻¹' e.target := by simp [E]
  let hc : RegularHeightChart h :=
    { chart := E
      height := fun y => heh y
      contDiff := by
        rw [hsource]
        exact a.contDiff.comp_contDiffOn hs
      contDiff_symm := by
        rw [htarget]
        exact ht.comp a.symm.contDiff.contDiffOn (fun _ hy => hy)
      contDiff_height := by rw [hsource]; exact hf
      regular := by rw [hsource]; exact hreg }
  refine ⟨hc, ?_, ?_⟩
  · change x ∈ E.source
    rwa [hsource]
  · change a (e x) = _
    rw [he0]
    change surfaceGraph (fun _ => h x) (k 0) = _
    rw [map_zero]

end AdmissibleGraphCap
end BoundaryDraft
