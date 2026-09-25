import BoundaryDraft

/-!
Independent contracts for the controlled atlas and both measure transports.
The overlap regression refines a whole atlas by duplicating every chart with
half its weight. Both copies are active on a nonempty open overlap, while
both finite-sum formulas remain unchanged. It does not assume disjoint charts,
a multiplicity bound or discarded seams. Coarea is now also exercised on the
refinement; height-density continuity is neither assumed nor asserted.
-/

open BoundaryDraft MeasureTheory Set
open scoped Topology ENNReal Manifold
noncomputable section

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) (x : JointSpace)
    (hx : x ∈ graphClosedPositive h)
    (hr : fderiv ℝ (fun y : JointSpace => h y) x ≠ 0) :
    ∃ c : SliceHeightChart h, x ∈ c.chart.source ∧ c.center = c.chart x :=
  hh.exists_sliceHeightChart x hx hr

example (h : Spatial → ℝ) (c : SliceHeightChart h) (t : ℝ) (ht : 0 ≤ t)
    (s : Set SurfacePlane) (hs : MeasurableSet s) (hsc : s ⊆ c.sliceDomain t) :
    (graphLevelMeasure h t).restrict (c.slice t '' s) =
      Measure.map (c.slice t) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (c.sliceJacobian (surfaceGraph (fun _ => t) u)))) :=
  c.graphLevelMeasure_slice_image t ht s hs hsc

example (h : Spatial → ℝ) (A : ControlledCollarAtlas h) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, IntegrableOn (fun _ : SurfacePlane => M) (A.charts i).disk ∧
      ∀ t ∈ Icc 0 A.width, ∀ u ∈ (A.charts i).disk, ‖A.localTerm i t u‖ ≤ M :=
  A.exists_uniform_integrable_dominator

example (h : Spatial → ℝ) (hh : AdmissibleGraphCap h) : Nonempty (ControlledCollarAtlas h) :=
  hh.exists_controlledCollarAtlas

-- Original unequal-axis hypotheses suffice; no parametric ellipsoid measure
-- is substituted for the canonical graph-level measure.
example (a : ℝ) (b : Fin 3 → ℝ) (ha : 0 < a) (hb : ∀ i, 2 * a < b i) :
    Nonempty (ControlledCollarAtlas (ellipsoidProfile a b)) :=
  (ellipsoid_admissible a b ha hb).exists_controlledCollarAtlas

namespace GraphAtlasRegression

private theorem sum_half_copies (n : ℕ) (f : Fin n → ℝ) :
    (∑ j : Fin (2 * n), (1 / 2 : ℝ) * f (finProdFinEquiv.symm j).2) = ∑ i, f i := by
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin n ≃ Fin (2 * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [← Finset.mul_sum]
  ring

/-- Deliberate overlapping refinement of a complete finite atlas. The two
copies of every chart each receive half its smooth partition weight. -/
def overlappingAtlas {h : Spatial → ℝ} (A : ControlledCollarAtlas h) : ControlledCollarAtlas h := by
  let π : Fin (2 * A.count) → Fin A.count := fun j => (finProdFinEquiv.symm j).2
  let w : SmoothPartitionOfUnity (Fin (2 * A.count)) 𝓘(ℝ, JointSpace) JointSpace
      (graphClosedCollar h A.width) :=
    { toFun := fun j => ⟨fun x => (1 / 2 : ℝ) * A.weights (π j) x,
        contMDiff_const.mul (A.weights (π j)).contMDiff⟩
      locallyFinite' := locallyFinite_of_finite _
      nonneg' := fun j x => mul_nonneg (by norm_num) (A.weights.nonneg (π j) x)
      sum_eq_one' := fun x hx => by
        rw [finsum_eq_sum_of_fintype]
        change (∑ j : Fin (2 * A.count), (1 / 2 : ℝ) *
          A.weights (finProdFinEquiv.symm j).2 x) = 1
        rw [sum_half_copies A.count (fun i => A.weights i x)]
        exact A.sum_weights x hx
      sum_le_one' := fun x => by
        rw [finsum_eq_sum_of_fintype]
        change (∑ j : Fin (2 * A.count), (1 / 2 : ℝ) *
          A.weights (finProdFinEquiv.symm j).2 x) ≤ 1
        rw [sum_half_copies A.count (fun i => A.weights i x), ← finsum_eq_sum_of_fintype]
        exact A.weights.sum_le_one x }
  exact {
    width := A.width
    width_pos := A.width_pos
    count := 2 * A.count
    charts := fun j => A.charts (π j)
    width_lt := fun j => A.width_lt (π j)
    noncritical := A.noncritical
    covers := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (A.covers hx)
      refine mem_iUnion.mpr ⟨finProdFinEquiv (0, i), ?_⟩
      simpa only [π, Equiv.symm_apply_apply] using hi
    weights := w
    subordinate := fun j => (tsupport_mul_subset_right).trans (A.subordinate (π j)) }

/-- The overlap is active, nonempty, and has positive ambient volume; it is
not a null seam. The sum is nevertheless one rather than two. -/
theorem active_overlap {h : Spatial → ℝ} (A : ControlledCollarAtlas h)
    (x : JointSpace) (hx : x ∈ graphClosedCollar h A.width) :
    ∃ j k : Fin (overlappingAtlas A).count, j ≠ k ∧
      0 < (overlappingAtlas A).weights j x ∧ 0 < (overlappingAtlas A).weights k x ∧
      0 < volume (((overlappingAtlas A).charts j).patch ∩
        ((overlappingAtlas A).charts k).patch) ∧
      (∑ i, (overlappingAtlas A).weights i x) = 1 := by
  obtain ⟨i, hi⟩ := A.weights.exists_pos_of_mem hx
  let j : Fin (2 * A.count) := finProdFinEquiv (0, i)
  let k : Fin (2 * A.count) := finProdFinEquiv (1, i)
  have hj : (overlappingAtlas A).weights j x = (1 / 2 : ℝ) * A.weights i x := by
    change (1 / 2 : ℝ) * A.weights (finProdFinEquiv.symm (finProdFinEquiv (0, i))).2 x = _
    rw [Equiv.symm_apply_apply]
  have hk : (overlappingAtlas A).weights k x = (1 / 2 : ℝ) * A.weights i x := by
    change (1 / 2 : ℝ) * A.weights (finProdFinEquiv.symm (finProdFinEquiv (1, i))).2 x = _
    rw [Equiv.symm_apply_apply]
  refine ⟨j, k, ?_, by rw [hj]; positivity, by rw [hk]; positivity, ?_,
    (overlappingAtlas A).sum_weights x hx⟩
  · intro he
    have hp := finProdFinEquiv.injective he
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst hp
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  · apply (((overlappingAtlas A).charts j).isOpen_patch.inter
      ((overlappingAtlas A).charts k).isOpen_patch).measure_pos volume
    have hmem := A.subordinate i (subset_tsupport _ hi.ne')
    refine ⟨x, ?_, ?_⟩
    · change x ∈ (A.charts (finProdFinEquiv.symm (finProdFinEquiv (0, i))).2).patch
      simpa only [Equiv.symm_apply_apply] using hmem
    · change x ∈ (A.charts (finProdFinEquiv.symm (finProdFinEquiv (1, i))).2).patch
      simpa only [Equiv.symm_apply_apply] using hmem

/-- The real canonical-density formula is exercised on the overlapping
refinement, not on a single global parameterization. -/
theorem overlapping_density {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (A : ControlledCollarAtlas h) (t : ℝ) (ht : t ∈ Icc 0 A.width) :
    graphHeightDensity h t =
      ∑ i, ∫ u in ((overlappingAtlas A).charts i).disk, (overlappingAtlas A).localTerm i t u :=
  (overlappingAtlas A).graphHeightDensity_eq_sum hh t ht

/-- The same overlap test exercises the ambient representation independently
of any height Fubini step or final coarea theorem. -/
theorem overlapping_volume {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (A : ControlledCollarAtlas h) (f : JointSpace → ℝ)
    (hf : IntegrableOn f (graphClosedCollar h A.width)) :
    (∫ x in graphClosedCollar h A.width, f x) =
      ∑ i, ∫ p in ((overlappingAtlas A).charts i).parameterRegion A.width,
        ((overlappingAtlas A).charts i).weightedJacobian ((overlappingAtlas A).weights i) p *
          f (((overlappingAtlas A).charts i).chart.symm p) :=
  (overlappingAtlas A).integral_closedCollar_eq_sum hh f hf

/-- Nonvacuous specialization: the unit-axis cap has a joint point, so its
constructed finite atlas really has an active positive-volume overlap after
refinement. -/
theorem ellipsoid_overlap_exists :
    ∃ A : ControlledCollarAtlas (ellipsoidProfile (1 / 4) (fun _ => 1)),
      ∃ x : JointSpace, ∃ j k : Fin A.count, j ≠ k ∧
        0 < A.weights j x ∧ 0 < A.weights k x ∧
        0 < volume ((A.charts j).patch ∩ (A.charts k).patch) ∧
        (∑ i, A.weights i x) = 1 := by
  let h := ellipsoidProfile (1 / 4) (fun _ : Fin 3 => 1)
  have hh : AdmissibleGraphCap h := ellipsoid_admissible _ _ (by norm_num) (fun _ => by norm_num)
  let x : JointSpace := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hx0 : h x = 0 := by
    norm_num [h, x, ellipsoidProfile, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply, Fin.sum_univ_succ]
  have hx : x ∈ graphClosedPositive h := by
    have hu : Filter.Tendsto (fun t : ℝ => t • x) (𝓝[<] 1) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
      simpa only [one_smul] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hu
    have hlt : ∀ᶠ t : ℝ in 𝓝[<] 1, t < 1 := self_mem_nhdsWithin
    filter_upwards [hlt, nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht0
    change 0 < h (t • x)
    have he : h (t • x) = (1 / 4 : ℝ) * (1 - t ^ 2) := by
      norm_num [h, x, ellipsoidProfile, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single_apply, Fin.sum_univ_succ]
    rw [he]
    nlinarith
  obtain ⟨A⟩ := hh.exists_controlledCollarAtlas
  exact ⟨overlappingAtlas A, x, active_overlap A x ⟨hx, hx0.le.trans A.width_pos.le⟩⟩

/-- Global coarea is invariant under the genuinely overlapping refinement;
the canonical density is not multiplied by the number of active charts. -/
theorem overlapping_coarea {h : Spatial → ℝ} (hh : AdmissibleGraphCap h)
    (A : ControlledCollarAtlas h) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 A.width)) :
    (∫ x : Spatial in {x | 0 < h x ∧ h x < (overlappingAtlas A).width}, f (h x)) =
      ∫ t in (0 : ℝ)..A.width, f t * graphHeightDensity h t :=
  (overlappingAtlas A).integral_openCollar_profile hh f hf

end GraphAtlasRegression
