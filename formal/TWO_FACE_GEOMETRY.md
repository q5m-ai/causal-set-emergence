# Two-face region geometry and exact action compatibility (#60)

**Status:** checked geometry and finite-density identities for every unchanged
`AdmissibleTwoFace h f`. The original `TwoFaceRegionGoal` now has the proof term
`twoFaceRegionGoal`. This is an integration prerequisite, not a two-face limit
or an overlap Taylor theorem. The separate [joint-geometry proof](JOINT_GEOMETRY.md)
now supplies induced joint area, angle, and transport results.

The [two-face contract](../notes/two-face-contract.md) retains the original
`AdmissibleGraphCap h`, local C³ face germs, and combined Euclidean Lipschitz
budget. No structure field or mathematical definition has changed. In
particular, the independently defined region, action, Poisson law, overlap,
long-displacement density, and geometric target are all unchanged.

## Geometry proof

`BoundaryDraft/TwoFaceGeometry.lean` proves reusable per-region lemmas.

1. **Causal envelopes.** The existing `twoFaceRegion_eq_envelopes` is exactly
   `twoFaceRegion_eq_twoGraphRegion`. The upper envelope is `f`; the lower is
   `fun x => f x - max 0 (h x)`. The triangle inequality bounds its Euclidean
   Lipschitz constant by the sum of the two budget components, strictly below
   one. `strictGraphLipschitz_lower` and `strictGraphLipschitz_upper` instantiate
   the existing `StrictGraphLipschitz` API. Neither the raw height nor the raw
   past-face germ is assumed globally smooth or globally Lipschitz.
2. **Openness and ambient causal convexity.** Continuous envelopes give two
   open strict inequalities. `StrictGraphLipschitz.epigraph_future` compares
   graph variation with the time separation of an arbitrary ambient causal
   pair; `hypograph_past` gives the dual result. Their intersection contains
   every closed ambient causal interval with endpoints inside it. Null pairs
   and vertices are retained. Intrinsic global hyperbolicity is not used.
3. **Closure and boundedness.** A continuous filling, using only the envelopes,
   sends the closed positive spatial region times the closed unit interval
   into spacetime. Its value, in Lean coordinates, is:

   ```lean
   Fin.cons (f x - (1 - u) * max 0 (h x)) x
   ```

   The image of the positive spatial region times the open unit interval is
   exactly the original open region. That product is dense in the closed
   product. Continuity gives one closure inclusion; compactness of the closed
   product makes its image closed and gives the other. This proves compactness
   of the actual closure and hence boundedness, also for an empty positive set.
   Nonnegativity of the raw height on its closed positive set identifies the
   closed fibres, including zero-height fibres:

   ```lean
   theorem AdmissibleTwoFace.mem_closure_region
       {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f) (p : Spacetime) :
       p ∈ closure (twoFaceRegion h f) ↔
         (WithLp.equiv 2 _).symm (spatialPart p) ∈ graphClosedPositive h ∧
         f (spatialPart p) - h (spatialPart p) ≤ p 0 ∧
         p 0 ≤ f (spatialPart p)
   ```

4. **Complete strata.** Subtracting the open region from this closure leaves
   exactly the two endpoint graphs. Their intersection forces height zero
   inside the closed positive set, exactly `graphJoint h`, not the whole raw
   zero set. Continuous graph embeddings of the existing compact spatial
   sets give compactness of the past face, future face and joint. Thus no
   unrecorded lateral boundary or irrelevant exterior zero is inserted.
5. **Constructor.** `AdmissibleTwoFace.boundedCausalRegion` combines the derived
   measurability, boundedness and ambient causal convexity. `twoFaceRegionGoal`
   assembles this constructor and the compactness/frontier/intersection facts
   into the original proposition without adding a premise.

This module proves the topological/compact stratum statements. Intrinsic area,
normal/angle identities and covering-chart interpretation are proved separately
in the [joint-geometry modules](JOINT_GEOMETRY.md), not inferred from this proof.

## Exact overlap and expectation

`BoundaryDraft/TwoFaceOverlap.lean` specializes the existing APIs rather than
constructing substitute densities or probability measures.

```lean
theorem AdmissibleTwoFace.translatedOverlap_causal
    {h f : Spatial → ℝ} (hf : AdmissibleTwoFace h f)
    {s : ℝ} {a : Spatial} (hz : Fin.cons s a ∈ causalFuture 0) :
    translatedOverlap (twoFaceRegion h f) (Fin.cons s a) =
      ∫ x : Spatial, max 0 (f (x + a) - s - (f x - max 0 (h x)))
```

This is `translatedOverlap_twoGraph_causal` applied to the envelopes. It
includes the vertex and macroscopic null displacements. The inherited proofs
supply overlap measurability, its nonnegative volume bound, compact support,
and absolute integrability after every continuous displacement weight.

`continuumMean_eq_overlap` specializes the exact signed reduction.
`continuumMean_eq_graphOverlap` inserts the spatial formula into the original
future-cone integral. Both keep the full `bdgKernel` and both density factors.
At each positive density, `expectedBDGAction_eq` uses the already proved
`BoundedCausalRegion.expectedBDGAction_eq`; `integrable_discreteBDGAction`
concerns the actual observable under the original finite Poisson law.
`expectedBDGAction_eq_overlap` and `expectedBDGAction_eq_graphOverlap` expose
the same exact expressions for that expectation. No expectation identity is
assumed and no probability law is reconstructed.

For every fixed positive cutoff, the actual
`longOverlapDensity (twoFaceRegion h f)` is measurable, uniformly bounded,
compactly supported and absolutely integrable; its nonnegative version is
finite at every proper-time square. The specialized `map_longOverlapMeasure`
retains the independently defined geometric measure and its pushforward.
`integrable_longOverlapDensity_weight`, `integral_longOverlap`, and
`integral_longOverlap_bdg` reuse the continuous signed-weight and full-kernel
identities from [the exact overlap API](TRANSLATED_OVERLAP.md).

`twoFace_expectedLimit_of_limit` now removes the discharged region-goal
premise from the older conditional implication. **The deterministic two-face
limit remains an explicit, unproved input.** This is not a new limit theorem.

## Independent regressions and validation

`TwoFaceGeometryRegression.lean` restates the original region contract and
checks ambient causal containment, closure, the envelope API, a concrete
macroscopic null displacement, the vertex, the actual Poisson expectation,
and the fixed-positive-cutoff signed density identity. It covers:

- every original planar cap, recovering its existing finite-density reduction;
- the contract's nonempty sine/ellipsoid example, with genuine future-face
  curvature inside its face domain;
- the damped quartic with its independently checked positive-height critical
  point, also with a curved future graph; and
- an admissible empty region, empty faces and joint, zero expected action and
  zero density, despite an everywhere-zero raw height.

`TwoFaceExteriorRegression.lean` constructs a nonempty admissible example
whose raw height is the original unit ellipsoid profile for first coordinate
less than two and zero otherwise. Its entire exterior zero half-space is
excluded from both the closure and joint. The positive part is unchanged,
and the original smooth/regular germs hold near the closed positive region;
the jump in the raw exterior height is immaterial. A curved future graph and
the exact expectation bridge still apply. Existing regressions are retained.

Run `bash formal/check.sh` for the integrated library build, warnings-as-errors
checks of every local Lean source, isolated transitive axiom audits and the
aggregate audit. Only the standard `propext`, `Classical.choice`, and
`Quot.sound` foundations are permitted. Also run the repository Python tests,
symbolic checks, numerical reproduction, and Markdown validation. GitHub CI
checks do not replace this local Lean audit.

## Remaining obligations

Joint area, positive angle identities, angle-weight integrability, planar
target identification and joint-measure transport are separately proved in
#51, not consequences of the region/overlap theorem. Geometric long-null
regularity and connection to the conditional cancellation theorem remain #61. Translated-boundary tangencies, wedge asymptotics, curved-face error
bounds and globalization remain research gates in the
[localization plan](../notes/flat-localization-plan.md). No two-face boundary
limit, convergence rate, variance bound or sample-wise convergence follows
from these finite-density identities.
