# Compact-manifold measured-order foundation (#137)

This package proves the **finite-density** BDG bridge for the actual cubic
flat-torus and round-unit-sphere–circle slabs selected in
[#133's gate](../notes/general-metric-atlas-gate.md). It does not prove an action
limit, curvature identity, focusing estimate, or sample-wise convergence.
Existing coordinate, conformal and dimension-indexed contracts are unchanged.

## Shared ownership and source audit

The integration ancestor is
`df7ef277ae8dc695396e359780ffd7be65b43e9a` on
`origin/issue-81-general-coverage`. The task branch is
`issue-137-compact-measured-order`; [PR #146](https://github.com/q5m-ai/causal-set-emergence/pull/146)
targets that integration branch, not main. The
[early signatures and ownership boundary](https://github.com/q5m-ai/causal-set-emergence/issues/137#issuecomment-6037366728)
were also published to #131/#132/#134 before implementation.

The coordinate-only `FiniteMeasureBDG` is not generalized by changing its
meaning. The source audit found that `MeasuredOrder`, `MeasuredOrderPoisson`,
`DimensionDiscrete` and `DimensionMeasureExpectation` already supply the
stronger arbitrary-measurable-order foundation. Their original
`FinitePoisson.law`, actual count probabilities, reduced two-point Mecke proof,
and first/second factorial-moment integrability are reused directly.

`MeasuredOrderBDG4.discreteAction` and `.action` are **abbreviations** of
`discreteDimensionAction O 4` and `dimensionFiniteMeasureAction O 4`.
There is no second action, new law, new coefficient family, or expectation
identity supplied as geometric input. The abstract proof requires less than
standard Borel structure; both concrete ambient spaces independently satisfy
`StandardBorelSpace`.

## Consumer API

[MeasuredOrderBDG4.lean](BoundaryDraft/MeasuredOrderBDG4.lean) specializes the
existing generic theorem. With a measurable point space, finite atomless
measure, and supplied measured partial order:

```lean
theorem MeasuredOrderBDG4.expectation_eq
    {X : Type*} [MeasurableSpace X] (O : MeasuredOrder X) (mu : Measure X)
    [IsFiniteMeasure mu] [NoAtoms mu] {rho : Real} (h : 0 < rho) :
  (∫ c, MeasuredOrderBDG4.discreteAction O rho c
    ∂FinitePoisson.law (ENNReal.ofReal rho • mu)) =
      MeasuredOrderBDG4.action O mu rho
```

The independently checked expanded contracts are:

- `discreteAction_eq`: original `bdgNormalization`, point cardinality, and
  signed layers with coefficients `-1, 9, -16, 8` at positive density.
- `action_eq`: original `bdgKernel`, actual exclusive interval measure,
  both endpoint measures, and original square-root normalization.
- `integral_action`: the intensity-measure formula before diagonal nullity;
  an atomic diagonal is still masked. The scaled geometric version has one
  intensity factor in the point term and two in the pair term.
- `measurable_intervalVolume`, `intervalVolume_bounds`, `measurable_kernel`,
  `measurable_discreteAction`, `integrable_kernel`, `integrable_discreteAction`.

Layers and finite-support order cardinalities remain the existing
`MeasuredOrder.layer`, `.layerPairs`, `.Point` and `.intervalCount` APIs.
The interval is the closed order interval minus exactly its two endpoints.
Null-related interior points remain; the reduced Mecke configuration does not
silently replace counts in the original configuration.

### Ultrastatic constructor

[SpatialDistance.lean](BoundaryDraft/SpatialDistance.lean) separates the actual
causal distance from the topology's presentation metric. Its fields are just
metric laws and continuity, with no action, measure, target or limit premise.
Its product constructor proves the Euclidean square-root-of-squares distance,
not the usual maximum product metric.

[UltrastaticMeasuredOrder.lean](BoundaryDraft/UltrastaticMeasuredOrder.lean)
constructs the order on `Real × X` from that spatial distance. It derives
transitivity, antisymmetry, closedness and the existing joint exclusive-interval
measurability. The main consumer names are:

```lean
Ultrastatic.measuredOrder
Ultrastatic.closedInterval
Ultrastatic.slab
Ultrastatic.slabVolume
Ultrastatic.interval_subset_slab
Ultrastatic.intervalVolume_ambient
Ultrastatic.isCompact_interval
Ultrastatic.isCompact_closure_slab
Ultrastatic.probability
Ultrastatic.ae_supported_layers
Ultrastatic.count_probability
Ultrastatic.expectation_eq
```

`slab T` contains every spatial point and the open time interval from `-T/2`
to `T/2`. `slabVolume nu T` is the restriction of Lebesgue time times spatial
geometric volume. Finiteness and atomlessness are proved, including when the
spatial measure itself is not assumed atomless. The law is still
`FinitePoisson.law (ENNReal.ofReal rho • slabVolume nu T)`.

`interval_subset_slab` proves **ambient closed interval containment** from
monotonicity of time for the actual order. It does not infer containment from
intrinsic global hyperbolicity. Only after containment is established does
`intervalVolume_ambient` identify restricted exclusive volume with ambient
closed-interval volume, using endpoint nullity. For compact spatial factors,
closed ambient intervals and the closure of the slab are compact.

## Concrete geometric instances

### Cubic flat torus

[CompactTorus.lean](BoundaryDraft/CompactTorus.lean) uses three actual
`AddCircle L` quotients, for positive circumference `L`. `distance_project`
computes the Euclidean distance from the three nearest integer lattice lifts;
`AddCircle.norm_eq` supplies the quotient minimum. There is no global choice
of a single chart and no maximum-norm substitution.

`quotientVolume` proves transport of ordinary product length on a fundamental
cube to `spatialVolume L`. Each circle has total **length** `L`, not total mass
one. `spatialVolume_univ` gives the cube of `L`; `slabVolume_univ` multiplies
it by slab width. Atomlessness and standard Borel/compactness facts are proved.

The consumer names are `CompactTorus.measuredOrder`, `.slab`, `.slabVolume`,
`.probability`, `.interval_subset_slab`, `.intervalVolume_ambient` and
`.expectation_eq`. In particular, they apply to the selected `L = 1`,
`T = 2/5` thin slab, whose mass is positive.

The finite-density bridge needs no thinness bound, since it uses **actual**
restricted intervals at every width. This does not assert the flat diamond
volume formula for thicker slabs. Injective interval lifting, quotient
integration of the deterministic pair kernel, and the thin-torus limit remain
separate downstream work in #138.

### Round unit sphere times a circle

[RoundSphereDistance.lean](BoundaryDraft/RoundSphereDistance.lean) uses the
actual unit sphere in Euclidean three-space. Its distance is the arccosine of
the unit-vector inner product. The triangle inequality is proved from the
orthogonal-component Cauchy–Schwarz bound. The pinned mathlib's
`proof_wanted angle_triangle` placeholder is **not used**. The usual sphere
Borel topology is retained, but ambient chord distance is not used for order.

[SphereCircle.lean](BoundaryDraft/SphereCircle.lean) takes the Euclidean product
of this angular distance and the shortest-circle distance. `sphereArea_eq_induced`
reuses `BoundaryDraft.normalizedHausdorffTwo_comap_sphere` from
`SphereSurface.lean`, identifying polar sphere
area with normalized induced Hausdorff area on every measurable set. The
spatial volume is this area times quotient circle length, not a supplied or
probability-normalized target measure. Its total is `4 * Real.pi * L`.

The parallel consumer names are `SphereCircle.measuredOrder`, `.slab`,
`.slabVolume`, `.probability`, `.interval_subset_slab`,
`.intervalVolume_ambient` and `.expectation_eq`. This implements the selected
sphere radius **one**, circumference **20**, width **4**, with slab mass
`320 * Real.pi`. Both antipodes and all coordinate seams are retained.
No unique-minimizer, no-cut-locus, or smooth interval-volume assumption is
needed for this foundation. This is not a Lean curvature calculation or a
proof of the focusing asymptotic from #133.

## Exact compatibility and regressions

[MeasuredOrderBDG4Compatibility.lean](BoundaryDraft/MeasuredOrderBDG4Compatibility.lean)
proves pointwise interval, count, layer and discrete-action recovery for the
original coordinate order, on **every multiset**, not only simple samples.
`coordinate_action` recovers `finiteMeasureAction` without requiring convexity
or finiteness. `flat_expectedAction`, `conformal_probability`,
`conformal_action`, `conformal_expectedAction` and `dimension_discreteAction`
recover the original observables/law and existing dimensional coordinate
transport. Old definitions and old theorem contracts are not edited.

The standalone [CompactMeasuredOrderRegression.lean](CompactMeasuredOrderRegression.lean)
independently checks:

- Both concrete standard Borel spaces, compact spatial factors, compact slab
  closures, finite atomless slab volumes, correct positive masses, and the
  restricted/ambient interval identification.
- Expanded finite-density expectation with the original kernel and actual
  restricted intervals; density-parameter measurability and signed-action
  integrability; actual Poisson cardinality probabilities, positive probability
  of a one-point sample, and both factorial moments with the density factors.
- A genuine null three-chain inside the thin torus slab: two links, one
  one-point interval, and discrete action `10 * bdgNormalization rho`.
- Exactly one ordered link, reverse-pair rejection, endpoint insertion
  invariance, and retention of the null-related midpoint.
- A seam-crossing shortest circle arc, and a two-component displacement
  rejected by the actual Euclidean product order but admitted by a maximum
  distance surrogate.
- Antipodal null endpoints strictly inside the selected sphere–circle slab,
  distance `Real.pi` rather than chord distance two, and a genuine ordered
  link through the antipodal cut locus.
- Unchanged flat, conformal and dimensional baselines.

## Acceptance and validation boundary

| #137 requirement | Evidence |
| --- | --- |
| Audit and reuse actual generic probability hypotheses | Existing `MeasuredOrderPoisson` and `DimensionMeasureExpectation`; four-dimensional abbreviations and specialization proofs |
| One shared owner, signatures early, compatible consumers | Linked coordination comment and additive modules; only three additive root imports |
| Real torus and sphere–circle orders and induced volumes | Quotient cube transport, proved angular/product distances, checked sphere induced-area identification, finite/atomless and standard Borel proofs |
| Ambient containment, not intrinsic GH substitution | `Ultrastatic.interval_subset_slab` and both concrete specializations |
| Finite-density/count/Mecke bridge, null relations and endpoints | Existing generic layer theorem, concrete expectation specializations, independent regressions |
| No target defined from action coefficients | No curvature/joint target is introduced or modified |
| Incremental development, final integrated local gate | Recorded below and in the validation receipt |

Final Lean-affecting input commit:
`f0aa46acefe27e753d0839ddaa90853a7e159b4f`.
The pinned-base incremental gate and the required fresh full local
`formal/check.sh` **passed** on that input. With the default two workers, the
full run checked 288 sources with warnings as errors and the transitive-axiom
rule, then audited **3,022 public theorems and all public definitions** in the
aggregate. Wall time was **2:41:52**; maximum single-process RSS was
2,925,968 KiB (not the sum of concurrent processes).

The [machine-readable receipt](receipts/issue-137-validation.json),
[complete input inventory](receipts/issue-137-inputs.sha256.gz),
[full audit log](receipts/issue-137-full-audit.log.gz) and
[timing record](receipts/issue-137-full-audit.time.txt) record the exact inputs
and result. All **13,537** selected source, checker/configuration, dependency,
toolchain and compiled-object hashes regenerated byte-identically after the
audit. All nine dependency checkouts match the unchanged manifest and have
unchanged tracked files. Later documentation/receipt-only changes do not alter
Lean validation inputs and do not require repeating this gate.

Local symbolic checks, all **306 Python tests**, Markdown lint and its **20
tests** passed. New mathematical contracts are Lean code; no rendered equations
were changed. PR CI is recorded separately on the PR's current head, not treated
as a substitute for this local proof audit.

No merge, deployment, or closure of #81/#24 is performed. Independent human
mathematical review remains separate. This bounded finite-density foundation
does not establish arbitrary Lorentzian manifold coverage, curvature/joint
identities, the thin-torus action limit, a sphere-cut-neighborhood estimate,
noncompact extensions, rates, or sample-wise convergence.
