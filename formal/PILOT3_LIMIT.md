# Full smooth 3D deterministic and expected limits (#80)

## Exact claim and supported class

`BoundaryDraft/Pilot3Limit.lean` proves the **unchanged**
`Pilot3DeterministicGoal` and `Pilot3ExpectedGoal` from `Pilot3Contract.lean`.
The new coverage is exactly `SmoothPilot3`: physical dimension three,
`DimensionSpacetime 2`, fixed flat metric, smooth ambient height/future germs
near the closed positive region, bounded positive region, regular zero-height
joint and the original strict **combined** global slope budget. Smooth germs
are stronger than the separately proposed all-dimensional C³ class. No
independent-envelope dimensional enlargement is asserted.

No definition of admissibility, region, action, probability law, angle, measure
or target changes. The deterministic observable is the original
`dimensionWeightedAction 2` at source weight one with the dimension-three
point/pair/interval coefficients. The expected observable integrates the actual
`discreteDimensionAction` against the constructed restricted-volume
`FinitePoisson.law`. It is not defined by a deterministic integral.

The target remains `pilot3BoundaryIntegral`, defined independently of the action
from the future-normal angle and induced Lorentzian Gram area. Spatial
Hausdorff one-measure has normalization one. The
[#115 area/atlas/integration proofs](PILOT3_INTEGRATION.md) identify that same
fixed measure on every Borel chart subset and overlap, then glue the whole
joint. Neither an arbitrary supplied measure nor Euclidean spacetime area
replaces it.

Import `BoundaryDraft.Pilot3Limit`. All names below are in `BoundaryDraft`:

```lean
theorem SmoothPilot3.action_limit
    {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    Tendsto (fun ρ => pilot3Action ρ h f) atTop
      (𝓝 (pilot3BoundaryIntegral h f))

theorem SmoothPilot3.expectedAction_limit
    {h f : Pilot3Space → ℝ} (hf : SmoothPilot3 h f) :
    Tendsto (fun ρ => dimensionExpectedAction 2 ρ (pilot3Region h f)) atTop
      (𝓝 (pilot3BoundaryIntegral h f))

theorem pilot3DeterministicGoal : Pilot3DeterministicGoal
theorem pilot3ExpectedGoal : Pilot3ExpectedGoal
```

The companion `action_limit_joint` and `expectedAction_limit_joint` state the
same limits as angle-weighted integrals on the actual spacetime joint,
using the separately proved `boundaryIntegral_eq_joint`. No analytic
hypothesis is supplied by the caller.

## Compatible inputs, not issue-closure inference

The earlier #78/#79 packages remain conventional proofs and diagnostics at
their delivery scope. Their later formal producers are the inputs here:

| Role | Actual proved input |
| --- | --- |
| Region, independent target and intrinsic identification | [#115 geometry](PILOT3_GEOMETRY.md), including canonical chart area, collar/coarea and whole-region divergence |
| Actual short response, remainder and target coefficient | [#126 / PR #129](PILOT3_SHORT.md), `SmoothPilot3.exists_shortAction_limit` |
| Actual long density, signed transport, contact jet and cancellation | [#125 / PR #128](PILOT3_LONG_NULL.md), `SmoothPilot3.tendsto_longAction` |
| Exact complete signed action split | `Pilot3Displacement`, `SmoothPilot3.action_eq_short_add_long` |
| Separate finite-density Poisson bridge | [#77](DIMENSION_EXPECTATION.md), specialized by `SmoothPilot3.expectedAction_eq` |

PR #129 already consolidated the two producers under the canonical displacement,
circle and null-coordinate definitions. Its integration regression proves a
common cutoff exists. This assembly imports both actual producers; it does not
instantiate two conditional consumers with postulated jets or limits.

## Conventional assembly proof

Fix any member of `SmoothPilot3`. The actual short theorem constructs a
positive geometric cutoff bound and proves convergence to the independent
target at every smaller positive fixed cutoff, including the bound itself.
Choose that endpoint once. The choice depends only on the fixed region, not on
density. The actual long theorem applies at every positive fixed cutoff, so
its fully normalized signed contribution tends to zero at this very choice.

For every density the complete action is exactly the sum of this short action
and this signed long action. This identity was proved by endpoint/displacement
shear and absolutely integrable signed splitting of the original causal-pair
integral. The elementary addition law for limits therefore gives convergence
of the full deterministic action to the short target. Equivalently,
`tendsto_action_sub_short` first proves that the full-minus-short difference
tends to zero, and `tendsto_action_iff_short` transfers the short limit. The
proof of `action_limit` supplies the geometry-selected endpoint to this
fixed-cutoff equivalence.

There is no cutoff-removal step. The strict short domain and closed long domain
are disjoint and exhaust the future cone; equality belongs to long, including
null displacements. The point term is assigned exactly once, to short. All
source components and all future partners are present in both the overlap and
the original action. The full-circle mass is `2 * Real.pi`; the canonical
3D Jacobian is `pilot3NullJacobian σ v = (1 - σ / v ^ 2) / 4`. The negative
long prefactor retains both density factors. These conventions are shared
identically by the two proofs, not reconciled by an assumed asymptotic identity.

The short producer uses direct-origin absolute overlap, not planar comparison.
Its constant fractional response cancels the physical point volume. The linear
slice, future Hessian and joint square remain through the signed angular/radial
calculation; whole-region divergence identifies the resulting coefficient with
the independent normal/Gram target. Finite collar weights localize sources only,
retain cross-chart partners and are summed with their derivative contributions
before the whole overlap jet is obtained. This assembly introduces no artificial
chart boundary or external source partition, and claims no additional weighted
action theorem. A global planar-base theorem is neither needed nor assumed.

The long producer derives the actual averaged linear jet with a uniform
quadratic error, sufficient for the real three-halves cancellation order.
Exact/approaching contacts, completely closing fibres and positive-height
critical points remain. The short producer supplies its own derivative-controlled
nearly-null remainder, including moving endpoints. The assembly does not
replace either estimate with a value-only Taylor bound or an absolute estimate
of the original signed kernel.

Only after the deterministic result, use `expectedAction_eq` at positive
density. Positivity holds eventually as density tends to infinity; thus the
actual expectation and deterministic action are eventually equal. Limit
congruence proves `expectedAction_limit`. Its probability measure and absolute
integrability were derived by #77 from the finite region constructor, not
assumed for this step. This proves convergence of expectations, not convergence
in probability or almost surely of individual sprinklings.

Finally the same long theorem shows the full-minus-short difference tends to
zero at **any** other fixed positive cutoff. Hence `shortAction_limit` extends
the short limit to every fixed positive cutoff after assembly, and
`tendsto_short_sub_short` proves that two such fixed choices have vanishing
difference. These are pointwise-in-cutoff consequences, not uniform estimates
or permission to use a density-dependent cutoff.

## Regressions and acceptance audit

`Pilot3LimitRegression.lean` imports producer modules directly, independently
of the library root, and is discovered by the full source audit. It checks:

- Both original goal propositions, without new premises.
- The expanded complete bilocal action, actual 3D kernel and physical density
  powers, and the canonical Hausdorff/Gram/angle target.
- The expanded discrete layer sum and restricted finite Poisson law;
  probability and action integrability follow from the geometric constructor.
- One common fixed cutoff, the exact point-once signed split, equality in long,
  and independence of two arbitrary fixed positive cutoffs.
- Both full limits for the nonempty ball/sine member, with actual nonzero future
  second derivative and retained positive-height critical point.
- Planar recovery as a consequence, the whole disconnected curved region,
  both annular boundary components and interior critical circle, and the empty
  control. No componentwise additivity of a bilocal action is asserted.
- Both intrinsic spacetime-joint formulations.
- Every original 4D C³ member's coordinate compatibility, both unchanged old
  goal contracts, and the original unequal-axis `48 * Real.pi` deterministic
  and expected calibration. These remain separate 4D results.

| #80 acceptance | Delivered here |
| --- | --- |
| Independently stated non-vacuous deterministic goal | `pilot3DeterministicGoal`, actual action/target regressions and curved/critical examples; independent area identification reused from #115 |
| Complete compatible signed short/long assembly | One fixed cutoff from #126, #125 at that same cutoff, exact `action_eq_short_add_long`; point, partner, partition and boundary terms retained upstream |
| Expectation only after deterministic proof | `expectedAction_limit`, then `pilot3ExpectedGoal`, using #77's exact positive-density identity |
| Conventional proof, exact coverage and integrated verification | Proof above, coverage below, standalone regression and required full source/axiom audit on the final Lean inputs |

## Residual dimension and generalization obligations (#81 / #24)

| Scope | Status after this package | Remaining obligation |
| --- | --- | --- |
| Flat 3D `SmoothPilot3` | Full deterministic and expected limits with unchanged intrinsic target | Independent human mathematical review; this is only a partial resolution of the general conjecture |
| Flat 3D C³ candidate, independent-envelope enlargement or arbitrary atlases/regions | Not covered by this smooth combined-budget theorem | Prove the corresponding actual geometric and analytic producers on a separately named justified class |
| Flat 4D original C³ two-face class and class E | Existing checked results unchanged | This 3D assembly does not establish unrestricted 4D coverage |
| Physical dimension two | Checked interval/expectation infrastructure and regular endpoint-counting geometry; regulated local coefficient | Full two-face short/long analysis, independent global contract and assembly beyond existing special cases |
| Physical dimensions five and six | Written long-only result for the separately named `C4LongPilot56` at sufficiently small fixed cutoffs | Formal geometric/analytic ports and actual short responses, remainder and intrinsic coefficient before global assembly |
| Other dimensions and general curved metrics | No new result here | Dimension-specific interval/curvature, intrinsic geometry, short/long estimates and compatible expectation instances under #81/#24 |
| Null/mixed boundaries | No extension here | Existing special results retain their own scopes and wider obligations |

In odd dimensions the first **height** moment is positive, not zero. In even
dimensions the second height moment diverges; the 4D zero-first-moment shortcut
and a finite-second-moment Taylor argument cannot be copied across dimensions.
Critical fractional/logarithmic terms must be retained until their complete
signed response is proved. Neither the 5D/6D long-only test nor this 3D theorem
closes arbitrary-dimensional coverage, #81 or #24. No obstruction to a proof
route is promoted to a counterexample to the full action conjecture.

## Validation and independent review

Follow [the pinned setup and full gate](README.md#reproduce). The final PR
records the exact audited Lean inputs and observed results. The full gate must
run **after the last Lean-affecting change**, even though each upstream producer
already has its own audit. A successful build or incremental check is not that
gate, and GitHub CI does not replace it.

```sh
cd formal
LEAN_NUM_THREADS=2 ./check.sh --incremental --base origin/main
LEAN_NUM_THREADS=2 ./check.sh
cd ..
.venv/bin/python -m unittest -v
.venv/bin/python check_symbolic.py
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
node --test scripts/test-proof-spine.mjs
```

Written argument, Lean kernel verification, symbolic/numerical diagnostics and
independent human mathematical review are separate. This package supplies the
first three with their stated validation boundaries; independent human review
remains outstanding. No rate for the full action, density-dependent geometry,
shrinking-cutoff uniformity or individual-sprinkling convergence is asserted.
