# Controlled curved 4D bulk-and-joint expectation limit (#76)

**Conventional written theorem, not a new Lean continuum-limit theorem or an
independently reviewed result.** This assembles the actual bulk/collar and
joint producers on the original C³ two-face class with the fixed conformal
volume density `q(t)=1+t^2`. The complete deterministic limit is proved first;
the expected limit then follows from #93's separately proved exact identity,
with its geometric hypotheses discharged below. Neither numerical convergence
nor the flat expectation bridge is used as a premise.

The integration base is `cfe211ecbe107b68505f4e945ab8453f5da546a5`. The inputs
are merged results, not the earlier obstruction-only deliveries:

| Input | Exact merged source / consumer output | Verification boundary |
| --- | --- | --- |
| #117 / #121 | [Contact-averaged long theorem](curved-contact-long.md#5-fully-normalized-signed-limit-and-summable-interface), (A14)-(A15) | Written signed cancellation, after contact averaging; not raw-fibre domination |
| #74 / #123 | Merge `6b7cac5f2866588eb137ba7bc8136ff62ad7758a`; [boundary-collar handoff](curved-boundary-collar.md), (H16)-(H18), consuming #122's full-cone remainder | Written whole-bulk/non-joint theorem, not just the old second-jet model |
| #75 / #127 | Merge `c74801692a65f58be3f8e3caf7e0ccf1824946a1`; [joint-corner theorem](curved-joint-corner.md), (J17)-(J19) | Written limit of the actual corner plus its single-face flux |
| #93 / #101 | Merge `efe7f8340920f363cb84d69fdc592d553900d5c0`; [canonical API](../formal/CONFORMAL_ACTION.md) | Lean finite-density expectation theorem; not a curved asymptotic theorem |

At this base, `ConformalAction.lean`, `ConformalGeometry.lean` and
`FiniteMeasureBDG.lean` are unchanged from #93's merged API. Its recorded
source/transitive-axiom audit was on
`9aed02c70f01c9fd4c5d14e5e4b1024d94f8367f`. Source identification is not a new
audit of the current Lean tree. Earlier notes retain their historical gaps;
the later named producers above supply precisely those missing estimates.

## 1. Fixed class, independent observable and target

Fix any original `AdmissibleTwoFace h f`, unchanged from
[`TwoFaceContract.lean`](../formal/BoundaryDraft/TwoFaceContract.lean). Thus
the positive-part height and future envelope have a strict combined global
Lipschitz budget, the positive spatial region has compact closure, the face
germs are C³ near that closure, and its joint is a regular height level.
There is no assumed jet, cancellation, action limit or expectation identity.
Positive-height critical points and all components remain allowed. Write

```math
\begin{aligned}
\mathcal O&=\{z:h(z)>0\},&\Sigma&=\partial\mathcal O,&\ell&=f-h,\\
M&=\{(t,z):z\in\mathcal O,\ \ell(z)\lt t\lt f(z)\},&
J&=\{(f(z),z):z\in\Sigma\},\\
q(t)&=1+t^2,&\Omega(t,z)&=q(t)^{1/4},&g&=q(t)^{1/2}\eta,\\
\eta&=\mathrm{diag}(1,-1,-1,-1),&&d\mu_g=q(t)\,dt\,dz.
\end{aligned}\tag{CA1}
```

Time increases toward the future. The lower global causal envelope is
`f - max 0 h`; ell denotes its raw C³ expression only on the positive region
and its face germs. The entire frontier consists of the past and future faces
over the closed positive region, with common boundary J; there is no missing
lateral wall or additional stratum. Causal convexity, boundedness and Borel
measurability are supplied by the original geometry. Conformal positivity
preserves its cones and causal order.

Use exactly the curvature convention of #73 (C4) and #90, §2:

```math
\begin{aligned}
R^a{}_{bcd}&=\partial_d\Gamma^a_{cb}-\partial_c\Gamma^a_{db}
 +\Gamma^a_{de}\Gamma^e_{cb}-\Gamma^a_{ce}\Gamma^e_{db},\\
\mathrm{Ric}_{bd}&=R^a{}_{bad},\qquad R=g^{bd}\mathrm{Ric}_{bd},\\
R(t)&=6\Omega^{-3}\Omega''=\frac{3(1-t^2/2)}{(1+t^2)^{5/2}}.
\end{aligned}\tag{CA2}
```

This is an independent Levi-Civita calculation, not a definition through an
action coefficient. The scalar in #93's example and `conformal_geometry.py`
has the opposite Riemann sign; it is **minus** (CA2). The finite-density API
itself has no curvature convention or target.

Let I[x,y] be the original closed causal interval, retaining null relations.
The actual isolated volume and production observable are

```math
\begin{aligned}
V_M(x,y)&=\mu_g\bigl(M\cap(I[x,y]\setminus\{x,y\})\bigr),\\
K(z)&=(1-9z+8z^2-\tfrac43z^3)e^{-z},\qquad C=4/\sqrt6,\\
A_g(\rho,M)&=C\sqrt\rho\left[\mu_g(M)-\rho\int_M
 \int_{M\cap J^+(x)}K(\rho V_M(x,y))\,d\mu_g(y)\,d\mu_g(x)\right].
\end{aligned}\tag{CA3}
```

These are `conformalIntervalVolume` and `conformalAction`, expanded by
`conformalAction_eq_integral`, not a second production definition. Both endpoint
measures and both density factors are present. Ambient/restricted compatibility
is used only for endpoints in M, by causal convexity and atomlessness.
Auxiliary outside-region intervals in #74/#75 use their actual ambient law
and cancel by (H3); they are not assigned the restricted-volume identity.

Define the joint measure from the positive metric induced by minus g, and the
angle from the two **future** unit timelike normals (past inward, future
outward). With p=Df, a=Dh, k=|a| and b the projection of p tangent to Sigma,
#75 (J3)-(J4) independently give

```math
\begin{aligned}
\gamma&=g(N_-,N_+)=\frac{1-|p|^2+p\cdot a}
 {\sqrt{(1-|p|^2)(1-|p-a|^2)}}>1,\qquad\theta=\mathrm{arcosh}\,\gamma>0,\\
dA_g&=\sqrt{q(f)}\sqrt{1-|b|^2}\,dA_\Sigma,\\
\mathcal I_g&=\int_J\coth\theta\,dA_g
 =\int_\Sigma\sqrt{q(f)}\frac{1-|p|^2+p\cdot a}{k}\,dA_\Sigma,\\
\mathcal B_g&=\frac12\int_M R\,d\mu_g.
\end{aligned}\tag{CA4}
```

The spatial reference area is normalized Euclidean area, not Euclidean
spacetime area. The induced chart measures agree on every Borel overlap by
the Gram Jacobian transformation. Compactness, regularity and the strict
slope budget imply finite area and fixed positive angle/normal/height-gradient
margins; hence the joint integrand is absolutely integrable. R is continuous
on the compact closure and metric volume is finite, so the bulk integral is
also absolutely integrable. No geometric quantity is defined by the action.

**Theorem (written, controlled curved 4D assembly).** For every fixed original
admissible pair and exactly the metric (CA1),

```math
\begin{aligned}
\lim_{\rho\to+\infty}A_g(\rho,M)&=\mathcal B_g+\mathcal I_g,\\
\lim_{\rho\to+\infty}\mathbb E_{\Pi_{\rho,g,M}}
 [A^{\mathrm{disc}}_\rho]&=\mathcal B_g+\mathcal I_g.
\end{aligned}\tag{CA5}
```

The law and discrete action in the second line are independently constructed
in §4. Empty positive regions give zero throughout. The nonempty example in
§5 has strictly positive bulk, nonconstant scalar curvature and variable
joint angle. No rate, changing geometry, singular-angle limit, shrinking-cutoff
uniformity or individual-sprinkling convergence is asserted.

```text
PROVED IN WRITING ControlledCurvedDeterministicLimit(h,f):
  input: original AdmissibleTwoFace h f, fixed Omega(t,z)=(1+t^2)^(1/4)
  actual conformalAction tends to independent whole bulk + induced joint

PROVED IN WRITING ControlledCurvedExpectedLimit(h,f):
  same geometric input, genuine discreteBDGAction and conformalProbability
  consume the proved positive-density conformal_expectedAction_eq
  its expectation tends to the same independent bulk + joint
```

These are theorem-contract descriptions, **not compiled Lean declarations**.

## 2. Deterministic proof at one fixed cutoff

Use the weighted notation of (H16), with fixed real C⁵ endpoint fields chi
and phi near the whole closure. Unit fields qualify. The point term is the
integral of chi times phi at the same source; the pair term uses chi(x)phi(y).
Choose delta positive and smaller than both #74's and #75's derived bounds.
For a finite collection of fields take the minimum of these finitely many
positive bounds. #117's long theorem works for **every** fixed positive delta
and C² fields, so it applies to that same choice. There is no competing cutoff
scheme or need to let delta approach zero.

The exact split uses `v = delta_t + spatial_distance`: short is `v < delta`,
long includes equality. The point term is allocated once, to short. All
finite-density integrals are absolutely finite before signed Fubini. In the
notation of (H3)-(H4), let F be the full single-future-face strip and J_c the
actual overshoot corner integral, distinguished here from the joint set J.
Then

```math
\begin{aligned}
A_{\chi,\phi}&=S^{\mathrm{full}}_{\chi,\phi}
 +C\rho^{3/2}F_{\chi,\phi}-C\rho^{3/2}J_{c,\chi,\phi}
 +L_{\chi,\phi},\\
\mathcal Q_{\chi,\phi}&=-C\rho^{3/2}J_{c,\chi,\phi}-\mathcal T_{\chi,\phi},\\
\mathcal B_{\chi,\phi}&=\int_M\chi(\Box_g\phi+R\phi/2)\,d\mu_g,\\
\mathcal N_{\chi,\phi}&=\int_{\mathcal O}\sqrt{q(f)}
 (\phi N_f\chi-\chi N_f\phi)_{t=f}\,dz,\qquad
 N_f=\partial_t+Df\cdot\nabla_z,\\
\mathcal T_{\chi,\phi}&=\int_\Sigma\sqrt{q(f)}(\chi\phi)_{t=f}
 Df\cdot\nu_{\mathcal O}\,dA_\Sigma,\qquad\nu_{\mathcal O}=-Dh/k,\\
\mathcal I_{\chi,\phi}&=\int_J\chi\phi\coth\theta\,dA_g.
\end{aligned}\tag{CA6}
```

All auxiliary outside-region pairs in the first line cancel **exactly** by
(H3), which remains valid at contact. No frozen or clipped corner model has
been substituted. Define four residuals solely for accounting:

```math
\begin{aligned}
e_{\mathrm{full}}&=S^{\mathrm{full}}_{\chi,\phi}-\mathcal B_{\chi,\phi},\\
e_{\mathrm{face}}&=C\rho^{3/2}F_{\chi,\phi}-\mathcal N_{\chi,\phi}
 +\mathcal T_{\chi,\phi},\\
e_{\mathrm{corner}}&=\mathcal Q_{\chi,\phi}-\mathcal I_{\chi,\phi},
 &e_{\mathrm{long}}&=L_{\chi,\phi},\\
A_{\chi,\phi}-\mathcal B_{\chi,\phi}-\mathcal N_{\chi,\phi}
 -\mathcal I_{\chi,\phi}
 &=e_{\mathrm{full}}+e_{\mathrm{face}}+e_{\mathrm{corner}}+e_{\mathrm{long}}.
\end{aligned}\tag{CA7}
```

Each residual tends to zero by a proved producer, not an admissibility field:

1. **Full:** (H5) applies #122's uniform full-cone signed remainder on the
   whole compact source closure, retaining the actual correction (H3).
2. **Face:** (H12)-(H15) control the entire curved face remainder and identify
   its response as N minus T, including endpoint derivatives and moving
   diagonal strips. This uses only C³ faces, not an unstated C⁵ geometry.
3. **Corner:** (J17)-(J19) compare the actual curved corner with its tangent
   integral with signed control. Restoring minus T gives exactly (CA4)'s
   independently induced joint target, not just its part without p dot a.
4. **Long:** (A14) cancels the actual long sector **after** time/contact
   averaging, including every partner. It does not use the false raw
   first-endpoint dominator or absolute nearly-null bound.

A finite sum of these four vanishing errors proves the weighted limit
`A_chi,phi -> B_chi,phi + N_chi,phi + I_chi,phi`. For chi=phi=1, Box applied
to one and N both vanish identically, B is the **whole** half-curvature
integral, and I is the unweighted joint integral. This proves the first line
of (CA5). T generally does **not** vanish for unit fields; it has been retained
in the corner target. Deleting it would give the wrong joint coefficient.

## 3. Complete partner, collar and artificial-cutoff accounting

- **Complement of the joint collar:** J_c is supported where `0 < h < d <= delta`,
  but the full-cone bulk and single-face strip are integrated on all of O.
  Outside this collar the overshoot is zero, not the whole short contribution.
  Equation (H18), equivalently (CA7), includes the entire collar curvature
  integral. No finite collection of compact interior supports is mistaken for
  a cover up to the boundary, and no collar is dropped by small volume.
- **Single faces:** the face response N minus T is kept in (CA7). If B is
  integrated by parts for nonconstant fields, both oriented spacetime fluxes
  in (H17), at t=f and t=ell, remain. They vanish for the unit field, not for
  an arbitrary weighted patch. No hidden flux is absorbed into admissibility.
- **Finite source partitions:** choose smooth weights summing to one on a
  neighborhood of the closure and the chosen auxiliary tube. The point,
  short, long, full, face, corner and flux terms sum exactly at every density.
  Their finitely many errors vanish at one common fixed cutoff. For phi=1,
  source derivatives in N cancel only after the complete sum.
- **Both-endpoint partitions:** for weights chi_i and phi_j each summing to one,
  retain the **entire ordered double sum**. This includes off-diagonal chart
  labels in the bilocal action and in its auxiliary restoration. The sums of
  Box phi_j and field derivatives vanish only then; same-chart-only pairing
  would change the observable. The point term also uses the double sum of
  chi_i(x)phi_j(x), equal to one, not one independent point term per chart.
- **Chart overlaps:** #75's height-chart partition glues the actual corner
  without restricting its partners. Its independent induced measure agrees
  on overlapping Borel sets, not just disjoint chart cells. All components
  and positive-height critical points outside the regular collar survive.
- **Cutoffs and extensions:** density varies with the geometry, fields,
  regular collars and delta fixed. Every smaller permitted fixed delta gives
  the same limit. (H16) and (J19) also show that different auxiliary field
  extensions agreeing on M have asymptotically identical Q. These facts are
  not uniform estimates for a density-dependent or shrinking cutoff.

Thus the four residuals exhaust the actual normalized action. No unassigned
cross-chart, contact, collar-complement or artificial-boundary term remains.

## 4. Apply the curved expectation bridge, with every instance hypothesis

For each positive rho, construct exactly

```math
\begin{aligned}
\Pi_{\rho,g,M}&=\mathrm{FinitePoisson.law}(\rho\,\mu_g|_M),\\
A^{\mathrm{disc}}_\rho(\mathcal C)
 &=\frac4{\sqrt6\sqrt\rho}\bigl[N-N_0+9N_1-16N_2+8N_3\bigr].
\end{aligned}\tag{CA8}
```

Here N_k counts ordered distinct related pairs having exactly k other points
in the closed interval; only the two selected endpoints are removed. Null
relations are not changed to a chronological order. These are
`conformalProbability` and the unchanged `discreteBDGAction`. The expectation
is its integral under that constructed law, not defined to be (CA3).

The specialization of `AdmissibleTwoFace.conformal_expectedAction_eq` is valid
for **every** member in §1:

| Required input / derived obligation | Discharge on this same class |
| --- | --- |
| Original `AdmissibleTwoFace h f` | The theorem's geometric input, not a strengthened or expectation-valued structure |
| Measurable bounded M | `hf.boundedCausalRegion.measurable` and `.bounded` from the original geometry |
| Globally measurable Omega | The positive polynomial `1+t^2` composed with its smooth positive fourth root is globally smooth, hence Borel |
| Open controlled neighborhood | Choose T greater than the maximum absolute time on the compact closure; the open slab `abs(t) < T` contains the closure |
| Smoothness and bounds on that slab | Omega is smooth of all orders there, with lower bound 1 and upper bound `(1+T^2)^(1/4)`, independent of rho |
| Finite atomless metric volume | `ControlledConformalFactor.finite_volume` and `conformalVolume_noAtoms`; restriction and positive-density scaling preserve these properties |
| Actual restricted/ambient interval compatibility | `ControlledConformalFactor.intervalVolume_ambient` with original causal convexity and endpoints in M; endpoint removal is null |
| Finite-density measurability/integrability | `measurable_intervalVolume`, `measurable_kernel`, `integrable_causalKernel`, `integrable_outer_kernel`, and `integrable_discreteAction` from the curved API |
| Genuine law and finite-order observable | `isProbabilityMeasure`, `ae_supported`, `ae_nodup`, and `ae_finite_order` for that constructed conformal law |
| Positive density | rho is positive in (CA8); this holds eventually when tending to positive infinity |

The slab and root argument explicitly verify `ControlledConformalFactor` for
this **fourth-root** pilot. The checked `quadraticConformalFactor` example in
#93 instead uses `Omega=1+t^2`; it is not silently reused as this instance.
This instantiation is a conventional argument applying the existing universal
Lean theorem, not a newly compiled instance declaration.

The curved theorem therefore gives, at every positive density,

```math
\begin{aligned}
\mathbb E_{\Pi_{\rho,g,M}}[A^{\mathrm{disc}}_\rho]&=A_g(\rho,M),\\
K(z)&=\sum_{k=0}^3 c_k e^{-z}\frac{z^k}{k!},
 & (c_0,c_1,c_2,c_3)&=(1,-9,16,-8).
\end{aligned}\tag{CA9}
```

The second line checks the ordered-layer coefficients, not a replacement
proof of Mecke. In that already proved bridge the point expectation carries
rho and the pair expectations carry rho squared; the normalization in (CA8)
yields (CA3). No factor of two for unordered pairs is allowed.

Apply the first line of (CA5) to the first line of (CA9). Equality on the
positive-density tail proves the expected limit in (CA5); no interchange of
expectation and a random limit, or coupling of different sprinklings, is used.
`BoundedCausalRegion.expectedBDGAction_eq` is **not** invoked as a curved theorem.
For an empty region the zero measure produces the empty sample almost surely,
and the action and both targets are zero.

## 5. A genuinely curved, variable-angle member with both terms nonzero

Take the original unequal-axis cap with

```math
\begin{aligned}
h(z)&=\tfrac14(1-z_1^2-z_2^2/4-z_3^2/9),&f(z)&=\tfrac18,\\
(b_1,b_2,b_3)&=(1,2,3),&H&=\tfrac14.
\end{aligned}\tag{CA10}
```

Its positive-part height is globally 1/2-Lipschitz, f has slope zero, all germs
are smooth, and the compact ellipsoidal joint gradient norm ranges from 1/6
to 1/2. Thus the original combined budget is strict, with the positive-height
critical center retained. The origin lies inside M. Its time closure is
`[-1/8,1/8]`, so the slab `abs(t)<1` has conformal bounds 1 and `2^(1/4)`.
The scalar (CA2) is positive throughout the closure and takes distinct values
at the interior times 0 and 1/16: this is **not constant curvature**.

At the first and third axis tips the angle weights are 2 and 6. The joint
lies at time 1/8, so its conformal induced area factor is `sqrt(65/64)`.
Ellipsoidal coarea or direct sphere parametrization gives the independent target

```math
\begin{aligned}
\mathcal I_g&=48\pi\sqrt{65/64},\\
\mathcal B_g&=\frac32\int_{-1/8}^{1/8}
 8\pi(1/2+4t)^{3/2}\frac{1-t^2/2}{(1+t^2)^{3/2}}\,dt>0,\\
\mathcal B_g&\ge\frac{4\pi}{5}\,
 \frac{3(1-1/128)}{2(65/64)^{3/2}}>0.
\end{aligned}\tag{CA11}
```

Indeed the spatial slice volume is `8*pi*(1/2+4*t)^(3/2)` and the flat
four-volume is `4*pi/5`. The lower bound follows pointwise from the time
range, independently of any action. Integrating the exact primitive
`9*t/(4*sqrt(1+t^2)) - 3*asinh(t)/4` of R*q/2 over spatial source radii gives
an independent check of the same bulk integral. The proved deterministic and
expected limits for this member are **the sum** of these two nonzero terms.
The theorem also includes #75's sine-future variant, with its nonzero
single-face joint flux; a planar future is not a theorem restriction.

## 6. Coverage comparison and acceptance boundary

This is a substantive controlled curved partial result under #24, **not its
completion**. Relative to [#90's baseline matrix](general-contract.md#1-coverage-matrix-target-is-not-the-union-of-todays-pilots):

| Coverage axis | What (CA5) now supplies | What remains open under #81/#24 or the indicated owner |
| --- | --- | --- |
| Dimension / observable | 4D, unsmeared original minimal layers and normalization | General-dimensional curved limits; no promotion of a 4D proof to 2D counting or higher dimensions |
| Metric / bulk | Exactly the fixed time-dependent fourth-root conformal factor, with independently identified whole half-curvature integral | Arbitrary smooth conformal factors, non-conformally-flat metrics, caustics/conjugate points and general manifold atlases |
| Interval / causality | Actual isolated curved intervals on the original ambient-causally-convex coordinate regions | Non-convex embeddings and intrinsic-versus-restricted-order questions |
| Regularity / presentation | Original C³ two-graph combined-budget class; all its components and allowed critical points | Independent-envelope curved enlargement, general face atlases, arbitrary topology and finite-regularity refinements outside this class |
| Joint / strata | Every past/future spacelike joint component of this class, induced area and varying positive angle | Curved null/mixed joints, same-side seams, tips, extra corners and singular-angle transitions; timelike boundaries stay with #26 |
| Compactness / integrability | Fixed compact closure and finite absolutely integrable bulk/joint targets | Noncompact signed tails and exhaustion; no density-dependent margins |
| Expectation / review | Written deterministic assembly plus application of the checked exact curved bridge | New Lean asymptotic formalization, independent human scrutiny #94/#86, publication and novelty audit |
| Limits | Fixed geometry and a common fixed cutoff chosen once | Rates, shrinking-cutoff uniformity, variance, concentration and individual-sprinkling convergence |

The all-dimensional/general-curved gate remains #81, with final coverage and
review integration under #86. The old localization obstructions are still
valid for their rejected proof routes, not counterexamples to the full action.
No additional geometric exclusion or desired cancellation has been inserted
to evade them.

**#76 acceptance map:** (CA5) and §5 provide a non-vacuous bulk-plus-variable-angle
theorem; §§2-3 exhaust all partners, collar and cutoff terms at one fixed cutoff;
§4 applies the actual curved bridge and discharges its instance; this section
keeps the general gaps open. Written arguments, executable evidence and
machine verification have different statuses:

- **Written proof:** the complete assembly above consumes the actual named
  upstream producers, not obstruction reports or conditional jets.
- **Executable regressions:** `curved_assembly.py` checks residual signs,
  Poisson coefficients/density powers and a geometric primitive.
  `test_curved_assembly.py` independently integrates the whole unequal-axis
  pilot in original source-time/target-time/radius coordinates. It checks
  full/short/long and full/face/corner restoration, overlapping signed source
  and target partitions with nonzero off-diagonal pairs, independent positive
  nonconstant curvature and induced variable-angle area, and flat/nonunit
  constant-factor calibrations. Wrong endpoint measures, frozen phase,
  missing density powers and unordered-pair factors are negative controls.
  Finite quadrature and refinement are not proofs of convergence or rates.
- **Lean:** no Lean source, checker, dependency or build input changes. The
  existing finite-density theorem retains its recorded audit; no new full
  integrated audit or Lean continuum-limit proof is claimed. Any later formal
  port must run the full local `formal/check.sh` gate on its integrated inputs.
- **Review:** independent human mathematical review remains outstanding under
  #94/#86. The PR records the exact validated head, observed CI and the bounded
  GitHub feedback snapshot separately; automated checks are not human review.

Reproduce with Python 3.12 and the pinned requirements (as in CI):

```sh
uv venv --python 3.12 .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python -m unittest -v test_curved_assembly
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
