# Complete two-tip deterministic and expected assembly TT-B (#155)

**Written theorem for exactly the selected fixed flat 4D U, not general
null/mixed coverage.** The deterministic result is proved first; the expected
limit then follows from the original finite Poisson law with the actual
region/order/volume hypotheses discharged below. No new Lean theorem or
independent human mathematical review is claimed. Refs #155, #154, #134, #81.

## 1. Pinned inputs, not administrative acceptance

Integration baseline: `41cf2c35378cf91c1c2d3651f8dd689370662bdf` on
`issue-81-general-coverage`. This continuation includes the **unmerged** TT-A
source at `43447dbf1be1de0e46d47147a3e07398ce396fdb` (PR #168), specifically
[LA1–LA10](two-tip-lens-limit.md). It is an explicit source dependency, not
independent acceptance of that PR. #83/#84's translated cap theorems and
[#134 TT1–TT11](two-tip-null-feasibility.md) are already in the integration
baseline; their actual proofs, rather than issue states, are used.

Keep a=1/2, b=1/10, H(z)=1+b*sin(z), the two tips at (0,±a,0,0), and precisely
TT1's caps M+, M-, intersection L, union U and exclusive parts E+, E-. Keep
ordinary four-volume, signature (+---), closed ambient causal order, isolated
restricted intervals, and the exact TT3 unsmeared action/layer normalization.
Only positive density tends to infinity. No geometric, angle, smoothing,
partner-cutoff or dimensional limit is implicit.

The targets S+, S-, J_L and J_U are **independent** induced SN areas from TT2.
They obey J_U+J_L=S++S-. The bulk curvature is identically zero. No coefficient
for a crease or tip is inserted as an admissibility field.

## 2. Physical point allocation and the full pair identity

The lower epigraph is a future set since its causal increment is at least
(1-b) times the time increment. Each upper cone is a past set. Consequently,
for endpoints in any one of the four regions, every point of the **closed
ambient interval**, including null segments and its endpoints, belongs to
that region. The isolated interval volume for timelike pairs is therefore
c*sigma², c=pi/24. Intrinsic order agrees because the entire straight causal
segment is contained. None of these facts follows from intrinsic global
hyperbolicity alone.

There are no causal pairs in either direction between E+ and E-. If a point
of E+ preceded one in E-, the latter's minus past cone would contain the
former, a contradiction. All other ordered pairs are retained. With
indicators and the ambient causal-pair indicator understood,

```math
\begin{aligned}
\mathbf1_U(p)&=\mathbf1_{M_+}(p)+\mathbf1_{M_-}(p)-\mathbf1_L(p),\\
\mathbf1_U(p)\mathbf1_U(q)\mathbf1_{p\preceq q}
 &=\left[\mathbf1_{M_+}(p)\mathbf1_{M_+}(q)
       +\mathbf1_{M_-}(p)\mathbf1_{M_-}(q)
       -\mathbf1_L(p)\mathbf1_L(q)\right]\mathbf1_{p\preceq q},\\
\mathcal A_\rho(U)
 &=\mathcal A_\rho(M_+)+\mathcal A_\rho(M_-)-\mathcal A_\rho(L).
\end{aligned}
\tag{LB1}
```

For point terms the physical allocation is 1+1-1 on L, and 1 on each exclusive
part. For pairs the subtraction removes exactly one copy of each L-to-L
pair. All L-to-E+ and L-to-E- partners remain in their corresponding cap.
There are no E-to-L causal partners: the same past-set argument would put
the source in L. No diagonal contributes to the Lebesgue pair integral.
Both measures and both powers of Poisson intensity are unchanged.

The equality is also true for restrictions of **one** finite configuration
in U. When both endpoints are in a cap or in L, closed interval containment
puts every intermediate point of the original configuration in that same
region. Thus restriction preserves the layer index of these endpoint pairs;
applying ordinary inclusion–exclusion to the points and to each ordered
layer separately proves the discrete identity. This does not assume actions
of independently sampled configurations are coupled or bilocally additive.

At finite density boundedness and continuity of the kernel on compact
closures justify all signed integrations in (LB1). General source/partner
partitions retain every ordered pair of charts. TT9's arbitrary measurable,
possibly source-dependent cutoff has the exact short-plus-complement sum;
the point term occurs in the short term only. No separately zero complement
is used in this proof.

## 3. Complete deterministic theorem and all strata

For each translated cap the floor is smooth, globally b-Lipschitz, and has
positive value H(±a) at its tip. These are precisely #84's hypotheses; no
standalone cap re-proof is needed. MA10 gives its full deterministic limit.
TT-A gives the actual lens limit. Hence, with the residuals defined from
the unchanged actions and independent areas,

```math
\begin{aligned}
e_i(\rho)&=\mathcal A_\rho(M_i)-S_i\longrightarrow0,\\
r_L(\rho)&=\mathcal A_\rho(L)-J_L\longrightarrow0,\\
\mathcal A_\rho(U)-J_U&=e_+(\rho)+e_-(\rho)-r_L(\rho)\longrightarrow0,\\
\lim_{\rho\to\infty}\mathcal A_\rho(U)&=J_U.
\end{aligned}
\tag{LB2}
```

This is a deterministic theorem, before any probability transfer. It concerns
the complete U action, not an isolated sheet or a locally regulated wedge.
The screen target has unit SN weight, derived through the full TT-A/cap
responses, not by evaluating a spacelike angle formula at infinity.

| Actual stratum | Independent geometry and complete-action accounting |
| --- | --- |
| Smooth lower face | H's strict spacelike graph, with nonzero second fundamental form on an open set; its actual moving floor is kept in LA3 and its Hessian/flux in LA10 |
| Two exposed null sheets | Cone generators from a floor or crease endpoint to their own tip; the two cap responses contain all partners; the complementary lens sheets are subtracted exactly |
| Two SN pieces | Induced area from TT2; radial/time derivatives cancel in the Lorentzian Gram matrix; J_U is their total area |
| Same-future-side crease C | The disk z=0, t=-sqrt(a²+|w|²), with intrinsic area 2*pi*a*(1-a); not a regular past–future NN joint and not assigned its weight by analogy |
| Gamma | Circle z=0, t=-1, |w|=sqrt(1-a²), at the crease/floor/SN contact; its moving overlap contacts are included in LA3–LA7 |
| Two tips | Distinct actual future tips; no tips occur in L. #134 §5 proves the all-partner normalized tip-neighborhood bound 4*pi*||phi||*delta² for fixed 0<delta<a |

The entire frontier and no lateral wall were proved in TT1 §2. For C and
Gamma we do **not** delete neighborhoods on a measure-zero argument. LA9–LA10
and (LB1) include their entire response. They prove that the complete action
needs no additional **net** stratum coefficient beyond J_U for this fixed
region. The nonzero opposite crease fluxes in LA10 were retained before
cancellation. This does not assert that any separately weighted crease,
corner or generator sector has zero limit. Smooth source partitions on the
caps retain MA11's generator derivatives; their total cancels only in the
full finite sum. Lens partitions recombine at finite density before LA9.

No logarithmic normal scale or continuum corner functional is imported.
Positive affine rescaling of each marked null generator leaves the induced
screen/crease areas and the complete action unchanged. The marks and their
nonzero scalar products are exactly those in TT1 §2.

## 4. Separate original-law expectation transfer

U is nonempty and open, bounded by -11/10<t<0 and |x|<a+11/10, with finite
positive four-volume V. Smooth/Lipschitz boundary graphs have zero volume.
Its restricted Lebesgue measure is finite and atomless. The ambient closed
causal relation is closed, and the exclusive interval relation is measurable.
Section 2 establishes containment for **all** related endpoints in U.
These facts discharge `BoundedCausalRegion`'s actual measurable/bounded/
closed-interval fields; no new compiled instance is asserted.

Construct the original law independently: draw a Poisson cardinality with
mean rho*V, then independent positions with law `volume.restrict(U)/V`.
Simplicity follows from atomlessness. Count ordered distinct related pairs
with exactly k **other** points in the closed interval. With C4=4/sqrt(6),

```math
\begin{aligned}
A^{\mathrm{disc}}_\rho(C)
 &=\frac{C_4}{\sqrt\rho}(N-L_0+9L_1-16L_2+8L_3),\\
|A^{\mathrm{disc}}_\rho(C)|
 &\le\frac{C_4}{\sqrt\rho}[N+16N(N-1)],\\
\mathbb E[L_k]&=\rho^2\int_U\int_{U\cap J^+(p)}
 e^{-c\rho\sigma^2}\frac{(c\rho\sigma^2)^k}{k!}\,dq\,dp.
\end{aligned}
\tag{LB3}
```

The second inequality and finite Poisson factorial moments prove integrability.
Reduced two-point Campbell–Mecke proves the last line with the true restricted
interval rate. Containment identifies that rate with c*rho*sigma² for timelike
pairs; removing the two endpoints changes no volume. Null pairs and the
diagonal are product-volume-null by Fubini on each translated null cone and
singleton, but null order remains in the discrete definition. Combining the
actual four factorial-weighted layers gives **exactly** K, and thus

```math
\begin{aligned}
\mathbb E_{\Pi_{\rho,U}}[A^{\mathrm{disc}}_\rho]
 &=\mathcal A_\rho(U)\quad(\rho>0),\\
\lim_{\rho\to\infty}\mathbb E_{\Pi_{\rho,U}}[A^{\mathrm{disc}}_\rho]
 &=J_U.
\end{aligned}
\tag{LB4}
```

The first line is a genuine finite-density equality with separately proved
hypotheses; the second applies the already established (LB2). It is not a
definition of expectation or an interchange with a sample-wise limit.
`FiniteSprinkling.interval_rate`,
`BoundedCausalRegion.integrable_discreteBDGAction`, and
`BoundedCausalRegion.expectedBDGAction_eq` are the existing checked counterparts.
Their written U specialization is new; their checked scope is not enlarged by
this note. One can likewise transfer the proved L theorem using its actual
containment, but it is not needed to infer (LB4) by coupling unrelated laws.

## 5. Acceptance, required residual coverage and verification

| #155 requirement | Receipt |
| --- | --- |
| Actual TT-A, caps and exact finite-density identities | §1 source pin; (LB1), TT2/TT5/TT11; #84 instantiated at translated H |
| Point once, all ordered partners and complete U | §2 indicator/layer proof; no componentwise bilocal additivity |
| Independent target and every stratum/coefficient | (LB2), §3 inventory; complete-action proof of no extra net term, no localized-vanishing shortcut |
| Deterministic before expectation | §3, followed by the separately discharged law/order/volume proof (LB3)–(LB4) |
| Fixed quantifiers, normalization and remaining regimes | §1 and residual table below; no rate, varying geometry or sample-wise claim |
| Tests and parent handoff | `test_two_tip_assembly.py`, full-density U/cap/lens regressions; this source-backed ledger is the #81 handoff, not automatic issue completion |

| Required #90 / #24 branch not exhausted by this theorem | Native residual owner |
| --- | --- |
| Arbitrary regular SN and past–future NN boundaries, beyond the existing cone/diamond/cap results | #156; verify the selected order, independent screen target and full producer before reuse |
| Same-side seams, tips and higher intersections beyond exactly TT1's C/Gamma/two tips | #156; their normalization is not assigned zero by this theorem |
| Other dimensions, including 2D counting normalization and higher-dimensional critical terms | #156 with #149's actual coefficient APIs; the G-SS positive theorem does not cover null faces |
| Curved null generators, cut/caustic contacts, metric volume and general atlases | #156 coordinated with #81's separate curved spacelike owner; #150/#151's G-SS results cannot simply be instantiated here |
| Non-convex ambient restrictions, if selected by a further approved contract | #156 must distinguish genuinely restricted volumes and intrinsic versus ambient order; no flat-volume inheritance |
| Independent human scrutiny, provenance and justified future formalization | #94/#86; these written results are not compiled analytic theorems |

Noncompact tails, finite-regularity relaxation, degenerating angles/rays,
density-dependent geometry, rates, sample-wise convergence, timelike
Conjecture 2 and unrelated extra strata are **not** added to this task.
The unresolved required branches above remain open: no finite collection of
successful pilots or conditional estimates completes #156/#81/#24.

The diagnostics compare direct union overlap to the cap-minus-lens identity,
including opening/closing/disconnected translated sections; combine four
positive layer integrals with the real factorials; preserve common-to-exclusive
pairs and point allocation on actual finite configurations; and check the
independently computed areas. They are not certified integration bounds or
proofs of asymptotics. The written argument is (LB1)–(LB4), consuming the actual
TT-A proof, not numerical extrapolation.

No Lean/checker/dependency/build input changes. Applicable validation is the
Python suite, symbolic/reproduction checks, Markdown lint and its tests,
GitHub browser rendering, exact-head CI and one bounded feedback pass. No new
Lean audit or human review is claimed. No merge, deployment, agent launch,
issue closure, or silent change to #24's completion criterion is authorized.
