# General null/mixed theorem attempt: construction failure dossier

**Outcome C — no general theorem or new complete-action obstruction obtained.**
This attempt starts at `4da24490dfca7ab80f397563b3ef6dbaa44e902f` on draft
#184, still targeting `issue-81-general-coverage`. It does not advertise a
new sufficient criterion, refined example, or exact identity as closure.
The candidate was recorded before repository implementation; the three
attempts below explain why its geometric construction has not been discharged.
This is **not a proof that such a theorem is impossible**.

The original #156 body and all four body-history entries, #81's fourteen
and #24's ten entries were checked against the current contracts. #81's
oldest provisional obstruction gate does not replace its subsequent corrected-
general-theorem obligation or #24's original completion criterion. The actual
#83/#84/#134 sources were read, not inferred from closed issues. The sole
original-item closure crosswalk remains [required coverage §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).
No new acceptance table is introduced here.

## 1. Best candidate before implementation — and its unfilled definition

**Proposed geometric construction theorem, not a theorem proved here.**
Fix an integer d>=2 and a smooth time-oriented globally hyperbolic ambient
spacetime. Consider a nonempty precompact open region M=F intersect P, with
F an open future set and P an open past set, in the original null/mixed
boundary regimes. Its actual closed ambient intervals are contained in M
by transitivity. Use the actual metric volume, both endpoint measures and
canonical action. Do not require a finite number of minimizing routes,
finite contact type, a nondegenerate cut locus, orientability, or a common
tip. Retain the actual boundary masks, including required higher, merging
and accumulating contacts and singular ends. The future/past presentation
is an organization of causally convex regions, not a new graph restriction:
for any open order-convex M, `I+(M) intersect I-(M)=M`. One inclusion follows
from openness, the other from order convexity between two points of M.
This does not identify an intrinsic-only order with an ambient restriction.

The proposed conclusion is a **construction from the jointly measured causal
contact geometry** of a nonlocal scale response, with a complete o(1) error
for the unchanged action. On regular strata it must restore the independently
normalized half-curvature, variable SS-angle and SN/NN screen contributions;
it must derive, rather than set to zero, additional singular contributions.
It may have finite, fractional, logarithmic or nonclassical scale dependence.
Where a separate regular target is not defined, the construction must specify
the whole response instead of assuming such a decomposition is integrable.
No new degenerating-geometry or noncompact uniformity is required.

The completely explicit mandatory test class is **every**
`M_T={|t|+|z|<T/2} x Y`, with metric `dt²-dz²-h_Y`, every closed smooth
Riemannian Y of dimension d-2 and every fixed T>0. There the proposed conclusion
has the unambiguous form

```math
\begin{aligned}
\mathcal A_{\rho,d}(M_T)
 &=\frac{T^2}{4}\int_Y R_Y\,d\mu_Y+2\mathrm{Vol}(Y)\\
 &\quad+\Gamma_Y(\rho,T)+o(1).
\end{aligned}\tag{GA1}
```

**The unfilled definition matters:** no independent universal construction of
Gamma was obtained. The candidates tested below are precisely attempts to
supply one. Merely asserting that some Gamma exists is vacuous: choosing the
original action minus the displayed local term would satisfy it. That choice,
the original complementary kernel integral, its filtered primitive, and an
assumed limiting distribution are all excluded. Consequently GA1 is a precise
unresolved output on an explicit geometric class, **not a fully specified
corrected theorem**. The wider construction proposal is not promoted to one
by naming “contact geometry.” This definitional failure, as well as the
missing estimate, is part of outcome C.

A genuine theorem on a smaller geometric class can have no asymptotic
hypothesis and still not meet #156. Conversely, a theorem saying “given an
independently constructed trace with a critical remainder, assembly follows”
is only a transfer theorem until those geometric inputs are produced. Neither
would resolve the original contract here. A suspension theorem alone would
also leave the required nonproduct/non-common-tip and singular-end regimes.

## 2. Complete observable and the common structure actually justified

Let V(p,q) be the whole physical exclusive-interval volume for the selected
closed order. Endpoint removal is continuum-null, not a change of discrete
counts. With b=1+2/d and the original constants,

```math
\begin{aligned}
P_\rho(M)&=\int_{p\preceq q\in M}K_d(\rho V(p,q))\,d\mu(p)d\mu(q),\\
\mathcal A_{\rho,d}(M)&=a_d\rho^{2/d}\mu(M)-\beta_d\rho^bP_\rho(M).
\end{aligned}\tag{GA2}
```

Choose one compatible positive physical temporal cutoff before varying rho.
Its two masks sum to one on **every** ordered pair; point belongs to short
once. Every ordered endpoint-partition product remains, including both cross
orders and the both-singular sector. Form physical interval unions before K.
Auxiliary rest gaps, path subdivisions and contact collars below do not change
that cutoff. Finite-density boundedness licenses Fubini, not uniform passage
to the density limit.

The common structure is **joint pushforward followed by signed matching**,
not a universal local conservation law or singularity normal form:

- Local geometry produces kernel-null powers and logarithmic partners. The
  latter restore point, curvature and screens after the signed integration.
  SM's four actual moments fix homogeneous data; the differentiated IN8
  equation cannot fix them.
- The flat fold changes the jointly measured endpoint/contact density while
  ambient curvature is zero and individual lifted diamonds are flat. Its fifteen-sector matching
  leaves a finite charge in 5D and growth in higher dimensions. Thus a
  curvature-only or conjugate-only contact object is inadequate.
- Spherical focusing changes the conditional intermediate-point geometry.
  Its radial resolution has a different scaling and retains a secondary
  transition. The surviving coefficient includes both matching tails.
- In the successful common-tip cases, integration of **all** partners first
  yields a signed profile with a proved mass and tail. That extra identity,
  not zero-volume singular sets, makes the geometric boundary flux possible.
  The low-dimensional suspension cancellations use their own circle/contact
  geometry, not an all-metric version of that identity.

### Dependencies audited for these uses, not independently accepted

The source inspection checks the following decisive steps. It is not a new
end-to-end certification of every earlier proof.

| Source actually consumed | Check and exact boundary of reuse |
| --- | --- |
| IN4–IN7; CT3–CT4 | Flat-block boost acts on the entire interval; the physical intermediate point is counted once. The Abel derivative gives CT3 by integration from opening. Only its smooth prefactor is Taylor-replaced; the longitudinal square root at both tips remains exact. A contained terminal short diamond gives the uniform excess lower bound. The resulting normalized **difference** tends to zero, not the original complement. |
| SM2–SM5; S1–S13 | Whole-interval locality precedes the smooth rescaled metric/ratio. SM uses polar power d-4+j, not the full spatial-cone power. Moving-diagonal contacts and logarithmic weights survive interpolation. Signed radial integration gives odd-dimensional tails -5 and -3; the divergent curvature power-three moment stays truncated. These establish the stated product-origin scope, not a general null-boundary short theorem. |
| SM6–SM9; K1–K8; FL5–FL9; CT6 | Finite lifts follow from this quotient and width window only. The null cap replaces the slab cap. Both fold branches/centers, inactive strips and all fifteen sectors remain. The overlap upper bound covers higher multiplicity at both tips. CT6's angular tangent differentiates the linear discriminant on each incident face; straightening occurs before bounding the integrable singularity. Its extra remainder upgrade is 6D only. |
| IU3–IU8 | The actual two-distance Jacobian gives a radial error of order r; only the opening collar needs four angular derivatives. The physical spectator cap is C4. The continuation line lies above the action-critical exponent and below the proved radial boundary. Neither a fourth derivative through the seven-halves transition nor a discarded meridian tail is used. This geometry does not describe a general cut locus. |
| CS2–CS10 | The combined homothety/boost is bounded, unlike the boost alone. The actual common-tip fibre and positive smooth conformal density are essential. The simple upper pole is retained; the beta zero times the continued pole supplies a nonzero profile mass. Curvature scaling is used before the tail estimate. Intrinsic containment supplies none of these additional analytic identities. |
| #83/#84 and #134 | The exact source-to-tip kernel identity needs the whole fibre, stronger than containment. TT's valuation removes exclusive-to-exclusive pairs by their particular causal geometry and retains the intersection lens. It is not general bilocal additivity. |
| GT5–GT12; CT7–CT9 | Count-free clock control, coarea and first-coefficient limits do not provide critical control. CT's three u-integrations retain lower anchor data and use cubic closing, not a vanishing third derivative. Its weak-test countercontrol is abstract, not a spacetime example. |

No contradiction in these limited uses was identified. Their weakest
unverified generalization is not a kernel constant: it is passage from actual
joint contact geometry to a completely matched critical response. #94/#86
scrutiny, existing Lean coverage and diagnostics remain different evidence.

## 3. Attempt I: compact minimizing-path geometry instead of route lists

For a connected positive-dimensional closed Y choose a fixed r below its
injectivity radius and an integer N with `diam(Y)/N<r/2`. Let Q_N(y,y') be
the compact set of chains `x_0=y,...,x_N=y'` with consecutive distances at
most r. The squared-distance functions are smooth on a neighborhood of this
set. Define the finite-dimensional energy and its complete minimizing set by

```math
\begin{aligned}
E_N(x_0,\ldots,x_N)&=N\sum_{i=1}^N d_Y(x_{i-1},x_i)^2,\\
\min_{Q_N(y,y')}E_N&=d_Y(y,y')^2,\\
\mathcal Z_N&=\{(y,x_1,\ldots,x_{N-1},y'):
                 E_N=d_Y(y,y')^2\}.
\end{aligned}\tag{GA3}
```

**Justification.** Triangle inequality and Cauchy–Schwarz bound E_N below
by the endpoint distance squared. Equal subdivisions of any minimizing
geodesic attain equality and have all steps strictly below r/2. Equality
requires equal step lengths and a length-minimizing concatenation. A corner
would shorten inside a normal neighborhood, so this concatenation is a
geodesic. Thus GA3 represents **all** minimizers, even when they form a
continuum. Compactness, positive injectivity radius and existence of a
minimizer follow for each fixed closed Riemannian manifold; no branch
selection, finite number of critical points or nondegenerate Hessian follows.
Disconnected components are treated separately; they have no cross pairs.

This is a genuinely geometric candidate input: the near-minimum energy
family with its endpoint/evaluation maps. But its chain-volume measure is
**not** the physical intermediate-point measure. Integrating over minimizers
would count routes, not physical x; isolated minimizers even have zero chain
volume. Therefore that attractive replacement is rejected before applying K.

To retain the correct measure, write ell=d_Y(y,y'),
`e(x)=d_Y(y,x)+d_Y(x,y')-ell`, and
`xi(x)=d_Y(y,x)-d_Y(x,y')`. For h>0 and Borel B, the thin-triangle
profile measure is

```math
\begin{aligned}
\lambda^h_{y,y'}(B)&=h^{-(n-1)/2}
 \int_Y\mathbf1_{e(x)\le h}
       \mathbf1_{(e(x)/h,\xi(x))\in B}\,d\mu_Y(x),\\
\frac{W_{N_0}(\ell+h;y,y')}{h^q}
 &=\int\int_a^1\sqrt{s-a}\sqrt{(\ell+hs)^2-\xi^2}
       A_{\ell,N_0}(hs,ha)\,ds\,d\lambda^h_{y,y'}(a,\xi),\\
 n&=d-2,\qquad q=d/2,\qquad N_0=\lfloor d/2\rfloor.
\end{aligned}\tag{GA4}
```

Use CT's fixed positive-length collar, where W_(N_0) denotes its auxiliary
phase; the subdivision count N in GA3 is unrelated to N_0. The inner
integral is zero for a>=1.
GA4 follows directly by `t=hs`, `e=ha` in CT3. The factor h^(3/2) from the
Abel integral combines with h^((n-1)/2) to give h^q. The full physical
longitudinal factor is still present at both tips. CT4 justifies this phase
replacement at complete critical order.

**Attempted extraction.** At a unique nonconjugate minimizer, the transverse
quadratic index form determines the leading tube profile. Try replacing
lambda^h by those tangent profiles and integrating over endpoints. This
fails to supply a proof for two separate reasons:

1. The almost-everywhere profile omits endpoint neighborhoods whose scale
   changes jointly with h. At antipodal endpoints of a round sphere the
   distance excess is zero along the entire minimizing family; the ordinary
   single-tube normalization is not uniform there. The flat folded endpoint
   map has a different failure despite no conjugate points. Their complete
   SM/IU responses show that discarding those neighborhoods changes answers.
2. Even a correctly integrated **leading** profile is not a critical error
   bound. On CT's complement the positive sublevel bound is of order v^(1/q).
   Its kernel response has normalized size O(rho). A relative o(1) replacement
   yields at best o(rho) by that estimate, not o(1). CT4 worked because its
   relative error had a proved extra power greater than one in volume. No
   comparable joint estimate for replacing lambda^h has been derived.

**Attempted repair by resolving GA3.** This converts infinitely many paths
into a compact finite-dimensional optimization problem, but not into finite
type. A smooth function on a compact manifold can have nonisolated minima,
flat contact and accumulating critical points. No assertion is made that
arbitrary such functions are realizable as geodesic energies: that would need
another proof. The point is that the proved smoothness/compactness of E_N
alone does not establish the needed hypothesis. The sphere already violates
nondegeneracy, and the quotient violates a single active minimum. A theorem
about analytic resolution cannot be applied to an arbitrary smooth metric;
a constant-rank pushforward theorem cannot be applied at a rank loss.
No such external theorem is imported here.

Keeping the entire h-dependent profile law in GA4 is exactly the nonlinear
conditional observable again, so it is **not Gamma**. Replacing it by only
regular tangent/index data is uncontrolled. No intermediate independent
contact extraction with a complete remainder was obtained. GA3/GA4 record
the failed construction, not new asymptotic coverage or a claimed universal
power/log expansion.

## 4. Attempt II: conservation and valuation of the complete signed response

The correct transport variable is IN2's point-plus-all-past-partners response,
not a selected long sector. For M=F intersect P its fibre is
`F intersect I-(q)` up to null boundaries. In the conformal 3D common-tip
case CS's derived signed profile mass is the derivative of conformal ray
length. Integrating that mass produces the outer screen and controls the
actual cusp ends. This suggests a conservation law for the whole response.

**Attempted extension:** transport a geometric ray current through all cuts
and then pair it with the real cap. There are two missing operations, not an
unknown integration constant. A ray current counts propagation routes, whereas
V counts the union of physical intermediate points. At cuts, a multiplicity
current is not that union. Also the CS mass proof uses a faithful reference
diamond and its density family; transitivity only preserves the fibre.
There is no derived intrinsic replacement for that mass or its tail.
The flat charge refutes a law with only local curvature/screen sources, and
NA3's width dependence rules out the proposed additive local-finite-jet repair
of the focal term. It does not rule out a genuinely nonlocal current.

One can always define a flux by integrating the actual response. CT7 does
this honestly as a finite-density identity, with all four lower moments.
It is not an independent geometric conservation law. IN8 still annihilates
both local homogeneous modes. Taking a smooth-test limit before the real
cap also fails as an inference: CT9's abstract concentration has a nonzero
cubic-cap pairing despite convergence to zero on smooth tests. Conversely,
IN3's actual diamond excludes demanding bounded total variation of the
unsummed response. Thus neither standard weak-measure compactness nor simply
solving the width equation supplies the geometric flux.

**Valuation repair tested:** cover F by chronological futures of points,
apply the successful common-tip theorem to each, and use inclusion–exclusion.
For finite such covers the pair identity is legitimate only with the full
intersection fibres and the same ambient phase. Those intersections are
generally not single-tip diamonds, exactly as #134's lens demonstrates.
For a countable cover, fixed-density dominated convergence has a bound that
grows with rho; it does not pass the normalized limit. A theorem on arbitrary
physical intersections and their complete signed remainder is missing, not
an algebraic inclusion–exclusion formula. Defining the flux using that
unevaluated family would again rename the observable. This route closes
neither general ends nor non-common-tip contacts.

## 5. Attempt III: operator organization preserving conditional correlations

A spectral route must first reproduce the **actual** interval, not a sum of
wave rays. For Y define the bounded distance-ball operator B_r on L2(Y), with
kernel `1_(d_Y(y,x)<r)`. In the product rest frame a physical time/z slice of
the interval is an intersection of two such balls. Consequently

```math
\begin{aligned}
W(u;y,y')&=\int_0^u\int_{-\min(t,u-t)}^{\min(t,u-t)}
 (B_{\sqrt{t^2-z^2}}B_{\sqrt{(u-t)^2-z^2}})(y,y')\,dz\,dt,\\
\int_{Y^2}W(u;y,y')^k\,d\mu_Y(y)d\mu_Y(y')
 &=\int_{Y^{k+2}}\prod_{j=1}^k
       H_u(y,x_j,y')\,d\mu_Y(y)d\mu_Y(y')\prod_{j=1}^k d\mu_Y(x_j),\\
H_u(y,x,y')&=\int_{\mathbb R}
 [u-\sqrt{d_Y(y,x)^2+z^2}-\sqrt{d_Y(x,y')^2+z^2}]_+\,dz.
\end{aligned}\tag{GA5}
```

Here k is a positive integer. Tonelli proves both identities; the ball
composition integrates physical x once. The time/z domain is the actual
one. This organization retains correlations: every factor in the second
line shares the **same two endpoints**, unlike averaging triangles before K.
It introduces no new geometry or asymptotic claim.

**Spectral-functional-calculus test.** The product in K(rho W) is pointwise
in the kernel entries, not operator composition or an operator exponential.
Already the cubic moment in GA5 has two shared endpoints and three separate
intermediate points, not the three-endpoint cyclic trace of a cubed operator.
The quadratic moment can equal a Hilbert–Schmidt norm; that exceptional
identity does not extend to all powers. Diagonalizing an operator therefore
does not diagonalize this observable.

There is a second geometric obstruction to the simplest heat-kernel proposal.
On a connected Y, any scalar spectral multiplier of its Laplacian sends the
constant function to a constant. But B_r sends it to the volume of a ball
centered at y. The normal volume density integrates to
`omega_n r^n [1-R_Y(y) r²/(6(n+2))+O(r³)]`. Whenever scalar curvature varies,
this is nonconstant for small r. Thus B_r is not, in general, a scalar
Laplacian multiplier. This is a direct geometric check of a proposed identity,
not an action counterexample or a new selected spacetime calculation.

**Correlation-hierarchy repair tested.** Expand the exponential and retain
every moment in GA5. At each fixed rho, bounded W justifies the series, but
an absolute sum is bounded by a polynomial times `exp(rho W_max)`.
Finite-order truncation is not a high-density approximation on the whole
domain, and summing the whole hierarchy gives the original observable.
A heat-trace local expansion supplies neither these conditional moments nor
their uniform resummation. A wave-parametrix route would additionally have
to derive the union/minimum rule and justify its singular compositions at
non-clean contacts. Neither a clean-intersection hypothesis nor the needed
remainder has been established from the admitted smooth geometry. No heat,
wave, Tauberian or resolution theorem is invoked with unchecked hypotheses.
This attempt obtains no independent spectral/flow correction.

## 6. Exact blocker and what a successful expert result must add

The three attempts fail at different steps: a compact smooth minimizing
family has not been resolved at critical order; a geometric signed flux has
not been constructed for union fibres and actual caps; an operator spectrum
does not preserve the required conditional nonlinear correlations. These
are not proofs that all other approaches fail. In particular no admitted
geometry with nonclassical asymptotics, no nonexistence of a general theorem,
and no new failure of GA1 has been established here.

**Concrete expert result needed for the suspension attack:** from the
measured near-minimum geometry in GA3 and the **physical** conditional
thin-triangle measures, construct an evaluable geometric contact model,
independent of K and of the action limit, that accounts jointly for endpoint
approach, both tips, coincident/merging/accumulating minimizers and actual
closing. Prove that its response differs from CT's complementary cap pairing
by o(rho^(-b)) before pair normalization, with both matching tails. Recover
SM's fold measure and IU's different focal response and the genuine zero
complements as consequences, not as stipulated coefficients. No separate
sector trace, finite expansion or CT8 norm is prescribed. This is an
unsolved geometric producer problem, **not** a claimed available external
result or an analytic condition added to admissibility.

For **original #156**, a product result must still be followed by the actual
time-dependent two-front version: whole clock unions with their physical
endpoint masks and non-common-tip intersection fibres, including all required
singular ends. SM's origin theorem is product-specific; S30's full boundary
theorem is spacelike. Neither licenses general null short/singular assembly.
A successful proof must determine all local and singular terms independently,
restore the full signed deterministic observable, and only then use the
original-law Mecke equality. The finite-density bridge itself is not blocked,
but **no new general expectation asymptotic** follows without that producer.

### Short human-readable proof spine and weakest dependencies

1. The original action uses a nonlinear function of a physical union, with
   both endpoint measures and point once. No route multiplicity is its input.
2. The source-audited successes have different jointly measured contacts.
   They exclude local-only and conjugate-only corrections, not general
   nonlocal corrections.
3. CT removes the elementary Abel-factor error. GA3 then tests whether a
   compact minimizing diagram supplies the remaining extraction; it does
   not establish finite type or the needed joint error. Transport and
   spectral reorganization do not bypass this missing information.
4. **No decisive new inference from geometry to critical asymptotics was
   proved.** The decisive diagnosis is the unfilled construction, not a new
   transfer identity. The elementary energy/ball identities need only compact
   Riemannian geometry and Fubini. The asymptotic constraints additionally
   depend on the scoped SM/CT/IU/CS proofs audited above; they remain written
   claims requiring scrutiny, not independently accepted premises.
5. Therefore neither A nor B is delivered. **C / STILL BLOCKED** is the only
   justified disposition. Prior proved scopes and complete obstructions are
   preserved; no new theorem coverage is claimed.

A user scope decision is needed **only if** the desired endpoint changes to
accept the existing restricted package, or to commission a narrower geometric
class (for example, an analytic/controlled-contact research problem) instead
of original acceptance. Such a decision would not itself prove that narrower
theorem. No decision is requested as a condition for continued research and
none is enacted. Exhaustive classification is not added to acceptance.
#156 retains the null producers; #81 the corrected general consumer; #177
and #94/#86 remain unresolved, and #185 remains deferred.

This delivery changes documentation only. No new example, numerical module,
probability/action API, Lean/checker input, dependency or workflow is added.
Validation checks document integrity and unchanged diagnostics, not the
missing geometric theorem. No fresh Lean audit, independent human acceptance,
agent/reviewer launch, merge, deployment or issue closure is claimed.
