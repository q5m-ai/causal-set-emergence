# The fixed flat 4D mixed expected-action theorem (#84)

**Written proof, with executable regressions; not a new Lean-checked theorem
or an independently reviewed result.** This assembles exactly the class
selected by [#90, §6](general-contract.md#6-selected-first-flat-4d-mixed-pilot-for-83--84)
and the full-partner identity from [#83](null-mixed-estimates.md). In particular,
the nonlocal contribution is integrated **exactly**, not assumed to vanish.
The deterministic theorem below precedes its separate Poisson transfer.
Neither the general null/mixed milestone nor #24 is completed by this pilot.

The source-to-tip strategy is already in [first-attempt §3](first-attempt.md#3-first-class-one-null-cone-future-boundary).
No novelty claim is made. The new assembly discharges the geometric hypotheses,
accounts for the complete frontier and all source/partner partitions, identifies
the independent induced area, and supplies the actual expected-action statement.

## 1. Independent definitions and theorem

Use flat Minkowski space with signature $(+---)$ and ordinary four-volume.
Fix a smooth function $`H:\mathbb R^3\to\mathbb R`$ and constants
$`T=H(0)>0`$, $`0\le\lambda\lt1`$ such that
$`|H(x)-H(y)|\le\lambda|x-y|`$ globally. Geometry is fixed as density varies.
There is **no** action identity, overlap jet or limit in these hypotheses.
Set

```math
\begin{aligned}
M_H&=\{(t,x):-H(x)\lt t\lt-|x|\},&
D_H&=\{x:|x|\lt H(x)\},\\
J_H&=\{(-|x|,x):H(x)=|x|\},&
m&=\frac{T}{1+\lambda},\qquad B=\frac{T}{1-\lambda}.
\end{aligned}
\tag{MA1}
```

The target $`\mathcal J_H=\int_{J_H}dA_g`$ uses the positive induced metric
$`-g|_{TJ_H}`$, **not** an action-defined measure or ambient Euclidean spacetime
area. Its well-definedness and value are proved in §2.

For $`\rho>0`$ let $`\Pi_{\rho,H}`$ be the finite Poisson law of intensity
$`\rho\,dp|_{M_H}`$. For a simple finite configuration $`C`$, let $`L_k(C)`$
count ordered distinct pairs $`p\preceq q`$ with exactly $`k`$ other sample
points in the closed ambient interval $`I(p,q)`$. Null relations are included;
only the two marked endpoints are excluded from the count. Define

```math
\begin{aligned}
A^{\mathrm{disc}}_\rho(C)
 &=\frac4{\sqrt{6\rho}}\,[\#C-L_0(C)+9L_1(C)-16L_2(C)+8L_3(C)],\\
K(z)&=(1-9z+8z^2-4z^3/3)e^{-z},\qquad c=\pi/24,\quad C_4=4/\sqrt6,\\
\sigma(p,q)&=(q_t-p_t)^2-|q_x-p_x|^2,\qquad \sigma(p)=\sigma(p,0),\\
\mathcal A_\rho(M_H)
 &=C_4\sqrt\rho\left[|M_H|-\rho\int_{M_H}\int_{M_H\cap J^+(p)}
 K(c\rho\sigma(p,q)^2)\,dq\,dp\right].
\end{aligned}
\tag{MA2}
```

These are the repository's unsmeared minimal-layer normalization, finite-order
observable and `continuumMean`; the expectation is **not** defined by the last
line. The probability law and integrability are justified separately in §5.

**Theorem (written).** For every such fixed $`H`$, the open region is nonempty,
bounded, measurable and ambient-causally-convex, with exactly the strata in §2.
For every positive density and in the density limit,

```math
\begin{aligned}
\mathbb E_{\Pi_{\rho,H}}[A^{\mathrm{disc}}_\rho]
 &=\mathcal A_\rho(M_H)
 =C_4\sqrt\rho\int_{M_H}e^{-c\rho\sigma(p)^2}\,dp,\\
\lim_{\rho\to\infty}\mathcal A_\rho(M_H)
 &=\mathcal J_H,\qquad
\lim_{\rho\to\infty}\mathbb E_{\Pi_{\rho,H}}[A^{\mathrm{disc}}_\rho]
 =\mathcal J_H.
\end{aligned}
\tag{MA3}
```

This proves unit mixed-joint weight for this single-cone class. It is not a
small-angle limit or a limit of spacelike faces becoming null. Curvature is
identically zero, so there is no bulk-curvature term to identify here.

## 2. Region, complete strata and independent target

### Radial domain and compact closure

For each unit vector $`\omega`$, the smooth function
$`r-H(r\omega)`$ is strictly increasing on $`r\ge0`$, with derivative at least
$`1-\lambda`$. It begins at $`-T`$ and tends to infinity. The intermediate
value and implicit function theorems give a unique smooth positive root
$`R(\omega)`$. The bounds $`T-\lambda r\le H(r\omega)\le T+\lambda r`$
give $`m\le R\le B`$. Thus $`D_H`$ is the radial domain $`0\le r\lt R(\omega)`$,
including the origin, and its closure has $`0\le r\le R(\omega)`$.
No global positivity of $`H`$ outside that domain is required.

The defining functions in (MA1) are continuous, so $`M_H`$ is open and Borel.
It contains $`(-T/2,0)`$, hence has positive volume. In the region,
$`r\lt B`$ and $`-B\lt t\lt0`$, since $`H(x)\le T+\lambda r\lt B`$ when
$`\lambda>0`$ (and $`H=T=B`$ when $`\lambda=0`$). In particular its closure
is compact and its volume is finite. Continuity gives one inclusion in

```math
\begin{aligned}
\overline{M_H}&=\{(t,x):x\in\overline{D_H},\ -H(x)\le t\le-|x|\},\\
\partial M_H&=\Sigma_-\cup\Sigma_+,\\
\Sigma_-&=\{(-H(x),x):x\in\overline{D_H}\},\qquad
\Sigma_+=\{(-|x|,x):x\in\overline{D_H}\},\\
\Sigma_-\cap\Sigma_+&=J_H.
\end{aligned}
\tag{MA4}
```

For the reverse closure inclusion, over an interior spatial point approach
either time endpoint by strict intermediate times. At a joint point first
approach radially from below its positive root, then use intermediate times;
both endpoints converge to the joint time. The tip is obtained with $`x=0`$
and negative times tending to zero. This also proves the frontier assertion:
points strictly between the graphs over $`D_H`$ are interior, and every other
point in the displayed closure is on one of its bounding graphs.

The disjoint strata are the lower face $`\Sigma_-\setminus J_H`$, the upper
face $`\Sigma_+\setminus(J_H\cup\{0\})`$, the mixed joint $`J_H`$, and the
single future tip $`0`$. The point $`(-T,0)`$ is a smooth point of the lower
face, not another tip. There is no lateral wall: the two time endpoints
coalesce at the entire spatial boundary. There are no same-side creases,
additional corners or unlisted components. Both faces are compact; the lower
one is smooth with boundary, and the upper one is smooth except at its tip.
Fubini on their graph descriptions proves zero four-volume, including the tip.
Zero volume alone will **not** be used to discard a normalized contribution.

### Closed ambient intervals, not just intrinsic causality

Write $`F(t,x)=t+H(x)`$. For $`p\preceq z`$, the closed causal inequality gives

```math
\begin{aligned}
F(z)-F(p)&\ge(z_t-p_t)-\lambda|z_x-p_x|
 \ge(1-\lambda)(z_t-p_t)\ge0.
\end{aligned}
\tag{MA5}
```

If $`p,q\in M_H`$ and $`p\preceq z\preceq q`$, then $`F(z)\ge F(p)>0`$.
Also the triangle inequality gives
$`z_t+|z_x|\le q_t+|q_x|\lt0`$. Therefore $`z\in M_H`$.
This proves containment of the **entire closed ambient interval**, including
null segments and marked endpoints. If the endpoints are unrelated the
interval is empty. Thus the isolated restricted interval volume equals the
ambient one; no substitute restricted-volume model is needed. Intrinsic
causality also agrees here: the causal line segment between any related
endpoints lies in that interval and hence in the region.

More strongly, (MA5) proves, for each $`p\in M_H`$,

```math
\begin{aligned}
M_H\cap J^+(p)&=J^+(p)\cap I^-(0),\\
\bigl(M_H\cap J^+(p)\bigr)\mathbin{\triangle} I(p,0)
 &\subset\partial J^-(0).
\end{aligned}
\tag{MA6}
```

Here $`I^-(0)`$ is the chronological past, while $`I(p,0)`$ is the closed
interval. The exceptional cone is a Lipschitz graph and volume-null. The tip
need not belong to $`M_H`$ for this source-to-tip integration identity; in
contrast the Poisson interval-rate argument in §5 uses two endpoints in
$`M_H`$, precisely as required by causal convexity.

### Smooth spacelike joint and its area

Away from the origin the spatial joint is the regular zero set of
$`H(x)-|x|`$: its radial derivative is at most $`\lambda-1\lt0`$.
Parameterize the actual spacetime joint by
$`\psi(\omega)=(-R(\omega),R(\omega)\omega)`$. It is an embedding, since
spatial radial projection recovers $`\omega`$. For tangent vectors $`v,w`$
to the unit sphere, $`\omega\cdot v=\omega\cdot w=0`$, so

```math
\begin{aligned}
-g(d\psi(v),d\psi(w))&=R^2(v\cdot w),\\
dA_g&=R^2d\omega,\qquad
\mathcal J_H=\int_{S^2}R(\omega)^2\,d\omega,\\
4\pi m^2&\le\mathcal J_H\le4\pi B^2.
\end{aligned}
\tag{MA7}
```

Both products of radial derivatives cancel against the time derivatives.
The induced metric is positive definite; the smooth compact joint therefore
has the stated finite, strictly positive area independently of the action.
The lower face has metric $`|v|^2-(\nabla H\cdot v)^2>0`$ for nonzero $`v`$.
The upper face is null. Their normals are the timelike/null pair in #83 §4,
with positive inner product, hence transverse at the joint. A rescaling of
the marked null normal changes neither this metric nor the observable.
In particular no logarithmic null-angle convention is an input to (MA7).

## 3. Complete signed cancellation and the global deterministic limit

The signed kernel is continuous; on the compact product of region closures
it is bounded at every fixed density. Thus all the bilocal integrals are
absolutely integrable **before** taking a density limit. The same holds after
multiplication by any bounded measurable source weight. Equations (MA6) and
`causalInterval_kernel_identity` in
[`TimelikeInterval.lean`](../formal/BoundaryDraft/TimelikeInterval.lean) give

```math
\begin{aligned}
\rho\int_{M_H\cap J^+(p)}K(c\rho\sigma(p,q)^2)\,dq
 &=1-e^{-c\rho\sigma(p)^2}\quad(p\in M_H).
\end{aligned}
\tag{MA8}
```

The theorem's timelike hypothesis holds because $`p\in I^-(0)`$.
This identity includes all macroscopic nearly-null partners. It is false to
replace the signed kernel by its absolute value. Integrating (MA8) cancels
the entire point-volume term and proves the deterministic equality in (MA3).
It is an exact alternative to a short/long asymptotic split, not an application
of the two-spacelike-face long-null theorem to a face outside its hypotheses.

For completeness a global convergence proof can now be given without assuming
an overlap jet or even a connected positive-sigma radial slice. Use polar
coordinates and the substitution $`t=-\sqrt{r^2+s}`$ on the open region.
The Jacobian is $`r^2/(2\sqrt{r^2+s})`$. Define

```math
\begin{aligned}
W_H(s)&=\int_{S^2}\int_0^B
 \mathbf1_{\sqrt{r^2+s}\lt H(r\omega)}
 \frac{r^2}{2\sqrt{r^2+s}}\,dr\,d\omega\quad(s>0),\\
W_H(0)&=\frac14\int_{S^2}R^2\,d\omega=\mathcal J_H/4,\\
\mathcal A_\rho(M_H)&=C_4\sqrt\rho\int_0^\infty e^{-c\rho s^2}W_H(s)\,ds.
\end{aligned}
\tag{MA9}
```

These are changes of variables in the actual integral. All indicators are
measurable, and the nonnegative reduced integrand permits Tonelli. For $`s>0`$
the radial domain is contained in $`(0,R)`$, so the integrand is bounded by
$`r/2`$ on $`(0,B)`$. Hence $`0\le W_H(s)\le\pi B^2`$, with zero weight
for $`s\ge B^2`$. For each direction and every $`0\lt r\lt R`$, the strict
inequality $`r\lt H(r\omega)`$ persists for sufficiently small positive $`s`$;
for $`r>R`$ it never holds. The exceptional moving endpoint has one-dimensional
measure zero in each radial fibre. Dominated convergence on the fixed product
$`S^2\times(0,B)`$ proves $`W_H(s)\to W_H(0)`$ from the right. This argument
does not assume monotonicity of $`H(r\omega)^2-r^2`$ or delete annular slices.

Finally set $`u=\sqrt{c\rho}\,s`$. The common integrable majorant is
$`\pi B^2e^{-u^2}`$, and

```math
\begin{aligned}
\mathcal A_\rho(M_H)
 &=\frac{C_4}{\sqrt c}\int_0^\infty e^{-u^2}
       W_H\!\left(\frac{u}{\sqrt{c\rho}}\right)\,du
 \longrightarrow\frac{C_4\sqrt\pi}{2\sqrt c}\,W_H(0)
 =4W_H(0)=\mathcal J_H.
\end{aligned}
\tag{MA10}
```

The point $`u=0`$ is immaterial. This proves the full deterministic target at
fixed geometry by global domination **after** signed partner cancellation.
It does not claim domination of the density-normalized absolute bilocal kernel.

## 4. Summability, transition strata, tips and cutoffs

There is no omitted remainder in (MA8)–(MA10). Nevertheless the partition
accounting is important: a source-local joint interpretation alone would be
wrong. Let $`\mathcal A_\rho[\phi]`$ denote (MA2) with a bounded first-endpoint
weight on both point and pair terms, **all partners still in the original
region**. For any finite bounded measurable partition $`\sum_i\phi_i=1`$,
finite-density absolute integrability proves exactly
$`\sum_i\mathcal A_\rho[\phi_i]=\mathcal A_\rho(M_H)`$.
The weights may overlap or have signs. This is not the sum of actions of
chart subregions; the latter loses cross-chart pairs and changes interval
counts.

For smooth weights on a neighborhood of the compact closure, #83 (NM5)–(NM8)
apply with finite bounds on the weights and their time derivatives. They give

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathcal A_\rho[\phi_i]
 &=\int_{S^2}R^2\phi_i(-R,R\omega)\,d\omega
   -\int_{S^2}\int_0^R r^2\frac{d}{dr}\phi_i(-r,r\omega)\,dr\,d\omega.
\end{aligned}
\tag{MA11}
```

Every term is absolutely integrable, because the sphere and radius interval
are bounded and the derivatives are bounded. The derivative is
$`-\partial_t\phi_i+\omega\cdot\nabla_x\phi_i`$. A finite partition on a
neighborhood of the closure has total derivative zero on each generator;
its joint traces sum to one. Consequently all transition-weight terms cancel
in the full finite sum, leaving (MA7). Compactness allows a finite chart cover;
no infinite atlas or unproved exchange with an infinite sum is needed.
Angular partitions transported along whole generators give the same conclusion
directly, even if their value at the spatial axis is defined only measurably.

The tip estimate is stronger than a measure-zero assertion. For $`|\phi|\le M`$
and a fixed spatial cylinder $`r\lt\delta`$, the reduced weight is bounded by
$`M\pi\delta^2`$. The Gaussian mass is four, so at **every** density

```math
\begin{aligned}
|\mathcal A_\rho[\phi\mathbf1_{r\lt\delta}]|
 &\le4M\pi\delta^2.
\end{aligned}
\tag{MA12}
```

This controls a true spacetime tip neighborhood and then tends to zero as
$`\delta\downarrow0`$. At fixed $`\delta\lt m`$, the unit cylinder's limit
is $`4\pi\delta^2`$, not zero. For a radial split at any interior radius,
the artificial endpoint terms have opposite signs and cancel. In particular
a collar $`R-h\lt r\lt R`$ contributes
$`\int[R^2-(R-h)^2]d\omega`$ in the density limit, while its complement
contributes $`\int(R-h)^2d\omega`$. The collar tends to zero as $`h\downarrow0`$;
discarding its complement is the rigorously obstructed route from #83, not
this theorem's argument.

If a partner cutoff $`0\le\chi(p,q)\le1`$ is used, keep both terms
$`S_\rho[\phi;\chi]`$ and $`N_\rho[\phi;\chi]`$ of #83 (NM11). Their exact
sum is the reduced Gaussian integral used here. No claim that the complement
$`N_\rho`$ vanishes separately is necessary or made. This retains all long
partners, tip sectors and artificial transition terms instead of hiding them
in an admissibility field.

**Limit order.** The proof (MA10) has only $`\rho\to\infty`$ with $`H,T,\lambda`$
and the entire region fixed; it introduces no geometric or partner cutoff.
For the optional #83 error estimate, first fix its positive proper-time-squared
split and take the density limit, then let that split decrease to zero. For
source cutoffs keep both complements through summation; tip removal may be
performed after the density limit using the uniform bound (MA12). No joint
collar, angle, null-face or dimension limit is interchanged with density.
No density rate or shrinking-partner-cutoff uniformity is asserted.

## 5. Actual Poisson law and exact expected-action transfer

Section 2 gives a finite, nonzero Borel volume $`V=|M_H|`$. Construct the law
by first drawing $`N\sim\mathrm{Poisson}(\rho V)`$, then, conditional on $`N`$,
independent points with distribution $`dp|_{M_H}/V`$, and forgetting their
labels. This is exactly the finite Poisson law used by the existing API.
Lebesgue atomlessness gives simplicity almost surely. The closed causal
relation and endpoint-excluded interval counts are measurable. Moreover

```math
\begin{aligned}
|A^{\mathrm{disc}}_\rho(C)|
 &\le\frac4{\sqrt{6\rho}}\,[N+16N(N-1)],\\
\mathbb E[N]&=\rho V,\qquad
\mathbb E[N(N-1)]=(\rho V)^2.
\end{aligned}
\tag{MA13}
```

The factor 16 bounds the magnitude of the weight of each ordered pair; the
four layers are disjoint, so their absolute weights need not be added.
This proves absolute integrability of the discrete observable before taking
its expectation, with no bounded-cardinality assumption.

For two endpoints in the region define the genuine restricted rate
$`z_{pq}=\rho\,|M_H\cap(I(p,q)\setminus\{p,q\})|`$. Reduced two-point
Campbell–Mecke and the interval Poisson count law give

```math
\begin{aligned}
\mathbb E[L_k]
 &=\rho^2\int_{M_H}\int_{M_H}
 \mathbf1_{p\preceq q,\ p\ne q}\ e^{-z_{pq}}\frac{z_{pq}^k}{k!}\,dq\,dp.
\end{aligned}
\tag{MA14}
```

The integrands are bounded by one, so this identity and the finite signed
sum are integrable. By the **closed** containment proved in §2, removing
the marked endpoints changes no volume, and for timelike pairs
$`z_{pq}=c\rho\sigma(p,q)^2`$. Null intervals have volume zero; null-related
pairs and the diagonal form a product-volume-null set (apply Fubini to each
translated null cone and singleton). The discrete definition still includes
null order; they are omitted only in this integral's almost-everywhere step.
Combining (MA14) for the actual four layers gives

```math
\begin{aligned}
e^{-z}\left(1-9z+16\frac{z^2}{2!}-8\frac{z^3}{3!}\right)&=K(z),\\
\mathbb E[A^{\mathrm{disc}}_\rho]
 &=\frac4{\sqrt{6\rho}}\left[\rho V-\rho^2
  \int_{M_H}\int_{M_H\cap J^+(p)}K(c\rho\sigma(p,q)^2)\,dq\,dp\right]
 =\mathcal A_\rho(M_H).
\end{aligned}
\tag{MA15}
```

Both factors of intensity, ordered pairs and factorial denominators are
retained. This is an exact equality for every positive density, not an
asymptotic approximation. Applying (MA10) to this equality proves the expected
limit in (MA3). It is **not** an interchange of expectation with an almost-sure
limit: no sample-wise limit has been proved or used.

### Existing Lean API: exact correspondence, not a new compiled instance

[`ExpectationBridge.lean`](../formal/BoundaryDraft/ExpectationBridge.lean)
has exactly three fields in `BoundedCausalRegion M`: `measurable`, `bounded`
and `causallyConvex`. The first two are discharged in §2's compact-domain
argument, and the third by (MA5) for all closed intervals. There is no smoothness,
spacelike-face or two-graph-budget premise in this bridge. Its
`BoundedCausalRegion.sprinkling` constructs the same positive-density law;
`BoundedCausalRegion.integrable_discreteBDGAction` and
`BoundedCausalRegion.expectedBDGAction_eq` express (MA13) and (MA15).
`FiniteSprinkling.interval_rate` in
[`ExpectationGeometry.lean`](../formal/BoundaryDraft/ExpectationGeometry.lean)
uses exactly the containment and endpoint-nullity established above.
`integral_intervalLayer` in
[`PoissonExpectation.lean`](../formal/BoundaryDraft/PoissonExpectation.lean)
is the checked abstract counterpart of (MA14).

The application in this note is a **conventional mathematical specialization**
with all hypotheses proved, not an added Lean declaration. In particular no
function named `expected_action` is defined to return `cap.action` and then
presented as a verified probability theorem. A future end-to-end formal port
must encode this region/stratum geometry, coordinate integral and induced area,
and check these proof terms. Existing Lean results are not changed or promoted
to a new mixed-region theorem by this written proof.

## 6. Nonvacuity and independent regressions

The constant member $`H=T`$ has $`V=\pi T^4/3`$ and target $`4\pi T^2`$.
It is a mixed cone cap, **not** a diamond of the same time extent, whose target
is $`\pi T^2`$. The genuinely nonplanar member
$`H(x)=1+\tfrac15\sin x_1`$ has variable radius and nonzero lower-face second
derivative. It satisfies the theorem without taking a null-face limit.
The affine member $`H=1+a\cdot x`$, $`0\lt|a|\lt1`$, tests that global
positivity of $`H`$ is not required; its radial root is $`1/(1-a\cdot\omega)`$.

`mixed_poisson.py` provides two independent diagnostics:

- Actual finite-order layer counts and the normalized discrete action on small
  simple configurations, including closed null relations and cross-chart pairs.
- Positive expected layer integrals (MA14) computed **separately**, using ordinary
  source time/radius coordinates and complete rest-frame partner intervals.
  The partner rule integrates $`4\pi r^2\,dr\,dt`$ on
  $`0\le t\le D`$, $`0\le r\le\min(t,D-t)`$, where $`D=\sqrt{\sigma(p)}`$.
  It does not call the reduced Gaussian/coarea action or insert the target.
  Combining the four layer means is then compared to #83's independent action.

`test_mixed_poisson.py` includes finite-order normalization/endpoint controls,
boosted complete-interval geometry samples, all frontier types, independent
screen versus Euclidean area, non-round layer quadrature refinement, and
negative controls for lost cross-chart pairs and incorrect layer factorials.
These samples and quadrature tolerances are **not** proofs of quantified
geometry or certified integration errors. High-density convergence diagnostics
remain in `reproduce_null_mixed.py`; separate positive layer means suffer
large signed cancellations and are used only at moderate densities.

```sh
uv venv --python 3.12 .venv
uv pip install --python .venv/bin/python -r requirements.txt
.venv/bin/python -m unittest -v test_mixed_poisson test_null_mixed
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
.venv/bin/python reproduce_null_mixed.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

## 7. Coverage and verification ledger

| Scope | Result / remaining obligation |
| --- | --- |
| Smooth global strict-Lipschitz lower graph under one flat 4D cone, with its one tip and regular SN joint | Written deterministic induced-area limit and exact expected-action transfer above |
| Round and sine mixed caps | Non-vacuous members; independent finite-density layer regressions, not simulations of convergence |
| Existing null-plane cap and diamonds | Retain their separate calibration results; their lower null faces do not satisfy this theorem's strict spacelike hypothesis |
| Arbitrary NN joints, multiple tips, same-side creases, additional corners or caustics | Not covered: the complete-future interval identity must be replaced or re-proved and every extra stratum's full signed contribution accounted for |
| Curved null/mixed regions | Not covered: metric volume, actual restricted interval phase, curved screen area and full nonlocal cancellation need a common proved interface; #93's different two-face conformal instance is not such a theorem |
| Other dimensions | Not covered: the dimension-indexed layer polynomial and interval identity, global concentration and induced joint measure need their own compatible proof; a 4D Gaussian mass is not a dimensional argument |
| General atlases, noncompact regions and degenerating slopes/angles | Not covered: global partners, tails and uniformity need bounded tasks under #24/#81/#86 |
| Variance, rates, individual sprinklings, geometry-dependent density limits | No result asserted |

**Next-branch reconnaissance (#134):** the [two-tip feasibility package](two-tip-null-feasibility.md)
selects a fixed nonplanar-floor union of two cones, outside (MA6). It derives
an exact full-partner cap-minus-lens interface and a normalized tip estimate;
the lens's complete signed limit and crease/triple-corner response remain
unproved. This is not a new global mixed theorem or Lean instance.

No new catch-all issue is needed: #24's coverage matrix and #86's integrated
review retain these branches. A further proof issue must specify its geometry,
actual interval law and missing signed estimate, rather than treat the present
single-cone theorem as general null/mixed completion.

**Written:** (MA1)–(MA15), with #83's weighted estimates used explicitly for
partition accounting. **Machine verification:** the cited baseline interval
and abstract probability theorems only; this package changes no Lean source,
checker, dependency or build input, and claims no new full Lean audit.
**Executable evidence:** Python/symbolic geometry, combinatorics and independent
quadratures, plus the unchanged repository checks. **Independent human
mathematical/physical review:** still outstanding with #94/#86. GitHub CI or
automated feedback is not a substitute for that review.
