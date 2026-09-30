# Fixed-null mixed estimates and the localization obstruction (#83)

**Written analytic result, with symbolic/numerical regressions; not a new Lean
result or independently reviewed theorem.** Work is on exactly the fixed flat
4D mixed class selected in [#90, §6](general-contract.md#6-selected-first-flat-4d-mixed-pilot-for-83--84).
The signed interval identity is already checked in the baseline. Its weighted
application, estimates and cutoff accounting below are conventional proofs.
No new Poisson instance or expected-action theorem is asserted. #84 owns that
geometric/API assembly. This does not close #24, cover arbitrary null/null
joints, or establish convergence of individual sprinklings.

The unweighted all-partner strategy already appears in
[first-attempt §3](first-attempt.md#3-first-class-one-null-cone-future-boundary).
The additions here are the weighted fixed-geometry bound, uniform tip estimate,
explicit compensating generator term, a rigorous obstruction to **discarding**
the artificial complement, and nonplanar regressions. No priority claim is made.

## 1. Geometry and the unchanged observable

Use signature $(+---)$. Fix smooth globally Lipschitz $`H:\mathbb R^3\to\mathbb R`$,
$`T=H(0)>0`$, and a Lipschitz bound $`0\le\lambda\lt1`$. Define

```math
\begin{aligned}
M_H&=\{(t,x):-H(x)\lt t\lt-|x|\},\\
m&=\frac{T}{1+\lambda},\qquad B=\frac{T}{1-\lambda},\\
R(\omega)&=H(R(\omega)\omega),\qquad m\le R(\omega)\le B.
\end{aligned}
\tag{NM1}
```

Indeed $`r-H(r\omega)`$ has derivative at least $`1-\lambda`$, starts at
$`-T`$, and tends to infinity. The root is unique and smooth. The entire
frontier consists of the lower spacelike face, the upper cone, their mixed
joint, and the cone tip. There is no lateral wall, extra corner or same-side
seam. The lower epigraph is a future set: a future causal displacement changes
$`t+H(x)`$ by at least $`(1-\lambda)\Delta t`$. Its intersection with the
chronological past of zero is therefore causally convex. Also $`r\lt B`$
and $`-B\lt t\lt0`$ in the region. Smooth graph boundaries and the Lipschitz
cone have zero four-volume. These facts justify the ordinary integrals below;
they have not been instantiated as new Lean region declarations here.

Put $`c=\pi/24`$, $`C=4/\sqrt6`$ and retain the **signed** kernel
$`K(z)=(1-9z+8z^2-4z^3/3)e^{-z}`$. For a bounded measurable first-endpoint
weight $`\phi`$ define

```math
\mathcal A_\rho[\phi]=C\sqrt\rho\left[
 \int_{M_H}\phi(p)\,dp-\rho\int_{M_H}\phi(p)
 \int_{M_H\cap J^+(p)}K(c\rho\tau_{py}^4)\,dy\,dp\right].
\tag{NM2}
```

The unweighted case is the existing 4D deterministic action, not a newly
renormalized observable. In particular, the inner integration is **not**
restricted to the support of the source weight. At finite density all these
integrals are absolutely integrable: the region and weight are bounded and
the kernel is bounded. This licenses Fubini before taking any limit; it does
not license dropping signed terms in the normalized asymptotics.

## 2. Exact signed cancellation with every partner retained

For any source $`p\in M_H`$, every future partner up to the tip is in the lower
future set. Thus the inner set in (NM2) agrees almost everywhere with the
entire closed interval $`I(p,0)`$. Define $`\sigma(p)=t^2-|x|^2>0`$.
The existing exact interval identity gives

```math
\rho\int_{I(p,0)}K(c\rho\tau_{py}^4)\,dy
  =1-e^{-c\rho\sigma(p)^2},\qquad
\mathcal A_\rho[\phi]=C\sqrt\rho\int_{M_H}\phi(p)e^{-c\rho\sigma(p)^2}\,dp.
\tag{NM3}
```

For an independent normalization check, the coefficient of $`z^n`$ in $`K`$
is $`(-1)^n(n+1)(2n+1)(2n+3)/(3n!)`$. The interval moment for proper duration
$`D`$ is
$`\pi D^{4n+4}/[(2n+1)(2n+2)(2n+3)(4n+4)]`$. Multiplication gives exactly
the exponential integral series, not an absolute-kernel series. Termwise
integration is legitimate on this fixed compact interval by uniform absolute
convergence. Alternatively, the baseline proves the identity by finite
primitives and Lorentz transport in
[`CausalInterval.lean`](../formal/BoundaryDraft/CausalInterval.lean) and
[`TimelikeInterval.lean`](../formal/BoundaryDraft/TimelikeInterval.lean).
This identity is independent of a spacelike limiting formula.

Write $`p=(-\sqrt{r^2+\sigma},r\omega)`$. The Jacobian is
$`r^2/(2\sqrt{r^2+\sigma})`$. With
$`D_\sigma(\omega)=\{0\lt r\lt B:\sqrt{r^2+\sigma}\lt H(r\omega)\}`$, put

```math
\begin{aligned}
W_\phi(\sigma)&=\int_{S^2}\int_{D_\sigma(\omega)}
 \frac{r^2\phi(-\sqrt{r^2+\sigma},r\omega)}{2\sqrt{r^2+\sigma}}\,dr\,d\omega,\\
W_\phi(0)&=\frac12\int_{S^2}\int_0^{R(\omega)}r\phi(-r,r\omega)\,dr\,d\omega,\\
\mathcal A_\rho[\phi]&=C\sqrt\rho\int_0^\infty e^{-c\rho\sigma^2}W_\phi(\sigma)\,d\sigma.
\end{aligned}
\tag{NM4}
```

For every positive $`\sigma`$, $`D_\sigma\subset(0,R)`$. Hence for
$`|\phi|\le M`$, $`|W_\phi(\sigma)|\le M\pi B^2`$ and the weight vanishes
for $`\sigma\ge B^2`$. Do **not** assume every positive-sigma radial slice
starts at zero: even the sine example below can have annular slices above
$`T^2`$. The definition (NM4) includes them.

## 3. A proved near-cone bound, without a null-limit interchange

In addition to $`|\phi|\le M`$, suppose the weight is Lipschitz in time with
constant $`L`$ on the closed bounding box, uniformly in space. Measurable
angular weights and radial step cutoffs independent of time are allowed.
For $`0\lt\sigma\le T^2/4`$, the following explicit estimate holds:

```math
|W_\phi(\sigma)-W_\phi(0)|\le E(\sigma),\qquad
E(\sigma)=\pi\sigma\left[
 M\left(1+\log\frac B{\sqrt\sigma}
       +\frac{2B}{m(1-\lambda)}\right)+LB\right].
\tag{NM5}
```

Here is a proof that includes both moving endpoints and the tip.

1. If $`r\le m/2`$, then $`H(r\omega)-r\ge T/2`$ while
   $`\sqrt{r^2+\sigma}-r\le\sqrt\sigma\le T/2`$; strict inclusion follows
   also at the possible endpoints (at $`r=0`$, $`H=T`$). Consequently any
   removed radius in $`(0,R)\setminus D_\sigma`$ is at least $`m/2`$.
2. By the radial slope bound,
   $`H(r\omega)-r\ge(1-\lambda)(R-r)`$. A removed radius therefore satisfies

   ```math
   (1-\lambda)(R-r)\le\sqrt{r^2+\sigma}-r
     =\frac\sigma{\sqrt{r^2+\sigma}+r}\le\frac\sigma m.
   ```

   The removed set, even without connectedness, lies in an endpoint shell
   of width $`\sigma/[m(1-\lambda)]`$. Bounding its Jacobian by $`B/2`$
   and integrating over the sphere costs at most
   $`2\pi B\sigma/[m(1-\lambda)]`$.
3. The Jacobian change on the full original interval is bounded by

   ```math
   0\le\frac r2-\frac{r^2}{2\sqrt{r^2+\sigma}}
     \le\min\left(\frac r2,\frac\sigma{4r}\right).
   ```

   Split at $`r=\sqrt\sigma\le B`$. Integration up to $`B`$ and over
   $`S^2`$ gives $`\pi\sigma[1+\log(B/\sqrt\sigma)]`$.
4. The change of the weight itself costs at most $`\pi LB\sigma`$, since
   its pointwise product with the Jacobian is bounded by
   $`L(r/2)\sigma/(2r)=L\sigma/4`$ for $`r>0`$.

Multiplying the geometric changes by $`M`$ proves (NM5). In particular this
is an actual weighted remainder estimate, not an assumed geometric jet.

The Gaussian has mass **four**, not one:

```math
C\sqrt\rho\int_0^\infty e^{-c\rho\sigma^2}\,d\sigma=4.
\tag{NM6}
```

For any fixed split $`0\lt s\le T^2/4`$, $`E`$ is increasing on $`[0,s]`$
with $`E(0)=0`$. The global bound and Gaussian tail give

```math
\left|\mathcal A_\rho[\phi]-4W_\phi(0)\right|
 \le4E(s)+8M\pi B^2\,\mathrm{erfc}(\sqrt{c\rho}\,s).
\tag{NM7}
```

First let density tend to infinity with geometry, weights and $`s`$ fixed,
then let $`s\downarrow0`$. This proves the weighted scalar limit. No exchange
with a varying geometry or angle was used. These are source-to-tip
near-cone estimates **after the complete signed partner integration**;
(NM5) is not an estimate for an isolated sector of almost-null endpoint pairs.
A coordinate-distance partner split has the separate interface in §6.
No density-dependent family, optimized density rate, or uniform null-face
transition is asserted. The constants explicitly deteriorate as
$`\lambda\uparrow1`$ or $`T\downarrow0`$.

## 4. The local coefficient and its indispensable generator term

Let $`\phi_0(r,\omega)=\phi(-r,r\omega)`$. For absolutely continuous radial
traces with integrable $`r^2\partial_r\phi_0`$ (in particular smooth weights),
integration by parts identifies the actual weighted response:

```math
4W_\phi(0)=\int_{S^2}R^2\phi_0(R,\omega)\,d\omega
 -\int_{S^2}\int_0^R r^2\partial_r\phi_0(r,\omega)\,dr\,d\omega.
\tag{NM8}
```

The tip endpoint is zero because $`r^2\phi_0\to0`$. The derivative is the
**total generator derivative**, $`-\partial_t\phi+\omega\cdot\nabla_x\phi`$,
not just a radial spatial derivative. The coefficient of the joint trace is
**+1**, derived from the signed kernel and (NM6), not from taking a spacelike
angle to infinity. It is accompanied by the generally nonzero second term.

For a joint test function $`\psi(\omega)`$, transport it constantly along
the generators and in time: $`\phi(t,r\omega)=\psi(\omega)`$ for $`r>0`$
(the axis value is immaterial). The second term vanishes and the response is
$`\int_{S^2}R^2\psi\,d\omega`$. Independently, the parameterization
$`(-R,R\omega)`$ has screen metric $`R^2d\omega^2`$, since its time and radial
derivative terms cancel. Thus this is unit coefficient against the correct
Lorentzian area, not ambient Euclidean spacetime area. Angular partitions of
unity are legitimate, but each weight must retain its full generator and
all future partners.

### Normal rescaling and the two singular limits

The future normals are
$`k=(1,-\omega)`$ and
$`n=(1,-\nabla H)/\sqrt{1-|\nabla H|^2}`$.
Their inner product is positive:
$`g(n,k)=(1-\nabla H\cdot\omega)/\sqrt{1-|\nabla H|^2}`$.
No logarithm of this quantity enters (NM3)–(NM8). Under an affine marking
$`k'=\alpha(\omega)k`$, write $`r=\alpha a`$. The cone response measure becomes
$`2\alpha^2a\,da`$, and the derivative term becomes
$`\alpha^2a^2\partial_a\phi_0\,da`$; the joint endpoint is still
$`\alpha^2a_J^2=R^2`$. For a nonaffine increasing reparameterization
$`r=f(a,\omega)`$, the same statements use $`2f\partial_af\,da`$ and
$`f^2\partial_a\phi_0\,da`$. All terms together are scale invariant, including
the artificial boundaries. A rescaling does not create a logarithmic corner
coefficient. The normalization $`g(n,k)=1`$ at the joint is optional gauge
fixing, not a hypothesis on the action.

For comparison only, two spacelike planar faces have weight $`1/s`$ for
$`0\lt s\lt1`$. The singularity $`s\downarrow0`$ corresponds to coincident
unit timelike normals and small positive rapidity. A face approaching a
**distinct** null ray is the opposite endpoint $`s\uparrow1`$. Neither
coefficient comparison licenses a density/geometry/cutoff interchange; no
such comparison is used in the proof above.

## 5. Tip estimate and a rigorous localization-route obstruction

After the signed cancellation, for every density and $`0\lt\delta\le B`$,

```math
|\mathcal A_\rho[\phi\,\mathbf1_{r\lt\delta}]|
 \le4M\pi\delta^2.
\tag{NM9}
```

Indeed its coarea weight is bounded by $`M\int_{S^2}\int_0^\delta r/2\,dr
=M\pi\delta^2`$. This proves there is no residual point mass at the cone tip
for this reduced full-partner action. The spatial cylinder used here contains
a genuine spacetime tip neighborhood, so this also bounds the latter. It is
not obtained by deleting a measure-zero tip from the raw bilocal integrand.
For $`\delta\lt m`$, the cylinder with unit source weight has limit exactly
$`4\pi\delta^2`$; at a fixed cutoff it is not zero.

Now put $`\phi_h=\mathbf1_{R(\omega)-h\lt r\lt R(\omega)}`$, independent
of time, with $`0\lt h\lt m`$. Formula (NM7) applies with $`L=0`$, and gives

```math
\lim_{\rho\to\infty}\mathcal A_\rho[\phi_h]
 =\int_{S^2}\left[R^2-(R-h)^2\right]d\omega
 \le8\pi Bh\ \longrightarrow\ 0\quad(h\downarrow0).
\tag{NM10}
```

Its complementary source region has the nonzero limit
$`\int_{S^2}(R-h)^2d\omega`$. Thus “keep a shrinking joint collar and discard
the complement” is a **false route on the actual weighted action**, not merely
an inconclusive absolute estimate. Smooth collar approximations have precisely
the compensating term in (NM8). For a finite smooth source partition,
$`\sum_i\phi_i=1`$, the generator derivatives sum to zero; for a radial split,
the two artificial endpoint terms cancel. Cross-chart partners were never
removed. This explains how a joint target can arise while the source density
is spread along the cone.

This is not a counterexample to Conjecture 1′: the collar observable retains
partners in the whole original region and is not the full action of an
independently chosen region. In fact (NM7) with $`\phi=1`$ gives the conventional
scalar limit $`\int R^2d\omega`$ for the whole pilot. No claim that its missing
formal geometric/expectation assembly is already checked follows.

## 6. Exact nonlocal interface to #84

If #84 uses the full-partner route, (NM3) is an **exact replacement** for proving
separate short- and long-pair cancellation. It has integrated every long partner,
not assumed that the long part is small. Equations (NM7)–(NM9) then supply
finite sums and tip control. The old two-spacelike-face long-null theorem has
not been applied to a null face outside its hypotheses.

If instead a measurable partner cutoff $`0\le\chi(p,y)\le1`$ is introduced,
its exact ledger is

```math
\begin{aligned}
S_\rho[\phi;\chi]&=C\sqrt\rho\left[\int\phi
 -\rho\int\!\!\int\phi(p)\chi(p,y)K(c\rho\tau_{py}^4)\,dy\,dp\right],\\
N_\rho[\phi;\chi]&=-C\rho^{3/2}
 \int\!\!\int\phi(p)(1-\chi(p,y))K(c\rho\tau_{py}^4)\,dy\,dp,\\
S_\rho+N_\rho&=C\sqrt\rho\int\phi(p)e^{-c\rho\sigma(p)^2}\,dp.
\end{aligned}
\tag{NM11}
```

All single integrals are over $`M_H`$, and double integrals have precisely
(NM2)'s full causal domain. No separate vanishing estimate for $`N_\rho`$ is
claimed. An exact remainder suitable for assembly is
$`\mathcal R_\rho[\phi;\chi]=S_\rho+N_\rho-4W_\phi(0)`$, bounded by (NM7).
For a finite partition, sum the actual weights and their (NM8) terms, not
actions of disjoint chart regions. Dropping $`N_\rho`$ or the generator term
requires a new proof and is not part of this handoff.

Remaining #84 deliverables are explicit, not conclusion-valued admissibility:

- Encode the selected region and all strata; prove its measurable finite-volume
  and ambient closed-interval containment instance. The conventional geometry
  argument in §1 indicates the construction, not a new checked declaration.
- Instantiate the existing interval integral with the actual weighted region;
  justify the coordinate/Fubini identities in that API and the independent
  screen-area measure. Port or independently verify the estimates as needed.
- Assemble the entire deterministic target with the exact complement ledger.
  The conventional scalar corollary above is available; there is no need to
  invent a separate long-null-vanishing premise for the full-partner route.
- Only then apply `BoundedCausalRegion.expectedBDGAction_eq` at each positive
  density with its real hypotheses discharged. The present Python action
  evaluator is not that probability construction or a sample-wise result.

## 7. Calibrations, new member and executable evidence

### Round mixed cap, independently of diamonds

For $`H=T`$, the joint radius is $`T`$, the candidate area is $`4\pi T^2`$,
and the exact radial primitive gives

```math
W_T(\sigma)=\pi\left[
 T\sqrt{T^2-\sigma}
 -\sigma\log\frac{T+\sqrt{T^2-\sigma}}{\sqrt\sigma}\right]
 \quad(0\lt\sigma\lt T^2),
\qquad W_T(0)=\pi T^2.
\tag{NM12}
```

It is zero beyond $`T^2`$. Its integral is the independently computed volume
$`\pi T^4/3`$. The time-dependent weight $`\phi=t`$ has
$`W_t(\sigma)=-2\pi(T^2-\sigma)^{3/2}/3`$; this tests the time derivative
in (NM8), not just time-independent cutoffs.

### Existing null calibrations, not members of the smooth mixed class

For the flat diamond of proper height $`T`$, $`R=T/2`$ and the same full-partner
response gives $`\pi T^2`$. For the checked null-plane-truncated diamond,
$`R(\mu)=\min(T/2,a/(1+\mu))`$, $`0\lt a\lt T`$, it gives
$`\pi a(2T-a)`$. The exact weight, support and action used in regressions are
those in `calculations.py` and [first-attempt (9)](first-attempt.md).
Their lower null faces and seams mean that the strict-Lipschitz proof of (NM5)
is not being extended to them. The baseline concrete cap has its own checked
Gaussian concentration proof. There is no extra seam term hidden in the
angular integral of these specific calibrations; this is not a theorem about
arbitrary corners.

### A genuinely nonplanar mixed member

Fix $`H(x)=1+\tfrac15\sin x_1`$. It is smooth, globally $`1/5`$-Lipschitz and
strictly positive. Its lower face has nonzero second derivative at interior
points, its joint radius varies, and it is not the all-null plane-cut
calibration. It is outside that calibration by causal face type, not by a
coordinate choice. `SineMixedCap` evaluates its radius, independent screen
area, exact coarea slices, finite-density action and ordinary volume.

For the evaluator's more general parameters only, impose
$`T\epsilon+2\epsilon^2\lt1`$. This guarantees
$`Q''\le2(T\epsilon+2\epsilon^2-1)\lt0`$ for
$`Q(r)=(T+\epsilon\sin(r\mu))^2-r^2`$. Each positive-sigma slice is an
interval, possibly with **two positive endpoints**. Bracket its unique
maximum before its endpoints; assuming monotonicity from zero loses real
volume. This restriction belongs only to the numerical evaluator, not to the
selected class or the proof of (NM5).

Run from the repository root:

```sh
.venv/bin/python -m unittest -v test_null_mixed
.venv/bin/python reproduce_null_mixed.py
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

The [generated diagnostic table](../results/null-mixed.md) reports refinement,
not certified quadrature errors. Tests check the signed interval normalization,
all-partner versus truncated-partner bookkeeping, Gaussian mass, radial
primitive, moving-endpoint and time-weight bounds, tip and complement terms,
round/diamond/null-cap calibrations, and the sine member including annular
slices and an independent direct coordinate integration. A finite sample is
not a proof of an asymptotic theorem.

**Verification ledger:** the arguments (NM1)–(NM12) are written here. The
existing interval identity is Lean checked in the baseline; no new Lean file,
checker, dependency or build input changes in this package, so no new Lean
audit is claimed. Python/symbolic checks validate formulas and regressions,
not all quantified mathematical hypotheses. Independent mathematical/physical
human review is still absent and remains with #94/#86. Arbitrary NN joints,
additional strata, curved null geometry, other dimensions, null/angle-limit
interchanges and individual-sprinkling convergence remain outside this result.
