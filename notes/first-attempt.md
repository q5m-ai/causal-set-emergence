# First proof attempt — four-dimensional flat regions

**Status:** a self-contained proof draft for the two classes below, with symbolic
and numerical checks. Not independently reviewed. No claim of priority or of a
proof of the full conjecture. The variable-angle result here has a **planar
future boundary**; it is not a localization theorem for two arbitrary boundaries.

**Formalization:** [the Lean layer](../formal/README.md) checks supporting
algebra, a generic signed-kernel limit lemma, concrete kernel scaling,
differentiation of the auxiliary integral through order three, and its
finite-interval mass and signed first-moment identities. It now also proves
half-line normalization, absolute integrability and the absolute first moment,
an explicit absolute tail bound, and the concrete signed-rescaling limit.
It now also verifies the **exact four-dimensional action reduction for every
admissible graph cap at every positive density**, including strict Euclidean
positive-part Lipschitz control, complete future slices, coordinate/Fubini steps,
compact domination, and the concrete BDG cone identity.
The **deterministic ellipsoid limit (19) and concrete null-cap limit (8) are
now machine-checked**. `ellipsoidLimitGoal` and `nullCapLimitGoal` prove the
unchanged four-dimensional targets. For the null cap, Lean derives the actual
causal-interval identity, arbitrary-timelike rest-frame transport, boundary
null-set replacement, full coordinate Jacobians, exact logarithmic weight (9),
absolute integrability, and normalized Gaussian concentration. The **concrete
ellipsoid geometric interpretation** is now also checked: regular joint,
positive-branch Lorentzian angle, and exact variable-angle surface integral.
For general graph caps, compactness/measurability of the Euclidean joint,
a uniform noncritical boundary band, and ambient C³ regular neighborhoods
are checked. This does not yet supply integration charts or coarea.
The general graph-cap regular-collar/coarea limit and variable-angle integral,
arbitrary null boundaries, induced null-joint geometry, and Poisson-expectation
bridge remain open.
The checked results concern `continuumMean`, not yet a formalized random sprinkling expectation,
and assert no convergence rate.

## 1. Precise target and conventions

We use Conjecture 1′, equation (11), of Dowker–Liu–Lloyd-Jones,
[arXiv:2501.00139v2](https://arxiv.org/html/2501.00139v2#S2.E11).
In four-dimensional Minkowski space with signature $`(-+++ )`$, its flat-space
specialization is

```math
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_J\coth\theta\,dA,
 \qquad \mathcal A_\rho:=\frac{l_p^2}{\hbar}\mathbb E S^{(4)}_\rho.
 \tag{1}
```

Here $`\rho=l^{-4}`$, and $`J`$ is the intersection of the past and future
boundaries, not the collection of all boundary seams. At a joint with a null
face we use the conjecture's limiting convention $`\coth\theta=1`$.
We prove statements about the **mean**, not about concentration of individual
sprinklings. All geometric parameters are fixed as $`\rho`$ increases.

Set

```math
 c=\frac\pi{24},\qquad
 P(z)=1-9z+8z^2-\frac43z^3,\qquad K(z)=P(z)e^{-z}.
```

For a bounded causally convex region, Poisson interval counting gives exactly

```math
 \mathcal A_\rho(M)=\frac4{\sqrt6}\sqrt\rho
 \left[|M|-\rho\int_M dx\int_{J^+(x)\cap M}dy\,
 K\bigl(c\rho\tau_{xy}^4\bigr)\right].
 \tag{2}
```

Causal convexity is essential: it makes the interval volume equal to the full
Minkowski value $`c\tau^4`$. We prove this property for our regions rather than
assuming that every globally hyperbolic subregion of Minkowski space has it.
Boundary sets have four-volume zero and do not affect (2).

## 2. An exact interval identity

For a causal interval $`I(x,q)`$ of proper duration $`T`$,

```math
 \rho\int_{I(x,q)}K(c\rho\tau_{xy}^4)\,dy
       =1-e^{-c\rho T^4}.
 \tag{3}
```

**Proof.** Put $`x=0`$, $`q=(T,\mathbf0)`$, and use radial null coordinates
$`u=(t-r)/\sqrt2`$, $`v=(t+r)/\sqrt2`$. Their domain is
$`0\le u\le v\le T/\sqrt2`$, and the angularly integrated measure is
$`2\pi(v-u)^2\,du\,dv`$. Consequently, for every integer $`n\ge0`$,

```math
 \int_{I(x,q)}\tau_{xy}^{4n}\,dy
 =\frac{\pi T^{4n+4}}
 {(2n+1)(2n+2)(2n+3)(4n+4)}.
 \tag{4}
```

The coefficient of $`z^n`$ in $`K(z)`$ is

```math
 \frac{(-1)^n}{n!}q_n,\qquad
 q_n=\frac{(n+1)(2n+1)(2n+3)}3.
```

Inserting (4) into the uniformly convergent power series for the kernel gives

```math
 \int_I K(c\rho\tau^4)\,dy
 =cT^4\sum_{n\ge0}\frac{(-c\rho T^4)^n}{(n+1)!},
```

which is (3). This also independently reproduces the flat specialization of
Dowker's equations (4.8)–(4.13), specifically the flat term in (4.9),
[arXiv:2007.13206v2](https://arxiv.org/html/2007.13206v2).
$`\square`$

**Machine-checked route.** `CausalInterval.lean` proves (3) directly from the
actual four-dimensional set integral, its polar/null-coordinate Jacobian, and
two finite primitives; it does not assume the series/integral exchange above.
`IntervalMoments.lean` independently proves (4) for every natural `n`, with
`n=0,1` exercised by focused regressions. Explicit determinant and
future-orientation proofs transport (3) from the standard rest frame to every
future-timelike pair.

## 3. First class: one null-cone future boundary

### Theorem 1

Let $`q`$ be an event and $`F`$ an open future set, meaning
$`J^+(F)\subset F`$, with $`q\in F`$. Suppose

```math
 M=F\cap I^-(q)
```

is bounded. Put $`q=0`$. Assume the trace of $`F`$ on the past null cone is
$`0\le r<R(\omega)`$, where $`\omega\in S^2`$ and $`R>0`$ is bounded and
piecewise $`C^1`$. More precisely, require cone points with $`r>R(\omega)`$
to lie outside $`\overline F`$; exceptional directions of measure zero are
harmless. Thus the joint is the radial section

```math
 J=\{(-R(\omega),R(\omega)\omega):\omega\in S^2\}.
```

Then

```math
 \lim_{\rho\to\infty}\mathcal A_\rho(M)
 =\int_{S^2}R(\omega)^2\,d\omega=\mathrm{Area}(J).
 \tag{5}
```

**Proof.** A future set intersected with a past set is causally convex. Strong
causality is inherited from Minkowski space, and the causal diamond between
any two points of $`M`$ is the full compact Minkowski diamond contained in
$`M`$. Hence $`M`$ is globally hyperbolic.

For $`x\in M`$, the entire interval $`I(x,q)`$ lies in $`F`$. Therefore
$`J^+(x)\cap M=I(x,q)`$ up to measure-zero sets. Equation (3) reduces the
bilocal action to the positive integral

```math
 \mathcal A_\rho(M)
 =\frac4{\sqrt6}\sqrt\rho\int_M
             e^{-c\rho\tau_{xq}^4}\,dx.
 \tag{6}
```

Write $`t=-\sqrt{r^2+\sigma}`$, $`\sigma=\tau_{xq}^2\ge0`$. Then

```math
 dx=\frac{r^2}{2\sqrt{r^2+\sigma}}\,d\sigma\,dr\,d\omega.
```

For a sufficiently large fixed $`B`$, define

```math
 W(\sigma)=\int_{S^2}\int_0^B
 \frac{r^2}{2\sqrt{r^2+\sigma}}
 \mathbf1_F(-\sqrt{r^2+\sigma},r\omega)\,dr\,d\omega.
```

The integrand is bounded by $`r/2`$. The trace hypotheses and dominated
convergence imply

```math
 W(0+)=\frac14\int_{S^2}R(\omega)^2\,d\omega.
```

On the half-line, $`(4/\sqrt6)\sqrt\rho e^{-c\rho\sigma^2}`$ has total
mass **4**, independent of $`\rho`$, and concentrates at zero. Boundedness
and the right limit of $`W`$ prove (5).

Finally the induced metric of this cone section is $`R^2d\omega^2`$:
the time contribution $`-dR^2`$ cancels the radial spatial contribution.
Its area is exactly the right-hand side of (5). Each joint face has a null
future face, so (1) has this same right-hand side. $`\square`$

### Corollary 1: null-plane-truncated diamond

Take $`p=(-T,\mathbf0)`$, $`q=0`$, $`T>0`$, and $`0<a<T`$. With spatial
coordinate $`z`$, retain the future side of a null plane:

```math
 M_{T,a}=I^+(p)\cap I^-(q)\cap\{t-z>-a\}.
 \tag{7}
```

This is a genuine truncation, not a rescaled diamond. If
$`\mu=\omega_z`$, its joint section has radius

```math
 R(\mu)=\min\left(\frac T2,\frac a{1+\mu}\right),
```

with the second term interpreted as infinite at $`\mu=-1`$. Thus

```math
 \boxed{\lim_{\rho\to\infty}\mathcal A_\rho(M_{T,a})
       =\pi a(2T-a).}
 \tag{8}
```

Indeed, splitting the angular integral at $`\mu=2a/T-1`$ gives
$`\pi aT`$ from the surviving original joint and $`\pi a(T-a)`$ from the
new plane–cone joint. The seam between these patches has area zero.

For reproducible finite-density checks, the exact weight in (6) is

```math
 W_{T,a}(\sigma)=\frac\pi4\left[
 a(2T-a)-2(1-a/T)\sigma-\frac{\sigma^2}{T^2}
 -2\sigma\log\frac{aT}{\sigma}\right],\quad 0<\sigma<aT,
 \tag{9}
```

and zero above $`aT`$, with $`W(0)=\pi a(2T-a)/4`$. To obtain this, at
fixed $`\sigma`$ set $`w=-t=\sqrt{r^2+\sigma}`$; the allowed solid angle
is $`2\pi\min(2,\max(0,1+(a-w)/r))`$, and
$`r\le(T^2-\sigma)/(2T)`$. The change $`r\,dr=w\,dw`$ makes the two
angular regimes elementary integrals of $`\sqrt{w^2-\sigma}`$.
Integrating (9) also gives

```math
 |M_{T,a}|=\frac{\pi a^2T(3T-2a)}{24}.
```

For fixed $`T,a`$, (9) yields an error
$`O(\rho^{-1/2}\log\rho)`$, with lengths held in fixed units.

**Machine-checked scope.** For this concrete plane-truncated diamond,
`NullGeometry`–`NullCapLimit` prove causal convexity and complete slices,
remove the strict null boundary by a zero-measure theorem, derive every
coordinate Jacobian and both Fubini swaps under compact domination, and obtain
(9) in the original spacetime measure, including support, endpoint value,
measurability, and absolute integrability. The bilocal action then cancels
exactly to (6). A normalized half-line Gaussian with proved mass and domination
concentrates at zero, giving the unchanged proof term
`nullCapLimitGoal : NullCapLimitGoal` under exactly `0<a<T`. The displayed
quantitative error rate, induced-joint area interpretation, arbitrary-null
version of Theorem 1, and Poisson probability statements are not claimed as
Lean results.

## 4. A different exact reduction: planar future boundary

The null-cone theorem does **not** test finite $`\theta`$. For that we change
the future boundary to a spacelike plane while keeping its causal future
slices exactly computable.

Let $`\Omega\subset\mathbb R^3`$ be bounded with $`C^3`$ boundary. Let
$`h\in C^3(\overline\Omega)`$ satisfy

- $`h>0`$ in $`\Omega`$ and $`h=0`$ on $`\partial\Omega`$;
- $`\nabla h\ne0`$ on $`\partial\Omega`$;
- the extension $`h_+`$, equal to $`h`$ inside and zero outside, is globally
  $`\kappa`$-Lipschitz for some fixed $`\kappa<1`$.

**Checked admissibility API.** `GraphCapData h` uses an ambient profile with
`Ω = {h > 0}`, bounded positivity, and the displayed global **Euclidean**
positive-part Lipschitz bound with `0 ≤ κ < 1`. It derives openness and
measurability rather than assuming them. `GraphCapRegularity h` separately
specifies C³ locally at every point of the closed positive region, zero height
on its boundary, and nonzero actual differential at the zero level in that
closure. Their combination is `AdmissibleGraphCap h`; its boundary is proved
equal to `{h = 0} ∩ closure Ω`. This uses an ambient local C³ extension near
the closure and ignores unrelated exterior zeros. These regular-level
assumptions are reserved for the future collar theorem: neither smoothness nor
nonvanishing is needed for the exact reduction, and **positive-height critical
points are allowed**. No field assumes an action identity, limit, or joint
integral.

Consider

```math
 M_h=\{(t,x):x\in\Omega,\ -h(x)<t<0\}.
 \tag{10}
```

The epigraph $`t>-h_+(x)`$ is a future set: along a future causal displacement
$`(\Delta t,\Delta x)`$, $`t+h_+(x)`$ increases by at least
$`(1-\kappa)\Delta t`$. Intersecting it with $`t<0`$ proves causal
convexity and global hyperbolicity as in Theorem 1.

For a point at depth $`H=-t`$, its future in $`M_h`$ is exactly the complete
future cone truncated at time $`H`$. In particular, no lateral boundary was
introduced. Define

```math
 F_\rho(H)=4\pi\int_0^H r^2 e^{-c\rho(H^2-r^2)^2}\,dr.
 \tag{11}
```

The action density obtained by doing the future-point integral first is

```math
 L_\rho(H)=\frac{\sqrt\rho}{2\pi\sqrt6}F_\rho'''(H).
 \tag{12}
```

This is an exact identity, not an asymptotic expansion.

### Verification of (12), including the boundary constant

Let $`m_n=\int_0^1v^2(1-v^2)^{2n}\,dv=\tfrac12B(3/2,2n+1)`$. Then

```math
 F_\rho(H)=4\pi\sum_{n\ge0}
 \frac{(-c\rho)^n}{n!}m_nH^{4n+3}.
```

The integral of $`K`$ over the truncated future cone is

```math
 Q_\rho(H)=4\pi\sum_{n\ge0}
 \frac{(-c\rho)^n}{n!}q_nm_n\frac{H^{4n+4}}{4n+4}.
```

For $`n\ge1`$, the beta-function recurrence gives

```math
 \frac12(4n+1)(4n+2)(4n+3)m_n
       =24q_{n-1}m_{n-1}.
```

Since $`c=\pi/24`$, comparison of coefficients proves
$`F_\rho'''/(8\pi)=1-\rho Q_\rho`$. This is (12) by (2).
In particular $`F_\rho'''(0)=8\pi`$; losing this constant would lose the
bulk cancellation. Uniform convergence on finite $`H`$-intervals justifies
all differentiations here.

**Checked differentiation, separate from the action-density identity.**
Writing $`r=Hv`$ in (11) gives a fixed interval $`0\le v\le1`$.
With $`z=c\rho H^4(1-v^2)^2`$, its first three parameter derivatives have
integrands $`H^{3-j}v^2R_j(z)e^{-z}`$, where
$`R_1=3-4z`$, $`R_2=6-36z+16z^2`$, and
$`R_3=6-204z+288z^2-64z^3`$. For each differentiation, the integrand
and its derivative are jointly continuous and uniformly bounded on every
compact parameter rectangle. This justifies differentiation under the integral.
The argument, including $`F_\rho'(0)=F_\rho''(0)=0`$ and
$`F_\rho'''(0)=8\pi`$, is machine-checked in `KernelDerivatives.lean`.

**Closing the analytic formalization gap without a series exchange.**
`ConeIntegral.lean` now proves (12) by an exact finite-interval cancellation.
Let $`k=c\rho H^4`$, $`w=1-v^2`$, $`z=kw^2`$, and define
```math
 M_k(v)=2v^3w\bigl[-8z^2(w+1)+2z(15w+14)-15w-12\bigr]e^{-z}.
```
Direct differentiation gives
```math
 M_k'(v)=v^2\bigl[w^2(R_3'-R_3)(z)+48P(z)\bigr]e^{-z},
 \qquad M_k(0)=M_k(1)=0.
```
The same compact-rectangle domination justifies a fourth parameter derivative.
Writing
```math
 S_\rho(H)=4\pi\int_0^H r^2K(c\rho(H^2-r^2)^2)\,dr,
```
the cancellation yields $`F_\rho''''(H)=-8\pi\rho S_\rho(H)`$.
The FTC with the checked boundary constant therefore proves
$`F_\rho'''(H)/(8\pi)=1-\rho\int_0^H S_\rho(t)\,dt`$, including $`H=0`$.
This supplies an analytic proof rather than substituting the coefficient
recurrence for a justified interchange. The original series argument above
is retained as draft provenance; it is not an assumption of the Lean proof.

**Checked general geometry and measure justification.** `GraphGeometry.lean`
proves the positive-part epigraph is a future set from the Euclidean Lipschitz
inequality, identifies the exact complete future slice **including null-related
points and the vertex**, and proves causal convexity. Positive-part continuity
and bounded positivity supply compact support and a compact spacetime box.
`EllipsoidGeometry.lean` instantiates this with the existing global
$`2a/\min b_i<1`$ bound, even across the joint; the untruncated quadratic
is not claimed to be globally Lipschitz. No axis hypotheses are strengthened.
`SpacetimeIntegration.lean` reuses the measure-preserving coordinate
equivalences, Euclidean three-ball volume, and concrete cone identity to
identify $`Q_\rho(H)=\int_0^H S_\rho(t)\,dt`$ with the actual
four-dimensional BDG integral. Translations and vertical Fubini are
profile-independent. Compact boxes establish absolute integrability of the
causally restricted bilocal kernel, the individual future integrals, and the
height integrands before integration; endpoint changes use Lebesgue atomlessness.

Integrating (12) over each vertical fibre of (10), using
$`F_\rho''(0)=0`$, gives the second exact reduction:

```math
 \boxed{\mathcal A_\rho(M_h)=\int_\Omega G_\rho(h(x))\,dx,\qquad
 G_\rho(H)=\frac{\sqrt\rho}{2\pi\sqrt6}F_\rho''(H).}
 \tag{13}
```

For **every admissible graph cap**, (13) is now checked by
`AdmissibleGraphCap.graphReduction`, starting from the unchanged `continuumMean`,
`graphCapRegion`, concrete `bdgKernel`, and `planeKernel` in product Lebesgue
measure. The stronger theorem `graphCap_graphReduction` uses only the reduction
data, not the reserved collar assumptions. `ellipsoid_graphReduction` remains
available with its original statement and hypotheses as a specialization.
`ellipsoid_admissible` reuses the concrete smoothness and joint-regularity
proofs. A nonquadratic example `e - e²`, with `e` the spherical profile
`(1 - |x|²)/4`, is also admitted: its positive interior maximum is `3/16`,
its differential there is zero, and it is checked to differ from every
quadratic ellipsoid profile. This milestone establishes an **exact deterministic
reduction only**, not the general collar/coarea limit or variable-angle
integral. The subsequent explicit ellipsoid integration and limit are checked
separately, as described after (19); they reuse this exact reduction.

## 5. The signed approximate identity

Put $`\varepsilon=\rho^{-1/4}`$, $`F=F_1`$, and
$`G=F''/(2\pi\sqrt6)`$. Scaling (11) gives

```math
 G_\rho(H)=\varepsilon^{-1}G(H/\varepsilon).
 \tag{14}
```

Equation (14) is machine-checked in `KernelScaling.lean`, directly from (11)
with the positive inverse width $`\sqrt{\sqrt\rho}`$. This does not presume
any mass or tail estimate.

The kernel satisfies

```math
 G\in L^1(0,\infty),\qquad
 \int_0^\infty G(u)\,du=1,\qquad
 \int_0^\infty u|G(u)|\,du<\infty.
 \tag{15}
```

It is **not positive**. Its negative tail must not be discarded.

The finite-interval identities
```math
 \int_0^U G(u)\,du=\frac{F'(U)}{2\pi\sqrt6},\qquad
 \int_0^U uG(u)\,du=\frac{UF'(U)-F(U)}{2\pi\sqrt6}
```
are machine-checked by the fundamental theorem of calculus. The passage to
infinity, including **absolute** integrability in (15), is now also checked in
`KernelEstimates.lean` and `KernelHalfLine.lean`, using the following argument.
It closes the earlier formalization gap without adding hypotheses or assuming
that an asymptotic remainder can be differentiated.

**Proof of (15) by exact Gaussian cancellation (machine-checked).** Put
$`a=cu^4`$ and substitute $`t=1-v^2`$ in the already-justified fixed-interval
derivative formulas. For
```math
 P_{b,d}(a,t)=b-(2b+3d)at^2+2da^2t^4
```
one obtains
```math
 F''(u)=2\pi u\int_0^1\sqrt{1-t}\,P_{6,8}(a,t)e^{-at^2}\,dt,
```
```math
 uF'(u)-F(u)=2\pi u^3\int_0^1\sqrt{1-t}\,P_{2,0}(a,t)e^{-at^2}\,dt.
```
For $`a>0`$ and $`b,d\ge0`$, the constant-weight integral has primitive
$`(bt-dat^3)e^{-at^2}`$, hence integral $`(b-da)e^{-a}`$.
Moreover, $`|\sqrt{1-t}-1|\le t`$ on $`[0,1]`$ and
```math
 |P_{b,d}(a,t)|\le Q_{b,d}(a,t):=b+(2b+3d)at^2+2da^2t^4.
```
An exact primitive for $`tQ_{b,d}(a,t)e^{-at^2}`$ is
```math
 -\frac1a\left[\frac{3b+7d}{2}
   +\frac{2b+7d}{2}at^2+da^2t^4\right]e^{-at^2}.
```
Consequently, $`\int_0^1 tQ_{b,d}(a,t)e^{-at^2}\,dt\le(3b+7d)/(2a)`$.
Using $`e^{-a}\le1/a`$ and $`ae^{-a}\le2/a`$ bounds the endpoint term,
so the triangle inequality gives
```math
 \left|\int_0^1\sqrt{1-t}\,P_{b,d}(a,t)e^{-at^2}\,dt\right|
 \le\frac{5b+11d}{2a}.
```
The two choices above yield, for every $`u>0`$,
```math
 |F''(u)|\le2832u^{-3},\qquad
 |uF'(u)-F(u)|\le240u^{-1},\qquad
 |G(u)|\le\frac{1416}{\pi\sqrt6}u^{-3}.
```
These constants are deliberately loose. Continuity on $`[0,1]`$ and the
last estimate on $`[1,\infty)`$ prove both $`G\in L^1`$ and
$`u|G|\in L^1`$; signed cancellation is not being substituted for either.

For the normalization, change variables again to get
```math
 \frac{F(u)}u=2\pi\int_0^\infty
   \sqrt{(1-s/u^2)_+}\,e^{-cs^2}\,ds\longrightarrow2\pi\sqrt6.
```
The square-root factor is at most one and converges pointwise to one, so the
integrable Gaussian supplies domination. The bound on $`uF'(u)-F(u)`$ now
implies $`F'(u)\to2\pi\sqrt6`$. Passing the finite mass identity to infinity
proves $`\int G=1`$. Separately, the same boundary bound proves the signed
moment $`\int_0^\infty uG(u)\,du=0`$; its absolute integrability was proved
first. The checked generic signed-rescaling theorem therefore applies to this
concrete kernel on the positive half-line. $`\square`$

**Sharper draft asymptotics (not needed or claimed as Lean results).** Near
zero, (11) gives $`F(u)=4\pi u^3/3+O(u^7)`$, so
$`G(u)=4u/\sqrt6+O(u^5)`$. For large $`u`$, change variable to
$`s=u^2-r^2`$:

```math
 F(u)=2\pi\int_0^{u^2}\sqrt{u^2-s}\,e^{-cs^2}\,ds
     =2\pi\sqrt6\,u-\frac{12}{u}+O(u^{-3}).
 \tag{16}
```

The remainder in (16) may be differentiated twice (or three times), with
its $`j`$-th derivative $`O(u^{-3-j})`$. Here is a justification rather
than an assumption about differentiating an asymptotic expansion. Insert a
smooth cutoff $`\chi(s/u^2)`$ equal to one for $`s/u^2\le1/2`$ and zero
for $`s/u^2\ge3/4`$. On its support Taylor-expand
$`\sqrt{1-s/u^2}=1-s/(2u^2)+O(s^2/u^4)`$, with the corresponding bounds
on its first three $`u`$-derivatives. Integrating these bounds against the
Gaussian gives the stated derivative remainders. Derivatives of the cutoff
are exponentially small. For the complementary integral, return to
$`r=uv`$; its support has $`1-v^2\ge1/2`$, so this integral and its first
three derivatives are polynomial factors times $`e^{-c u^4/4}`$.

It follows that

```math
 G(u)=-\frac{2\sqrt6}{\pi u^3}+O(u^{-5}),
 \qquad F'(\infty)=2\pi\sqrt6,\qquad F'(0)=0.
```

These sharper draft facts are consistent with the checked half-line results
above. The leading negative-tail coefficient and the derivative remainder
bounds through order three have not themselves been formalized; none is a
hypothesis of the Lean normalization, tail, or rescaling theorems.

## 6. Variable-angle theorem

### Theorem 2

For every graph cap (10) satisfying the stated hypotheses,

```math
 \boxed{\mathcal A_\rho(M_h)
 =\int_{\partial\Omega}\frac{dA}{|\nabla h|}
       +O(\rho^{-1/4})
 =\int_J\coth\theta\,dA+O(\rho^{-1/4}).}
 \tag{17}
```

Constants in the error estimate may depend on the fixed region. The estimate
is not asserted uniformly as the joint becomes tangent, $`|\nabla h|\to0`$.
The displayed rate and the general limit remain **draft-level**, not Lean
results. `GraphCollar.lean` currently checks only the compact-joint and
uniformly noncritical-band prerequisites, with ambient regular neighborhoods.

For the future surface-measure formalization, level sets here are understood
inside the closed positive region, excluding unrelated exterior zeros. In
Euclidean coordinates the normalized area convention is
`(π/4) · μH[2]`, since pinned mathlib uses unnormalized squared diameters.
Identification with parametric area, including the existing ellipsoid measure,
and the coarea/height-density formula below still require proofs. The
coordinate sup-norm Hausdorff measure is not a substitute for Euclidean area.

**Proof.** By regularity and compactness of the joint there is a collar
$`0\le h\le\delta`$ with no critical points. Coarea gives a $`C^1`$
function on this interval,

```math
 B(s)=\int_{h=s}\frac{dA_s}{|\nabla h|},\qquad
 B(0)=\int_{\partial\Omega}\frac{dA}{|\nabla h|}.
```

The contribution of this collar to (13) is

```math
 \int_0^{\delta/\varepsilon}G(u)B(\varepsilon u)\,du.
```

Using (15), its difference from $`B(0)`$ is bounded by

```math
 \|B'\|_\infty\varepsilon\int_0^\infty u|G(u)|\,du
 +|B(0)|\int_{\delta/\varepsilon}^\infty|G(u)|\,du
 =O(\varepsilon)+O(\varepsilon^2).
```

For sufficiently small $`\varepsilon`$, on the remainder $`h\ge\delta`$
the tail estimate gives
$`|G_\rho(h)|\le C\varepsilon^2 h^{-3}`$. Its integral is
$`O(\varepsilon^2|\Omega|\delta^{-3})`$. This argument permits critical
points of $`h`$ away from the joint; no regularity of interior level sets
is being assumed. The first equality in (17) follows.

At a joint point let $`n`$ be the inward unit spatial normal and
$`k=|\nabla h|\in(0,1)`$. The tangent vectors orthogonal to the joint and
pointing into the respective faces can be chosen as

```math
 a=(0,n),\qquad b=(-k,n).
```

Thus
$`\cosh\theta=1/\sqrt{1-k^2}`$, $`\tanh\theta=k`$, and
$`\coth\theta=1/k`$. This proves the second equality and hence the modified
conjecture for this class. $`\square`$

### Corollary 2: an explicit connected joint with nonconstant angle

Let $`b_i>0`$, $`0<a<\tfrac12\min b_i`$, and set

```math
 \Omega=\left\{\sum_{i=1}^3x_i^2/b_i^2<1\right\},\qquad
 h(x)=a\left(1-\sum_{i=1}^3x_i^2/b_i^2\right).
 \tag{18}
```

The positive-part extension is $`2a/\min b_i`$-Lipschitz. On the joint,
parametrized by $`x_i=b_i\omega_i`$,

```math
 \tanh\theta(\omega)=2a\sqrt{\sum_i\omega_i^2/b_i^2}.
```

This varies on a single connected joint whenever the axes are not all equal.
Since

```math
 |\{h>s\}|=\frac{4\pi}{3}b_1b_2b_3(1-s/a)^{3/2},\qquad 0\le s\le a,
```

Theorem 2 gives the completely explicit value

```math
 \boxed{\lim_{\rho\to\infty}\mathcal A_\rho(M_h)
        =\frac{2\pi b_1b_2b_3}{a}.}
 \tag{19}
```

For $`(b_1,b_2,b_3)=(1,2,3)`$, $`a=1/4`$, the prediction is $`48\pi`$,
and $`\tanh\theta`$ ranges from $`1/6`$ to $`1/2`$. This is not merely a
family of constant-angle examples.

**Checked deterministic proof of (19), without general coarea or angle geometry.**
`EllipsoidIntegration.lean` derives the displayed superlevel volume from the
axis-scaling determinant and the Euclidean three-ball in the original spatial
product Lebesgue measure. The strict superlevel set is empty for `s ≥ a`,
including the critical height. Radial spheres are null sets, so boundary
endpoint replacements are justified. For every globally continuous real `f`,
including the signed kernel at any fixed density, it proves

```math
 \int_{h>0} f(h(x))\,dx
 =C\int_0^a\sqrt{1-s/a}\,f(s)\,ds,
 \qquad C=\frac{2\pi b_1b_2b_3}{a}.
```

Compact spatial boxes and continuity give absolute integrability. After
axis/radial integration, the substitution is performed in the smooth direction
`t = 1-r²`, then `s = a*t`. This is important: the square-root height density
is **not globally C¹**, and the interior critical level `s = a` cannot be
handled by silently applying the regular-collar argument there. No derivative
of the square root at this endpoint is used in the checked proof.

`EllipsoidLimit.lean` instead defines the continuous global extension
`B(s) = C sqrt((1-max(0,s)/a)₊)`. It equals `C` below zero, the exact height
density on `[0,a]`, and zero for `s ≥ a`, with `|B| ≤ |C|`. Combining (13),
the exact signed integration formula, and (14) gives exactly

```math
 \mathrm{continuumMean}_\rho(M_h)
 =\int_0^\infty G(u)B(\varepsilon u)\,du,
 \qquad \varepsilon=(\sqrt{\sqrt\rho})^{-1}.
```

Both the extended height integral and this rescaled integral are proved
absolutely integrable; the latter is dominated by `|C| |G|`. The extension
adds only zeros, so there is no unproved moving-domain or interior remainder
step. The checked density-to-width limit and concrete signed-rescaling theorem
now give `B(0) = C`. The whole ellipsoid, including its critical point and the
kernel's negative tail, is retained. No extra assumptions on volume, reduction,
normalization, or spacelikeness are added.

This is the audited proof term `ellipsoidLimitGoal : EllipsoidLimitGoal`,
not merely a definition of the desired conclusion. It establishes the
**deterministic** value in (19). The identification with a Poisson expectation
and general Theorem 2 remain draft-level. No quantitative rate follows from
this checked limit.

**Checked geometric interpretation of the concrete ellipsoid.** The separate
modules `EllipsoidJoint`, `EllipsoidAngle`, and `EllipsoidSurface` now interpret
(19) geometrically under the original hypotheses, without changing or reproving
`ellipsoidLimitGoal`. The smooth profile has Euclidean gradient
`(−2a xᵢ/bᵢ²)`, nonzero differential on the joint, and inward unit normal
`n = ∇h/‖∇h‖`; its outward normal is `−n`. The original axes give strict
`0 < k = ‖∇h‖ < 1`. The explicit positive rapidity
`θ = log((1+k)/sqrt(1−k²))` has the stated cosh, sinh, tanh, and coth identities.
The vectors `(0,n)` and `(−k,n)` are checked face tangents orthogonal to the
joint; their normalized inner product is `−cosh θ` in Lean's opposite
`(+---)` signature. The positive branch is proved, not inferred from the
squared algebra lemma.

For area, the entire Euclidean sphere parametrizes the joint by
`Φ(ω)ᵢ = bᵢ ωᵢ`, with checked inverse. Its derivative's cross-product identity
and Gram determinant prove the positive area Jacobian
`Jac₂ Φ = (∏ bᵢ) ‖(ωᵢ/bᵢ)‖`. The explicit parametric induced measure transports
this density times mathlib's Euclidean polar sphere measure. The latter's
mass `4π` is derived from the three-ball volume and polar measure construction;
no ellipsoid surface-area identity is assumed. This global parameterization
has no seams, omitted poles, or null-boundary replacements, and is not a claim
about general Hausdorff-area/coarea infrastructure.

The measurable density cancels the proved weight pointwise:
`Jac₂ Φ · coth θ = (∏ bᵢ)/(2a)`. Finite spherical area establishes absolute
integrability and the exact integral `2π(∏ bᵢ)/a`. The theorem
`ellipsoid_limit_eq_joint_integral` combines this with the existing deterministic
limit. Connectedness follows from the sphere; axis endpoint weights
`bⱼ/(2a)` prove nonconstancy for unequal axes. The `(1/4, ![1,2,3])` regressions
check slopes `1/2, 1/6`, weights `2, 6`, and surface integral `48π` alongside
the unchanged deterministic regression. This completes only the concrete
ellipsoid interpretation: general Theorem 2, arbitrary null boundaries,
induced null-joint geometry, and the probability bridge remain separate.

## 7. What remains outside this attempt

- Two independently curved spacelike faces: the exact future-cone reduction
  fails. A new estimate for the bilocal kernel is needed.
- General dimension: neither four-dimensional kernel reduction is being
  asserted unchanged in other dimensions.
- General null boundaries, tangential/degenerate joints, or varying the
  geometry simultaneously with density.
- Variance and convergence in probability of the unsmeared random action.
- Independent proof review and a broader novelty/literature check.

A tempting but invalid shortcut is to say that the kernel localizes at short
coordinate separations and then add local wedge answers. Nearly null pairs
can have macroscopic coordinate separation and small interval volume. Our
proofs avoid that step: the complete future integral is done exactly first,
and the remaining limit has an explicit dominating bound or an integrable
signed-kernel estimate. Numerical agreement alone would not repair a missing
bound at this step.
