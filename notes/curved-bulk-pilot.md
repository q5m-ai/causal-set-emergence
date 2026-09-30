# Fixed-geometry curved bulk feasibility pilot (#73)

**Decision: narrow, not a curved limit theorem.** This package supplies a
conventional analytic derivation, exact symbolic identities and numerical
regressions. It is not Lean-verified or independently human-reviewed. The
second-jet model has the expected curvature coefficient. A smooth interior
long-null sector admits signed control, but the **actual boundary-truncated
unweighted remainder is still open**. A rigorous absolute-value obstruction
rules out one tempting localization route, not Conjecture 1′ or #24.

The source baseline is `73ddd09b4a631dc2d4818d9bd2da7ef69a2ca1b1`.
[Issue #93](https://github.com/q5m-ai/causal-set-emergence/issues/93) owns the
canonical conformal finite-density definitions and Poisson API. Everything
below is analytic notation for its agreed specification, not a second
production observable or an assumed expectation identity. The old flat Lean
API and original `AdmissibleTwoFace` are unchanged.

## 1. Interface, nonvacuity and limit order

Use the existing future orientation and signature $`\eta=\mathrm{diag}(1,-1,-1,-1)`$.
Fix one original `AdmissibleTwoFace h f` region $`M`$, and on a neighborhood of
its closure a smooth positive $`\Omega`$ with fixed bounds
$`0<m\leq\Omega\leq L`$. Put $`q=\Omega^4`$ and
$`d\mu_g=q\,d^4x`$. No desired limit or cancellation is part of admissibility.
The observable is exactly

```math
\begin{aligned}
K(z)&=(1-9z+8z^2-\tfrac43z^3)e^{-z},\\
V_M(x,y)&=\int_{M\cap(I[x,y]\setminus\{x,y\})}q(z)\,d^4z,\\
P_g(\rho,M)&=\int_M\int_{M\cap J^+(x)}
 K(\rho V_M(x,y))\,d\mu_g(y)\,d\mu_g(x),\\
A_g(\rho,M)&=C\sqrt\rho[\mu_g(M)-\rho P_g(\rho,M)],
 \qquad C=\frac4{\sqrt6}.
\end{aligned} \tag{C1}
```

Here $`I[x,y]`$ is the original **closed** causal interval. Positive conformal
rescaling preserves its cones. The original lower and upper causal envelopes
make $`M`$ ambient-causally-convex: any intermediate causal point stays strictly
above the lower and below the upper envelope. Thus $`I[x,y]\subset M`$ for
endpoints in $`M`$. Removing its two endpoints changes no conformal volume,
since bounded continuous densities are atomless. Only with this argument may
we replace the restricted interval in (C1) by its ambient volume. This is not
a substitution of the flat proper-time formula.

The discrete specification remains the ordered-pair action
`4/(sqrt(6)*sqrt(rho)) * (N - N_0 + 9*N_1 - 16*N_2 + 8*N_3)`;
#93 constructs its law with intensity `rho * mu_g.restrict M` and proves any
expectation identification. We use neither a probability theorem nor a
sample-wise convergence premise here.

### Explicit curved example

In the original coordinates choose

```math
\begin{aligned}
h(\mathbf x)&=\tfrac14(1-|\mathbf x|^2),\qquad f(\mathbf x)=\tfrac18,\\
M&=\{(t,\mathbf x):|\mathbf x|^2/4-1/8\lt t\lt1/8\},\\
\Omega(t)&=(1+bt^2)^{1/4}.
\end{aligned} \tag{C2}
```

Take **$`b=1`$** for the fixed pilot; retaining $`b\geq0`$ in formulas supplies
a flat calibration, not an additional asymptotic parameter. The positive part
of $`h`$ is globally $`1/2`$-Lipschitz, its joint gradient has norm $`1/2`$,
and $`f`$ has slope zero. All face germs are smooth. This verifies the original
slope budget and regularity, including the allowed interior critical point.
The region contains the origin, is bounded, and has closure in
$`[-1/8,1/8]\times\{|\mathbf x|\leq1\}`$.
On $`U=\{|t|<1,\ |\mathbf x|<2\}`$ we can use
$`m=1`$, $`L=2^{1/4}`$. The factor is smooth and positive globally;
§2 proves its curvature is nonzero, independently of the action.

Geometry, $`b`$, all bounds, and every cutoff used below stay fixed as
$`\rho\to+\infty`$. There is **no** interchange with a shrinking cutoff,
small-curvature limit, or density-dependent geometry.

For $`\Omega=1`$, (C1) is the unchanged flat `continuumMean`, by interval
containment and the flat volume law. For a constant $`\Omega=a>0`$, direct
substitution of both endpoint measures and the interval measure gives

```math
\begin{aligned}
A_a(\rho,M)&=a^2 A_1(\rho a^4,M).
\end{aligned} \tag{C3}
```

These are written calibrations of the specified integral; formal API
identifications belong to #93. A constant factor is not a curved example.

### Pinned #93 API identification (source-level, not an integrated audit)

After the initial calculation, #93 published
[`373cacaac38f6773c09f87441fcb5d068befb55f`](https://github.com/q5m-ai/causal-set-emergence/commit/373cacaac38f6773c09f87441fcb5d068befb55f).
The [action source](https://github.com/q5m-ai/causal-set-emergence/blob/373cacaac38f6773c09f87441fcb5d068befb55f/formal/BoundaryDraft/ConformalAction.lean)
and [API note](https://github.com/q5m-ai/causal-set-emergence/blob/373cacaac38f6773c09f87441fcb5d068befb55f/formal/CONFORMAL_ACTION.md)
were inspected. The precise identification is:

```text
mu_g              <-> BoundaryDraft.conformalVolume Omega
V_M(x,y)          <-> BoundaryDraft.conformalIntervalVolume Omega M x y
A_g(rho,M)        <-> BoundaryDraft.conformalAction Omega rho M
(C1) integral     <-> conformalAction_eq_integral
ambient equality  <-> ControlledConformalFactor.intervalVolume_ambient
flat / scaling    <-> conformalAction_one / conformalAction_const
```

The source retains the original region and closed order, exclusive endpoints,
both curved endpoint measures, restricted interval volume and normalization.
Its `ControlledConformalFactor` also requires a globally measurable extension;
our globally smooth factor meets this without changing it. Its finite-density
integrability is compatible with the ordinary pair-domain split (C19), which
is an analytic identity here, not a new Lean declaration. No use is made of
its expectation theorem in any estimate above or below. At the owner's
publication of this revision, the full audit was still running; inspecting
proof terms does not certify that gate or an integrated #73/#93 build.

## 2. Curvature convention, fixed before the coefficient calculation

Let $`\Gamma`$ be the Levi-Civita connection. Our convention is

```math
\begin{aligned}
R^\alpha{}_{\beta\mu\nu}
 &=\partial_\nu\Gamma^\alpha_{\mu\beta}
   -\partial_\mu\Gamma^\alpha_{\nu\beta}
   +\Gamma^\alpha_{\nu\lambda}\Gamma^\lambda_{\mu\beta}
   -\Gamma^\alpha_{\mu\lambda}\Gamma^\lambda_{\nu\beta},\\
R_{\beta\nu}&=R^\alpha{}_{\beta\alpha\nu},\qquad
R=g^{\beta\nu}R_{\beta\nu},\\
\Box_g\phi&=|\det g|^{-1/2}\partial_\mu
 (|\det g|^{1/2}g^{\mu\nu}\partial_\nu\phi).
\end{aligned} \tag{C4}
```

Thus, writing $`\sigma=\log\Omega(t)`$, direct connection contraction gives

```math
\begin{aligned}
R_{00}&=3\sigma'',\qquad R_{ij}=-(\sigma''+2(\sigma')^2)\delta_{ij},\\
R&=6\Omega^{-3}\Omega''=3b(1-bt^2/2)(1+bt^2)^{-5/2}.
\end{aligned} \tag{C5}
```

In particular $`R(0)=3b`$, and it is positive on the entire closure of (C2)
when $`b=1`$. No action has been used to define or evaluate it. For a general
conformal factor our convention gives $`R=6\Omega^{-3}\Box_\eta\Omega`$.

**Source conversion matters.** Dowker's [2020 paper, (2.4)–(2.8)](https://arxiv.org/html/2007.13206v2#S2.SS1)
uses signature $`(-+++)`$ with $`R_{00}=-6\beta`$ and $`R=12\beta`$
at the origin for $`\Phi=1+\beta t^2`$. Reversing both the metric sign and
the Riemann convention gives (C4): Ricci components reverse but the scalar
does not. Our factor agrees to quadratic order with $`\beta=b/4`$,
so both give $`R(0)=3b`$. The source's d'Alembertian changes sign;
the action density is the negative of its advanced scalar operator. Therefore
its $`\Box\phi-R\phi/2`$ corresponds here to
$`\Box_g\phi+R\phi/2`$. This conversion is a check, **not** the derivation
of the coefficient in §4. Keeping the other Riemann sign with our signature
would instead write that curvature term as $`-R/2`$.

This also resolves the concurrent source conventions explicitly: #93's
nonzero-curvature example at the pinned revision uses the opposite Riemann
sign, so $`R_{93}=-R`$ and our candidate $`R/2=-R_{93}/2`$. Its production
finite-density API defines no curvature and imposes no bulk target; the
examples need not use the same conformal factor. The proposed #90 general
contract at [`67c2029430d8b91942e5df7c929e756b7cb85714`](https://github.com/q5m-ai/causal-set-emergence/blob/67c2029430d8b91942e5df7c929e756b7cb85714/notes/general-contract.md#curvature-sign-not-just-metric-signature)
uses exactly (C4). There is no action/region conflict or proposed interface
change. Any later scalar-curvature API must preserve this conversion rather
than treating the common metric signature as sufficient.

## 3. Actual interval and endpoint-measure corrections

Put $`\Delta=y-x=(T,\mathbf r)`$, $`r=|\mathbf r|`$,
$`s=T^2-r^2\geq0`$, $`p=(x+y)/2`$, and $`c=\pi/24`$.
A timelike flat diamond of volume $`cs^2`$ has centered second moment

```math
\begin{aligned}
\frac1{cs^2}\int_{I[x,y]}(z-p)^\mu(z-p)^\nu\,d^4z
 &=\frac{\Delta^\mu\Delta^\nu}{20}-\frac{s\eta^{\mu\nu}}{30}.
\end{aligned} \tag{C6}
```

For a rest diamond, direct spatial-ball integration gives time variance
$`s/60`$ and each spatial variance $`s/30`$. A determinant-one Lorentz
transport proves (C6); symmetry kills its odd moments. This proof also
explains why a boost is not a uniform coordinate-smallness argument.

For a $`C^4`$ density on a neighborhood of that diamond, Taylor's theorem gives

```math
\begin{aligned}
V_g(x,y)&=cs^2\left[q(p)
 +\frac{\Delta^\mu\Delta^\nu\partial_{\mu\nu}q(p)}{40}
 -\frac{s\Box_\eta q(p)}{60}+E_4\right],\\
|E_4|&\leq \frac{B_4 T^4}{24}.
\end{aligned} \tag{C7}
```

Here $`B_4`$ bounds the Euclidean operator norm of $`D^4q`$ on the diamond.
Every centered point has Euclidean distance at most $`T/\sqrt2\leq T`$:
apply the triangle inequality to its two causal endpoint displacements.
The diamond is convex, so the Taylor segments stay inside it. A common bound
is valid only on diamonds in the stated compact coordinate neighborhood.
For the endpoint form, $`C^3`$ suffices and gives

```math
\begin{aligned}
\frac{V_g(x,y)}{cs^2}&=q(x)+\tfrac12\Delta^\mu\partial_\mu q(x)
 +\frac{3\Delta^\mu\Delta^\nu\partial_{\mu\nu}q(x)}{20}
 -\frac{s\Box_\eta q(x)}{60}+E_3,\\
|E_3|&\leq\frac{\sqrt2}{3}B_3T^3.
\end{aligned} \tag{C8}
```

For (C2), $`q(t)=1+bt^2`$ is quadratic and both remainders are **identically
zero**, for all causal intervals, not merely short or weakly curved ones:

```math
\begin{aligned}
V_g(x,y)&=cs^2 H(t,T,r),\\
H&=1+b\left((t+T/2)^2+T^2/20-s/30\right)\\
 &=1+b\left(t^2+tT+3T^2/10-s/30\right).
\end{aligned} \tag{C9}
```

The formula extends to null/diagonal pairs with volume zero. The endpoint
measure is also exact: $`q(t+T)=q(t)+2btT+bT^2`$. Both factors
$`q(t)`$ and $`q(t+T)`$ must remain in the pair integral.
Notice $`m^4\leq H\leq L^4`$ on intervals in $`U`$, since $`H`$ is an
average of $`q`$, not a flat proper-time prescription.

For an explicit invariant curvature calibration take a rest diamond centered
at $`t=0`$. Its central timelike geodesic has proper duration
$`\tau=\int_{-T/2}^{T/2}(1+bt^2)^{1/4}dt`$. For $`bT^2\leq1`$,

```math
\begin{aligned}
\left|\tau/T-1-bT^2/48\right|&\leq 3b^2T^4/2560,\\
\left|\frac{V_g}{c\tau^4}-1+bT^2/15\right|&\leq b^2T^4.
\end{aligned} \tag{C10}
```

The first bound follows from the second derivative of $`(1+z)^{1/4}`$;
the second from $`|(1+a)^{-4}-1+4a|\leq10a^2`$ for $`a\geq0`$,
$`0\leq\tau/T-1\leq bT^2/48`$, and (C9). Thus the first invariant
correction is $`-(R/180+R_{00}/30)T^2=-bT^2/15`$ in (C4).
This is a rest-diamond calibration, not a claim of a uniform proper-time
expansion for infinitely boosted macroscopic diamonds.

## 4. Candidate bulk coefficient: a derived second-jet response

Fix an interior first endpoint and a fixed $`\delta>0`$ such that its future
diamond $`T+r<\delta`$ lies in $`M`$. Set
$`u=T-r`$, $`v=T+r`$; then $`s=uv`$. This is the **same coordinate cutoff**
as the existing flat `shortFuture` / `longFuture` split, not a cutoff on volume.
For the moment retain a smooth second-endpoint field $`\phi(y)`$ and the
point term $`\phi(x)`$. No weighted observable is presumed to have only
the unweighted curvature target.

Write $`q=q(t)>0`$, $`a=q'/q`$, $`d=q''/q`$, $`z=c\rho q s^2`$,
$`\phi_0=\phi(x)`$, and evaluate all field derivatives at $`x`$.
Angular averaging and keeping coordinate degree at most two in
$`q(t+T)\phi(y)K(\rho V_g)`$ gives $`q`$ times

```math
\begin{aligned}
&\phi_0 K
 +T\left[\phi_tK+a\phi_0(K+zK'/2)\right]\\
&+\left(\tfrac12T^2\phi_{tt}+\tfrac16r^2\Delta_{\mathbf x}\phi\right)K
 +aT^2\phi_t(K+zK'/2)\\
&+\phi_0 d\left[T^2K/2+z(3T^2/20-s/60)K'\right]
 +\phi_0 a^2T^2\left[zK'/2+z^2K''/8\right].
\end{aligned} \tag{C11}
```

The term with $`K''`$ cannot be discarded: it is quadratic in the first
metric derivative and contributes at the same coordinate order as $`q''`$.
This is a defined **jet model** for the integral, not a replacement definition
of (C1).

### Signed evaluation with the full normalization

After radial integration, the factor is $`2\pi\,ds`$ times the following
primitives, for $`0<s<\delta^2`$:

```math
\begin{aligned}
J_0(s)&=\int_{\sqrt s}^{(\delta+s/\delta)/2}\sqrt{T^2-s}\,dT
 =\frac{\delta^2-s^2/\delta^2}{8}+\frac{s}{4}\log(s/\delta^2),\\
J_1(s)&=\int_{\sqrt s}^{(\delta+s/\delta)/2}T\sqrt{T^2-s}\,dT
 =\frac{(\delta-s/\delta)^3}{24},\\
J_2(s)&=\int_{\sqrt s}^{(\delta+s/\delta)/2}T^2\sqrt{T^2-s}\,dT
 =\frac{\delta^4-s^4/\delta^4}{64}+\frac{s^2}{16}\log(s/\delta^2).
\end{aligned} \tag{C12}
```

Substitute $`T=(v+s/v)/2`$ to verify these exactly. The original kernel has

```math
\begin{aligned}
M(j)&=\int_0^\infty w^jK(w^2)\,dw
 =-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2),\\
M(0)&=M(1)=M(2)=0,\qquad M(3)=-\tfrac12,\\
\int_0^\infty w\log w\,K(w^2)\,dw&=\tfrac1{12},\\
\int_0^\infty w^2\log w\,K(w^2)\,dw&=-\frac{\sqrt\pi}{12}.
\end{aligned} \tag{C13}
```

The Mellin identity is for $`j>-1`$; its log derivatives are justified by
absolute domination on compact subintervals of that range. Integration by
parts multiplies the critical second log moment by $`1,-3/2,15/4`$ when
$`K`$ is replaced by $`K,zK',z^2K''`$, respectively. Boundary terms vanish.
The $`s\log s`$ term supplies **exactly** $`\phi_0/\rho`$ in the inner
integral, cancelling the point term. The first-order terms have no critical
log and vanish after normalization. The second-order log response has common
factor $`32q^{-1/2}`$, giving

```math
\begin{aligned}
D^{\mathrm{jet}}\phi
&=q^{-1/2}\left[\phi_{tt}-\Delta_{\mathbf x}\phi
 +\frac a2\phi_t+\left(\frac{3d}{4}-\frac{9a^2}{16}\right)\phi_0\right]\\
&=\Box_g\phi+\frac R2\phi_0.
\end{aligned} \tag{C14}
```

This proves the density limit of the second-jet model. Indeed (C12) contains
only the displayed logs and finite polynomials; moments through degree two
cancel, higher powers vanish after the $`C\rho^{3/2}`$ normalization, and
half-line extensions have exponentially small tails at fixed $`\delta`$.
For $`\phi=1`$ the **candidate** unweighted bulk term is consequently
$`\tfrac12\int_M R\,d\mu_g`$. At the origin it has density $`3b/2`$;
constant $`q`$ gives zero curvature and (C3). We have derived, not postulated,
this coefficient, but have not yet justified inserting it into (C1).

### Explicit remainder domain and why Taylor alone does not finish the proof

Here are bounds for the actual integrand, not just formal degree counting.
For the pilot, choose $`\delta`$ so that
$`c_1\delta+c_2\delta^2\leq1/2`$, where
$`c_1=|a|/2`$, $`c_2=|d|/6`$. Then

```math
E_1=aT/2,\quad E_2=d(3T^2/20-s/60),\quad
\rho V_g=z(1+E_1+E_2),\quad |E_1|\leq c_1T,\quad |E_2|\leq c_2T^2.
```

Define $`p_k(z)=e^zK^{(k)}(z)`$, a cubic polynomial, and
$`D_k(z)=e^{-z/2}\sum_{j=0}^3|[z^j]p_k|(3z/2)^j`$.
Thus $`D_k`$ bounds the derivative on $`[z/2,3z/2]`$.
Taylor's theorem for $`K`$ and the omitted cross terms in $`(E_1+E_2)^2`$
give an error at most $`T^3 C_K(z)`$ in its degree-two model, with

```math
\begin{aligned}
C_K(z)&=\frac{(c_1+c_2\delta)^3}{6}z^3D_3(z)
 +(c_1c_2+c_2^2\delta/2)z^2D_2(z).
\end{aligned} \tag{C15}
```

For $`F(y)=q(t+T)\phi(y)`$, assume $`C^3`$ on the same closed diamond
with Euclidean derivative bounds $`B_i=\sup\|D^iF\|`$, $`0\leq i\leq3`$.
Its angular Taylor remainder is at most $`C_FT^3`$,
$`C_F=\sqrt2 B_3/3`$. Let
$`k_1=c_1zD_1`$ and $`k_2=c_2zD_1+c_1^2z^2D_2/2`$.
Multiplying the two Taylor polynomials and retaining all degrees through two
bounds the remainder in (C11), including its outside $`q`$, by

```math
\begin{aligned}
&T^3\mathcal E(z),\\
&\mathcal E=C_FD_0+(B_0+B_1\delta+B_2\delta^2)C_K
 +B_1k_2+B_2k_1+B_2\delta k_2.
\end{aligned} \tag{C16}
```

All constants are finite for the stated fixed compact domain. The envelope
is a polynomial times $`e^{-z/2}`$ and therefore integrable after $`z=w^2`$.
Nevertheless, taking absolute values before integration yields only

```math
\begin{aligned}
C\rho^{3/2}\left|I_{\mathrm{short}}-I_{\mathrm{jet}}\right|
&\leq \frac{2\pi C\delta^5}{5\sqrt{cq}}\,\rho
 \int_0^\infty\mathcal E(w^2)\,dw.
\end{aligned} \tag{C17}
```

We enlarged to $`0<T<\delta,\ 0<s<T^2`$ and used
$`\sqrt{T^2-s}\leq T`$. This is a valid but **nonvanishing** bound at fixed
cutoff. It is not a lower bound, not a failed pilot, and not a counterexample.
Even an exact quadratic interval law leaves higher kernel terms requiring
signed control. C³ coordinate Taylor data or a small volume alone do not
justify the local-limit/outer-integral interchange.

### Endpoint weights

A first-endpoint weight $`w(x)`$ retains every causal partner; the exact
point/pair observable is linear in $`w`$. For a second-endpoint field its
candidate response is $`\int w(\Box_g\phi+R\phi/2)d\mu_g`$, not just
$`\int w\phi R/2\,d\mu_g`$. For compact interior smooth weights,

```math
\begin{aligned}
\int w\Box_g\phi\,d\mu_g
&=-\int g^{\mu\nu}(\partial_\mu w)(\partial_\nu\phi)\,d\mu_g.
\end{aligned} \tag{C18}
```

There are boundary flux terms without compact support. For example even in
flat space a spatially varying field has the nonzero
$`-\Delta_{\mathbf x}\phi`$ term in (C14). A partition in the first endpoint
alone introduces no second-endpoint field; replacing it with pairwise chart
restrictions does. All resulting cross-chart, cutoff, and derivative terms
must be retained. Equations (C14) and (C18) do not prove an arbitrary weighted
action limit.

## 5. Exact common decomposition and two nonlocal tests

Let $`P_<`$ and $`P_\geq`$ denote the actual pair integral in (C1), restricted
to $`v<\delta`$ and $`v\geq\delta`$, respectively. The equality case belongs
to the long part, including null points. Finite volume and bounded continuous
kernel ensure absolute integrability **at each fixed density**, so

```math
\begin{aligned}
A_g&=C\sqrt\rho[\mu_g(M)-\rho P_<]-C\rho^{3/2}P_\geq.
\end{aligned} \tag{C19}
```

For a finite smooth first-endpoint partition $`\sum_i w_i=1`$ on $`M`$,
apply the same split to each weight and allocate its point term once, to its
short part. This is a summable exact identity; it discards no partner and
asserts no asymptotics. On the pilot, the long-pair volume is exactly

```math
\begin{aligned}
V_g&=cu^2v^2H(t,u,v),\\
H&=1+b\left(t^2+\tfrac12t(u+v)+\tfrac3{40}(u+v)^2-\tfrac1{30}uv\right).
\end{aligned} \tag{C20}
```

### 5.1 A rigorous obstruction to coordinate-local or absolute localization

Fix $`x=0`$ and $`1/16\leq v\leq1/8`$. As $`u\downarrow0`$, both
endpoints stay in (C2), while

```math
\begin{aligned}
s&=uv\longrightarrow0,\\
H(0,u,v)&\longrightarrow 1+3bv^2/40\ne q(0).
\end{aligned} \tag{C21}
```

Their coordinate separation does not go to zero. In particular there is no
uniform bound $`|V_g-cq(x)s^2|\leq C_0s^3`$ on this long sector: dividing
by $`cs^2`$ contradicts (C21). At $`u=\alpha/\sqrt\rho`$, the true
kernel argument tends to $`c\alpha^2v^2(1+3bv^2/40)`$, not
$`c\alpha^2v^2`$. Freezing the phase at the first endpoint is not a
uniformly small error in the density limit. This does not rule out a signed
cancellation using the **actual** phase.

There is also an explicit positive-measure obstruction to an absolute proof.
Use $`b=1`$, $`\delta=1/32`$, $`\beta=1/64`$ and the four-dimensional
Euclidean ball $`X=B(0,1/64)`$. For all $`\rho\geq1`$ consider

```math
\begin{aligned}
&x\in X,\quad n\in S^2,\quad v\in[v_0,v_1]=[1/16,1/8],\\
&\frac{\beta}{2\sqrt\rho}\leq u\leq\frac{\beta}{\sqrt\rho},\\
&y=x+((u+v)/2,(v-u)n/2).
\end{aligned} \tag{C22}
```

Both endpoints are strictly in $`M`$: their absolute times are less than
$`1/8`$, their spatial norms are at most $`5/64`$, and their times exceed
the lower graph (for $`y`$ its time is at least $`1/64`$).
Here $`q(x)q(y)\geq1`$, $`H\leq2`$,
$`\rho V_g\leq2c\beta^2v_1^2<1/100`$, and $`K(z)\geq1/2`$
on $`[0,1/100]`$. The coordinate pair Jacobian is
$`(v-u)^2/8\geq(v_0-\beta)^2/8`$. Consequently the **actual** long-pair
absolute integral satisfies

```math
\begin{aligned}
C\rho^{3/2}\int_{M}\int_{M\cap J^+(x),\ v\geq\delta}
 |K(\rho V_g)|\,d\mu_g(y)\,d\mu_g(x)&\geq c_*\rho,\\
c_*&=C\,|X|\,4\pi(v_1-v_0)\frac{(v_0-\beta)^2}{8}\frac\beta4>0.
\end{aligned} \tag{C23}
```

This is a falsifiable obstruction, with constants independent of density,
to dropping long partners by a vanishing absolute bound. It says nothing
about the full **signed** long integral: its other bands can and must cancel.
In particular it is not a counterexample to #24.

### 5.2 A controlling signed estimate that does survive normalization

For this paragraph only, insert a fixed $`C^3`$ pair weight compactly supported
in the interior of $`M\times M`$, with $`\delta\leq v\leq D`$ and a smooth
cutoff in a sufficiently small null collar. These are **test-sector**
hypotheses, not new geometric admissibility fields. The exact change of phase

```math
\begin{aligned}
w&=uv\sqrt{H(t,u,v)},\qquad \rho V_g=c\rho w^2.
\end{aligned} \tag{C24}
```

has positive $`u`$ derivative near zero. For the pilot,
$`H\geq1`$, $`H_u\geq-b/16`$ when $`|t|\leq1/8`$ and $`u,v\geq0`$,
so $`w_u\geq v(1-bu/32)\geq\delta/2`$ for $`bu\leq16`$.
Choose $`0<\varepsilon<\delta/2`$ with $`b\varepsilon\leq16`$.
All inverse fibres exist for $`0\leq w\leq\delta\varepsilon/2`$;
put a smooth cutoff strictly inside this common interval. The pilot phase
and its inverse are smooth. In particular, the Jacobian is C³; bounding
three derivatives of it uses four derivatives of the inverse, available
here because (C20) is polynomial and the derivative is bounded away from zero.

After including **both** endpoint densities and the Jacobian, then integrating
over $`x,v,n`$, the pair integral is
$`\int_0^\infty K(c\rho w^2)B(w)\,dw`$ with a compactly supported
$`C^3`$ amplitude on the nonnegative half-line. Compact support away from
both faces is important: it makes the region indicators identically one
where the smooth weight is nonzero. Differentiation under the remaining
finite integrals is justified by compact derivative bounds. If
$`|B'''(w)|\leq6L_B`$, Taylor's integral remainder on this whole half-line
and the three signed zero moments give

```math
\begin{aligned}
\left|C\rho^{3/2}\int_0^\infty K(c\rho w^2)B(w)\,dw\right|
&\leq \frac{CL_B}{c^2\sqrt\rho}\int_0^\infty z^3|K(z^2)|\,dz\\
&\leq\frac{99CL_B}{2c^2\sqrt\rho}.
\end{aligned} \tag{C25}
```

The last bound integrates the absolute polynomial coefficients against the
Gaussian. This is a conventional proved rate for **this test sector only**.
A compact sector away from $`w=0`$ is exponentially small by (C9) and
$`q\geq1`$. There is no curvature expansion of the exponential in this
argument: the phase straightening is exact.

The missing step for (C1) is not supplied by (C25). Its weight is the actual
indicator of $`M\times M`$, not a compact interior smooth weight. After
(C24), the boundary contacts move with $`w`$; merely differentiating the
interior integrand omits their terms. The flat long-overlap quadratic-jet
proof integrates such moving contacts, but its translation-invariant phase
and height-hinge representation do **not** already prove the corresponding
curved statement. Deriving a right quadratic jet with dominated little-o
remainder for this actual transformed amplitude, or another signed estimate,
remains open. The short-sector remainder in (C17) is open as well.

## 6. Literature audit: coefficient agreement is not a new global theorem

The following source versions were inspected for this pilot, not as an
exhaustive novelty search:

- **Belenchia–Benincasa–Dowker**, [arXiv:1510.04656v2](https://arxiv.org/html/1510.04656v2),
  §§II–III and Appendix A's role in §III. Their four-dimensional scalar-operator
  calculation explicitly separates the near region, the long light-cone
  neighborhood, and the deep timelike region. §III assumes compact field
  support, unique light-cone generators (no relevant caustics), suitable null
  coordinate tubes, differentiable interval/measure/field expansions
  (63)–(65), and small relative phase corrections. It handles signed
  cancellation rather than a vanishing absolute kernel norm. Their near/long
  coordinate matching and bounds are not an already-proved uniform outer
  integral theorem for indicators of arbitrary two-face regions. Conformal
  coordinates remove cone deflection in this pilot; (C9) replaces unknown
  interval coefficients by an exact expression. Neither fact removes our
  boundary-contact or outer-integration obligation. We do not import an
  unspecified finite regularity threshold from that paper.
- **Dowker**, [arXiv:2007.13206v2](https://arxiv.org/html/2007.13206v2),
  §§1–2, §4 and §5. Its conformal factor is $`1+\beta t^2`$, not our
  fourth root. In §2 it explicitly drops higher curvature orders assuming
  no divergences from them; §5 says that rigor requires bounds showing
  their normalized contributions vanish. With $`\beta=b/4`$, its (2.16)–(2.17)
  in four dimensions agrees with the first-order part of (C9). Our polynomial
  **volume density** makes that interval expression exact, but does not make
  the kernel linear in curvature. We do not cite its truncated action as
  remainder control.
- **Machet–Wang**, [arXiv:2007.13192v2](https://arxiv.org/html/2007.13192v2),
  §§2–4. The small causal-diamond calculation is first order in curvature,
  using Riemann normal coordinates and a diamond small relative to curvature
  scales. Its null-boundary diamond is not this fixed two-spacelike-face
  class. Its bulk/joint agreement is relevant prior evidence, not a proof
  of the full remainder in (C19).

The $`R/2`$ coefficient and light-cone cancellation mechanism are prior work.
The contribution here is a bounded, exact-interval pilot, explicit convention
conversion, normalization/weight checks, and a precise route obstruction and
remaining interface. Local agreement is not evidence that every hypothesis
of a global curved theorem has been met.

## 7. Go / narrow / stop inputs for #74 and #75

**Go:** use (C1), the original region class, conformal measure and causal
interval convention from #93. Use the exact split (C19), one fixed
$`v`$ cutoff, and finite first-endpoint partitions retaining all partners.
Use (C9) as an analytic regression, (C14) only as a jet-model coefficient,
and (C25) only for its stated smooth interior sectors.

**Narrow #74:** before claiming a bulk theorem, prove a signed estimate for
both the actual short remainder and the boundary-truncated, phase-straightened
long amplitude. Include all moving-contact terms and an integrable bound in
the first endpoint. Do not posit that jet as an admissibility condition.
Start with the exact $`q=1+t^2`$ pilot, original C³ faces, compact closure,
strict original slope/joint margins, a smooth positive conformal factor with
explicit bounds, and a fixed cutoff. Any extension to arbitrary smooth
$`\Omega`$ needs a geometric derivation of the null phase and its regularity,
not just (C7). The full pilot limit is **not** licensed by this package.

**Narrow #75:** keep it blocked on the same decomposition and the actual
#93 API. Pointwise conformal geometry gives $`n_g=\Omega^{-1}n_\eta`$,
unchanged positive-normal angle, and $`dA_g=\Omega^2dA_\eta`$ on a two-dimensional
joint. These geometric facts do not prove an action coefficient. Tangent
comparison must keep (C20), both endpoint measures, cross-chart pairs,
single-face terms and (C18)'s derivatives. Do not transport the flat global
unweighted theorem into arbitrary weighted curved patches. For a varying-angle
regression, also use $`h=(1-x_1^2-x_2^2/4-x_3^2/9)/4`$, $`f=1/8`$,
with the same conformal factor: it is an original admissible ellipsoid,
has flat angle weights $`2`$ and $`6`$ at two axis endpoints and nonzero
spacetime curvature. Its geometry is fixed; only enlarge $`U`$ spatially.

**Stop these routes:** freezing the long phase at $`q(x)`$, treating small
$`V_g`$ as coordinate locality, dropping long partners by absolute domination,
or replacing a weighted response by its unweighted target. Equations
(C21)–(C23) rigorously obstruct the first three shortcuts; (C14)/(C18)
exhibit the missing derivative terms in the last.

Before #74/#75 implementation, compare these interfaces to #93's **proved**
API at its recorded source revision. This note works from the agreed
specification; it does not certify a concurrent branch's unobserved proofs.
If the missing signed estimate has a surviving term, retain it and revise the
target. Failure of a bound alone does not revise #24's conjecture.

## 8. Reproduction and claim ledger

- `curved_bulk_pilot.py` derives the exact density/interval identities and
  second-jet response; `test_curved_bulk_pilot.py` supplies independent
  Christoffel contraction, rest/boosted interval quadrature, radial primitives,
  log moments, calibrations, derivative negative controls and null scaling.
- `check_symbolic.py` includes the new exact identity checks. Run the pinned
  Python environment as in the root README, then `python check_symbolic.py`,
  `python -m unittest -v`, and the Markdown checks.
- Quadrature tests detect regressions, **not** full-action convergence. No
  numerical fit to the complete curved action is asserted.
- Written analytic results: (C3), (C6)–(C10), the jet-model limit (C14),
  explicit remainder bounds, exact decomposition, obstruction (C23), and
  smooth-sector estimate (C25). Their conventional proofs are above.
- Lean verification: **none added**; no Lean/checker/build inputs changed.
  Any later Lean implementation requires the full integrated `formal/check.sh`
  source/transitive-axiom audit on the exact integrated head, not this package's
  Python checks or another branch's audit.
- Independent human review: **outstanding**. Complete deterministic curved
  limit, its expected-action transfer, shrinking-cutoff uniformity, full-action
  rates and individual-sprinkling convergence: **not proved here**.
