# A corrected curved-4D convergence theorem with retained focusing (#151)

**Written theorem for a geometrically specified infinite-dimensional class,
not a restored universal G-SS claim.** Every smooth positive factor depending
on time and circle position in (RC1) satisfies the complete deterministic
curvature-target limit and, separately, the original-law expectation limit.
The proof derives the actual weighted interval, both-measure pushforward,
closing-contact terms and critical signed estimates. It does not put a
vanishing long response into the hypotheses.

This continues the exact audited PR #164 head
`41ce274cb5c2066d6f00dcaa6ff4480c1727f863`, preserving its written quartic
obstruction and all integrated results, including #149/PR #163. No predecessor
proof or receipt is revised. The new estimates below are conventional written
analysis, not Lean proofs, validated numerical certificates or independent
mathematical acceptance. The model-only Arb certificate in #164 certifies its
stated model, not this theorem. Final scrutiny remains with #94/#86.

## 1. Checkable geometric hypotheses and the theorem

Let Omega be any **fixed smooth strictly positive function on**
`R x (R/20Z)`. There is no smallness, polynomial, time-independence or
reflection-symmetry requirement. In particular it can vary along the spatial
circle. It is independent of the sphere position. Set

```math
\begin{aligned}
X&=S^2_1\times(\mathbb R/20\mathbb Z),&
M&=(-2,2)\times X,\\
g_0&=dt^2-h_{S^2_1}-dz^2,&
g&=\Omega(t,z)^2g_0,& \omega&=\Omega^4,\\
\mathcal T_g
 &=\frac12\int_M R_g\,d\mu_g
 =4\pi\int_{-2}^{2}\int_0^{20}
   [\Omega^2+3\Omega(\Omega_{tt}-\Omega_{zz})]\,dz\,dt,\\
\lim_{\rho\to\infty}\mathcal A_{\rho,4}(M,g)
 &=\mathcal T_g,
 &\lim_{\rho\to\infty}\mathbb E_{\rho\mu_g}
       A^{\mathrm{disc}}_{\rho,4}&=\mathcal T_g.
\end{aligned}\tag{RC1}
```

These hypotheses can be checked directly on the metric, conformal factor,
periods and boundary. They contain no condition on an action coefficient,
volume inverse, Mellin pole or desired limit. Bounds on finitely many
Omega derivatives and a positive lower bound on compact tubes follow from
smoothness and positivity; their sizes need not be small. The constants and
cutoff in the proof can depend on this fixed factor. This is not a theorem
uniform over factors approaching zero or with unbounded derivatives.

### Admissibility, order and independent target

Positive conformal rescaling preserves causal curves, their orientation,
and unparameterized null geodesics. Thus the selected **ambient** order is
exactly SA1 of the [complete sphere-circle theorem](sphere-circle-assembly.md):
time difference at least the square root of squared round sphere distance
plus squared shortest-circle distance. The compact complete spatial product
makes the base globally hyperbolic; conformal invariance preserves this.
Constant-time slices remain Cauchy and spacelike. The closure of M is compact,
and its whole frontier consists of its past and future slices. The joint is
empty, with no evaluation of coth at a zero angle. Time monotonicity separately
proves ambient interval containment. Every G-SS clause is therefore satisfied.

The two measures and curvature are obtained directly from the metric:
`dmu_g=omega dt dA dz` and, in the repository's Riemann convention,
`R_g=2/Omega^2+6*(Omega_tt-Omega_zz)/Omega^3`. The base scalar two is the
independent product contraction in SA2; the conformal formula has the same
sign as [CA2](curved-assembly.md). These give RC1 **before** calculating the
action. The Weyl square is `4/(3*Omega^4)>0`, so this family is not a
conformally flat coordinate pilot. Antipodal endpoints still admit the whole
circle of minimizing null meridians. No caustic has been removed.

## 2. What the comparisons actually suggest

| Existing result | Mechanism that matters here | What it does not justify |
| --- | --- | --- |
| [Quartic complete obstruction](curved4-complete-action-obstruction.md), CO5–CO16 | Fully matched physical pole at `9/7`, nonzero kernel multiplier, negative normalized growth `rho^(3/14)` | A universal 4D limit, or replacing a physical residue by model positivity alone |
| [Sphere-circle assembly](sphere-circle-assembly.md), SA6–SA10 | Endpoint measure makes the antipodal cubic primitive remainder summable; regular complement and short action are also restored | Arbitrary spacetime weights in the old cut proof; the present extension requires new estimates |
| [Controlled conformal assembly](curved-assembly.md) and [contact averaging](curved-contact-long.md), A4–A14 | Actual interval phase, both moving roots, time averaging before domination | Inferring arbitrary conformal-factor coverage from the old fixed density `1+t^2` |
| [Nonpolynomial control](general-metric-atlas-gate.md#3-c--nonpolynomial-conformal-branch) | A separately derived phase and contact transport, not a curvature truncation | Generic spatially dependent factors or focusing geometries |
| [General short theorem](general-metric-short-remainders.md), S30 | Actual short action, one point term, independent bulk/joint and local shell restoration | A long inverse or cancellation through a macroscopic caustic |
| [Signed-response criterion](curved4-physical-response.md), CP7–CP8 | Summable dilation increments suffice even without a cubic Peano jet | A geometric discharge for every G-SS member |

The useful distinction is **summability after the actual endpoint averaging**,
not the mere presence of a caustic. Sections 3–5 derive that summability for
RC1. Section 6 isolates its geometric power threshold and compares the
quartic failure. Conditions such as “no caustics,” “finitely many branches,”
“ordinary folds,” convexity, Einstein equations or an energy condition are
not asserted to suffice. None replaces an actual interval/contact estimate.

## 3. Exact physical interval and the complete pair measure

Write theta for round sphere endpoint distance, b for shortest signed circle
separation, tau for time separation, and s,z for source time and circle
position. All causal pairs satisfy `|b|<=tau<4<10`. The same injective
**whole-interval** circle lift proved in F1 applies because the order is
unchanged. There is no corresponding unique-geodesic assertion on the sphere.
For a lifted intermediate point with sphere distances r1,r2 and circle
coordinate Z relative to the source, the physical volume is

```math
\begin{aligned}
V_g(s,z;\tau,\theta,b)
 &=\int_{S^2}\int_{\mathbb R}
 \mathbf1_{\{d_1+d_2\lt\tau\}}
 \int_{d_1}^{\tau-d_2}\omega(s+t,z+Z)\,dt\,dZ\,dA,\\
d_1&=\sqrt{r_1^2+Z^2},&d_2&=\sqrt{r_2^2+(Z-b)^2},\\
\omega_-W(\sqrt{\tau^2-b^2},\theta)
 &\le V_g\le
 \omega_+W(\sqrt{\tau^2-b^2},\theta),
 &0&\lt\omega_-\le\omega\le\omega_+.
\end{aligned}\tag{RC2}
```

An empty fibre contributes zero, not an oriented integral. This counts the
union of all causal routes once, including the secondary transition and
antipodal meridians. W is the actual unweighted F1 volume; its bounds can
be transferred by RC2, but its value cannot be substituted for V_g. The
constants are compact bounds on the entire relevant interval tube.

First straighten **both endpoint times**, without averaging the phase away:
`s=-2+xi*(4-tau)`, with `0<=xi<=1`, and write V_g with these actual endpoints.
The time-coordinate Jacobian is `4-tau`. Sphere rotations still preserve g
because Omega is independent of sphere position. Thus the full pair integral is

```math
\begin{aligned}
P_g(\rho)&=8\pi^2\int_0^{20}dz\int_0^1d\xi
 \int_0^\pi\sin\theta\,d\theta
 \int_{\theta}^{4}d\tau
 \int_{-\sqrt{\tau^2-\theta^2}}^{\sqrt{\tau^2-\theta^2}}
 (4-\tau)\omega(s,z)\omega(s+\tau,z+b)
 K_4(\rho V_g)\,db,\\
K_4(v)&=(1-9v+8v^2-\tfrac43v^3)e^{-v},\\
\mathcal A_{\rho,4}
 &=\frac4{\sqrt6}\,[\sqrt\rho\,\mu_g(M)-\rho^{3/2}P_g(\rho)].
\end{aligned}\tag{RC3}
```

Both endpoint densities, source circle length 20, and both signs of b remain.
One must **not** double a positive-b integral for a general Omega. At the
closing `tau=4`, xi degenerates only on a null boundary and the Jacobian is
zero; its neighborhood is retained. The source interval and target interval
in time are not replaced by a value at one endpoint. All quantities are
measurable by their actual interval integrals. Finite measure and a bounded
kernel on the compact phase interval justify finite-density Fubini.

### An exact weighted fixed-diamond formula on the regular side

Set `r=sqrt(theta^2+b^2)>0`, `q=tau^2-r^2`, and let
`D0={|A|+|B|<=1/2}`, of four-volume `pi/24`. Denote F8's exact spherical to
Euclidean two-distance area ratio by Q_theta. The two orientations are
already included in that ratio. For `sqrt(theta^2+q)<2*pi-theta`, put

```math
\begin{aligned}
\ell&=\tfrac12+A,& \tau&=\sqrt{r^2+q},\\
X_1&=\theta\ell+\frac{\tau\theta}{r}B_1
                         -\frac b r\sqrt q B_3,
 &X_2&=\sqrt q B_2,\\
Z_*&=z+b\ell+\frac{\tau b}{r}B_1
                         +\frac\theta r\sqrt q B_3,
 &t_*&=s+\tau\ell+rB_1,\\
r_1^2&=X_1^2+X_2^2,&r_2^2&=(X_1-\theta)^2+X_2^2,\\
V_g&=q^2 H(r,m,\xi,z,q),& m&=b/r,\\
H&=\int_{D_0}Q_\theta(r_1,r_2)\omega(t_*,Z_*)\,dA\,dB,
 &s&=-2+\xi(4-\tau).
\end{aligned}\tag{RC4}
```

To prove this, apply the ordinary flat Lorentz/dilation map to D0 with
spatial displacement `(theta,0,b)`. Its determinant is q squared. Replacing
the Euclidean-plane point by the sphere point with the **same two distances**
has Jacobian Q_theta, leaves its time and circle coordinate unchanged, and
preserves the two inequalities defining the diamond. The regular-side
inequality ensures that the whole flat diamond is in the spherical
triangle range. Omega is unchanged by the choice of the two sphere
orientations, which is precisely where sphere-independence is used. This is
an exact change of physical coordinates, not a metric jet or a conformal
invariance claim for volume.

F8 shows that Q_theta is a smooth function of `theta^2,r1^2,r2^2` wherever
its denominator has a fixed positive margin. Its apparent zero-distance
roots are removable. On a compact set `theta<=d<pi`, its denominator is
uniformly nonzero for small q. The integrand in RC4 is smooth in
`h=sqrt(q)`. Reflection of B2,B3 makes its integral even in h. Smooth even
functions are smooth functions of h squared on the closed half-line:
Taylor's formula with integral remainder proves each order using twice as
many h derivatives, uniformly on the compact parameter set. **Omega need
not be analytic.** At theta zero, reflection of B3 also makes the integral
even in theta, including the argument of omega. Thus it is smooth in
`theta^2`, with bounded m derivatives at `m=+1,-1`.

It follows, for every compact regular long set with `r>=delta/2`, that H is
smooth with bounded derivatives through any fixed order, and
`0<c<=H(r,m,xi,z,0)<=C`. This proves the needed uniform regular phase; it
is not inferred just from absence of conjugacy. The full spatial boost in
RC4 avoids the false singularity of a time/circle boost when
`theta,q -> 0` but b and the original time are long.

## 4. Complete off-cut long pushforward, with moving roots

Choose one sufficiently small fixed temporal cutoff delta, below every S30
threshold for this metric and below 1/4. Choose the F11–F13 constants a0,e0
smaller if necessary so `d=pi-a0>delta` and `pi+e0<4`. Short means
`tau<delta`, with equality assigned to long. On the off-cut long set
`theta<=d`, choose a fixed small phase cap w0, and use **`w=sqrt(V_g)`**.
There is no factor `pi/24` in this phase convention.

RC4 and the implicit function theorem give the actual inverse
`q=Q(r,m,xi,z,w)`, smooth on a common collar, `Q(.,0)=0`, `Q_w>0`.
It is the inverse of `q*sqrt(H)`, not of the unweighted phase. Pairs with
`r<delta/2` in long have a fixed positive phase gap by RC2 and compactness;
shrink w0 to exclude them only from this **small-phase collar**. They remain
in the positive-phase complement.

Put `tau=sqrt(r^2+Q)`, s as in RC3, and define

```math
\begin{aligned}
f(r,m,\xi,z,w)
 &=\frac{r^2\mathrm{sinc}(r\sqrt{1-m^2})}{2}
 \left(\frac4\tau-1\right)
 \omega(s,z)\omega(s+\tau,z+rm)Q_w,\\
R_T^2+Q(R_T,m,\xi,z,w)&=T^2,
 &T&\in\{\delta,4\},\\
R_d(m)&=\frac d{\sqrt{1-m^2}},\\
R_d(\sigma n_\sigma)^2+
 Q(R_d(\sigma n_\sigma),\sigma n_\sigma,\xi,z,w)&=16,
 &\sigma&\in\{-1,1\},\\
B_o(w)&=8\pi^2\sum_{\sigma=\pm1}\int_0^{20}dz\int_0^1d\xi
 \left[\int_0^{n_\sigma(w)}\int_{R_\delta}^{R_d}f\,dr\,dn
       +\int_{n_\sigma(w)}^1\int_{R_\delta}^{R_4}f\,dr\,dn\right].
\end{aligned}\tag{RC5}
```

In the last line f and all radial roots use `m=sigma*n`; n_sigma also
depends on xi,z. R4 is only needed on its displayed directional domain,
where the sphere coordinate is below d. A slightly larger regular chart
supplies harmless extensions for differentiating the roots. At zero phase
`R_T=T` and `n_sigma=sqrt(1-d^2/16)` is strictly between zero and one.
The radial root derivative is `2*r+O(w)`, bounded below at both contacts.
At the outer intersection, the n derivative at zero is
`2*d^2*n/(1-n^2)^2>0`. Compact implicit-function bounds therefore control
**all** the displayed roots uniformly, including their mixed xi,z derivatives.

The spatial Jacobian in RC5 is exactly
`sin(theta) dtheta db = r^2 sinc(theta) dr dm`; the factor one-half comes
from `d tau=dq/(2*tau)`. Thus `P_o=integral K_4(rho*w^2) B_o(w) dw`
on the small collar. Each radial and n integral transports to a fixed unit
interval using its **moving** endpoints. Bounded derivatives through third
order give `B_o=b0+b1*w+b2*w^2+O(w^3)`. The coefficients are its actual
right derivatives, obtained by differentiating RC5, not prescribed constants.
In particular SC7's full Leibniz formulas apply to each radial integral and
then again to the two outer n integrals. Terms from R_delta, R4 and n_sigma
are retained. Vanishing of f at the upper time contact does not set its
higher boundary derivatives to zero.

This proves the off-cut critical signed estimate in section 7. It includes
all long circle-axis partners, both circle directions, both physical time
contacts and the artificial sphere boundary. It does not differentiate the
old reduced square-root time weight at fixed theta, nor import its
unweighted inverse into the new metric.

## 5. Weighted focusing neighborhood: closing first, then domination

Let `a=pi-theta`, `u=theta+e`, with `0<=a<=a0`, `0<=e<=e0`.
This whole neighborhood is long. Instead of integrating b into the old G,
straighten its **actual** closing interval before expanding any volume:

```math
\begin{aligned}
B(u)&=\sqrt{16-u^2},& b&=B(u)v,&-1&\le v\le1,\\
\tau&=\sqrt{u^2+B(u)^2v^2},&s&=-2+\xi(4-\tau),\\
j(a,e,\zeta)
 &=(4-\tau)\frac{uB(u)}\tau
       \omega(s,z)\omega(s+\tau,z+b),
 &\zeta&=(v,\xi,z),\\
d\nu_c&=8\pi^2\sin a\,j(a,e,\zeta)\,da\,de\,d\zeta,
 &d\zeta&=dv\,d\xi\,dz.
\end{aligned}\tag{RC6}
```

Indeed `d tau db = (u/tau) du db` at fixed b, then the Jacobian of
`(u,v)->(u,b)` is B(u). Here B(u) stays bounded away from zero because
`u<=pi+e0<4`. Every factor in j is smooth with bounded derivatives on the
closed parameter box. At `v=+1,-1`, the original time gap vanishes;
`4-tau=B(u)^2*(1-v^2)/(4+tau)` makes this regularity explicit. This retains
sources and circle partners in moving closing fibres, rather than
freezing their limiting b window. No differentiation of a fractional-power
post-integrated weight is required.

### Deriving, rather than assuming, the regular-wedge bounds

For `0<=e<=eta*a`, use the exact F9 sphere map and the bounded time/circle
boost (u is near pi). Its time and circle coordinates on D0 are

```math
\begin{aligned}
q&=e(2\theta+e),&u&=\theta+e,\\
t_*&=s+\tau(\tfrac12+A)+\frac{\tau\theta}{u}B_1
                         +\frac b u\sqrt q B_3,\\
Z_*&=z+b(\tfrac12+A)+\frac{b\theta}{u}B_1
                         +\frac\tau u\sqrt q B_3,\\
V_g&=e^2H_c(a,e,\zeta),\\
H_c&=(2\theta+e)^2\int_{D_0}
       Q_\theta(r_1(e),r_2(e))\omega(t_*,Z_*)\,dA\,dB,\\
r_1(e)^2&=(\theta\ell+eB_1)^2+qB_2^2,
 &r_2(e)^2&=(\theta(1-\ell)-eB_1)^2+qB_2^2,
 &\ell&=\tfrac12+A+B_1.
\end{aligned}\tag{RC7}
```

The two boosts in RC4 and RC7 parameterize the same physical interval;
neither is asserted to preserve the conformal density. The omega factor
inside each integral is essential.

Here is the uniform estimate with the new weight. The pointwise complex
disk argument of F9–F11 bounds Q_theta and its e derivatives by
`C_j*a^(-j)*Q_theta(r1(0),r2(0))` on a smaller disk. Its zero-probe integral
is between positive constants times `a^(-1/2)`. The Q factor is independent
of B3. Pair the B3 and minus-B3 values of omega in RC7. Their average is an
even smooth function of sqrt(q), whose q derivatives through fourth order
are uniformly bounded by the integral-remainder argument following RC4.
All remaining arguments s,b,tau,u have bounded e derivatives on this box,
including the closing boundary. Applying the product rule inside the
integral now gives, for a single sufficiently small eta,

```math
\begin{aligned}
h(a,e,\zeta)&=\sqrt a\,H_c(a,e,\zeta),\\
0&\lt c\le h(a,e,\zeta)\le C,
 &|\partial_e^j h(a,e,\zeta)|&\le C_j a^{-j}
 \quad(0\le j\le4),\\
c\,\frac{e^2}{\sqrt{a+e}}
 &\le V_g(a,e,\zeta)\le
 C\,\frac{e^2}{\sqrt{a+e}}
 \quad(0\le a\le a_0,\ 0\lt e\le e_0).
\end{aligned}\tag{RC8}
```

The lower zero-probe bound uses omega_->0; shrinking eta controls the
variation and the positive derivative of `e*sqrt(H_c)` in the regular
wedge. The last line follows on the **entire** cut box from RC2 and F13.
It includes `e=2*a` and the full-meridian regime without differentiating
through their secondary transition. Positivity comparisons alone would
not supply the first two lines; the weighted fixed-domain argument does.

### The actual sublevel primitive and its integrable remainder

Do not assume global monotonicity of V_g as e varies with the moving b.
Define its physical sublevel primitive directly:

```math
\begin{aligned}
f_c(a,\zeta,w)
 &=\int_0^{e_0}j(a,e,\zeta)
                 \mathbf1_{\{V_g(a,e,\zeta)\le w^2\}}\,de,\\
N_c(w)&=8\pi^2\int_0^{a_0}\sin a
                     \int f_c(a,\zeta,w)\,d\zeta\,da.
\end{aligned}\tag{RC9}
```

This is a capped primitive of the actual positive pair measure at all w.
It is measurable by Tonelli, with no geodesic branch choices. For
`w<=kappa*a^(3/4)`, RC8 puts **every** sublevel point in the regular wedge;
there the phase is strictly increasing and has a unique inverse E(a,zeta,w).
Consequently f_c is the integral of j from zero to E in that wedge. Set
`H_i=partial_e^i H_c(a,0,zeta)` and `j_i=partial_e^i j(a,0,zeta)`.
Direct inversion, including both endpoint densities and closing Jacobians,
gives its actual first three coefficients:

```math
\begin{aligned}
\alpha_1&=H_0^{-1/2},&
\alpha_2&=-\frac{H_1}{2H_0^2},&
\alpha_3&=\frac{5H_1^2}{8H_0^{7/2}}-\frac{H_2}{4H_0^{5/2}},\\
c_1&=j_0\alpha_1,&
c_2&=j_0\alpha_2+\tfrac12j_1\alpha_1^2,&
c_3&=j_0\alpha_3+j_1\alpha_1\alpha_2+\tfrac16j_2\alpha_1^3,\\
|c_i(a,\zeta)|&\le C_i a^{1-3i/4}\quad(i=1,2,3).
\end{aligned}\tag{RC10}
```

Rescale `e=a*E`, `w=a^(3/4)*W`. RC8 gives a uniformly smooth positive
inverse at W=0, so the cubic remainder quotient in the regular wedge is
bounded by `C*a^(-5/4)` and tends to zero for each fixed a>0 and zeta.
Outside that wedge RC8 bounds every sublevel point by
`e<=C*(a^(1/4)*w+w^(4/3))`. For `w>=kappa*a^(3/4)` this is at most
`C*w^(4/3)`. Bounded j therefore gives
`|f_c|/w^3<=C*w^(-5/3)<=C*a^(-5/4)`; RC10 gives the same bound for each
subtracted term. Multiplying by the **actual** endpoint measure proves

```math
\begin{aligned}
\left|\sin a\,
 \frac{f_c-\sum_{i=1}^3c_iw^i}{w^3}\right|&\le C a^{-1/4},\\
N_c(w)&=n_1w+n_2w^2+n_3w^3+w^3\varepsilon_c(w),\\
n_i&=8\pi^2\int_0^{a_0}\sin a\int c_i(a,\zeta)\,d\zeta\,da,
 &\varepsilon_c(w)&\longrightarrow0,
 &|\varepsilon_c(w)|&\le C.
\end{aligned}\tag{RC11}
```

The majorant is integrable in a and in every remaining compact source/partner
parameter. Dominated convergence proves RC11. This is the missing weighted
extension, not an invocation of F16 for arbitrary weights. No uniform cubic
jet at the exact antipode, derivative through `e=2*a`, negligible focusing
neighborhood, or source-only domination has been assumed. The null boundary
and the exact antipode have zero pair measure, but that fact alone is not
used as a normalized estimate.

## 6. A sufficient geometric power test, and why quartic focusing escapes

The argument exposes a reusable sufficient **lens-scaling** test. It is not
an assertion that every caustic admits these data. Suppose an actual resolved
pair chart has measure `a^nu j(a,e,zeta) da de dzeta` with compact zeta,
and its regular wedge is `0<=e<=eta*a^beta`. Suppose geometry supplies

- `V=e^2*a^(-sigma)*h(a,e/a^beta,zeta)` with h positive and uniformly
  bounded in C³ in its second variable;
- bounded C³ density after the same e rescaling;
- confinement of every actual sublevel to the regular wedge when
  `w<=kappa*a^lambda`, and the bound `e<=C*w^(beta/lambda)` on every
  sublevel when `w>=kappa*a^lambda`, where `lambda=beta-sigma/2`
  and `w=sqrt(V)`;
- retained closing/contact coordinates and no omitted physical part.

These are finite derivative and sublevel inequalities for a physical lens,
not a cancellation or primitive-jet hypothesis. RC2/RC6–RC8 derive them
from the metric in RC1, rather than adding them to its admissibility.
For `0<beta<3*lambda`, the identical inverse/rescaling argument gives

```math
\begin{aligned}
|c_i|&\le C a^{\beta-i\lambda},\\
\left|a^\nu
 \frac{f-\sum_{i=1}^3c_iw^i}{w^3}\right|
 &\le C a^{\nu+\beta-3\lambda},\\
\nu+\beta-3\lambda&>-1
 \quad\Longrightarrow\quad
 \text{a summable cubic primitive jet and zero signed response}.
\end{aligned}\tag{RC12}
```

In the wedge use the uniformly rescaled inverse. Outside it, divide the
stated sublevel bound by w cubed; the exponent `beta/lambda-3` is negative,
so `w>=kappa*a^lambda` gives the same majorant. All subtracted terms obey
it as well. Pointwise Taylor expansion and dominated convergence finish
the proof. At equality this sufficient argument stops; on the failing side
it proves neither a divergence nor a nonzero signed coefficient.

For the sphere-circle lens the data are
`(nu,beta,sigma)=(1,1,1/2)`: the majorant exponent is **minus one-quarter**.
A transition sector has volume-primitive power two, as separately derived
in F19, safely above the critical power three-halves. The full matched
regular wedge is still necessary: one cannot extrapolate that isolated
sector calculation over its nonintegrable opening edge.

For the quartic lens in #164, the primary regular wedge has
`(nu,beta,sigma)=(3/2,2,1/2)`: its majorant exponent is **minus seven-quarters**.
Here a is the stiffness variable k, not the sphere deficit. CR13–CR14 derive
the failed absolute cubic domination from the actual interval; at fixed
opening parameter the small-energy expansion has a shrinking wedge, so no
uniform two-well version of the sufficient hypotheses is being silently
claimed. The failure already occurs on a fixed primary subwedge. Failure
alone is not the counterexample: CO5–CO16 match both wells and the opening
layer and derive the **retained physical** contribution. Its exponent and
the canonical kernel multiplier are

```math
\begin{aligned}
\frac{\nu+\beta+1}{2\lambda}&=
 \begin{cases}2&\text{sphere-circle},\\9/7&\text{quartic},\end{cases}\\
\widehat K_4(z)&=\Gamma(z)\prod_{j=1}^3(1-2z/j),&
\prod_{j=1}^3\left(1-\frac{2(9/7)}j\right)&=\frac{22}{343}>0,\\
\mathcal A_{\rho,4}^{\mathrm{quartic}}
 &=-D\rho^{3/14}+O(\rho^{1/6}),&D&>0.
\end{aligned}\tag{RC13}
```

The first line describes these derived transition scalings, not a universal
formula for a residue. For the quartic case only the complete matched proof
and its positive model certificate establish a nonzero physical coefficient.
Conformal rescaling in RC1 leaves the sphere's null contact relation intact;
it cannot turn its circle of minimizing meridians into the isolated quartic
minimizer. Thus the new hypotheses exclude the obstruction for a structural
reason whose **critical estimate is exhibited**, not by redefining G-SS or
assuming the desired long limit.

## 7. Signed kernel estimate and complete deterministic restoration

On the original pair space make the disjoint exhaustive split:

1. short: `tau<delta`;
2. off-cut long: `tau>=delta`, `theta<d`;
3. cut: `theta>=d`, `0<=u-theta<e0`;
4. excess: `theta>=d`, `u-theta>=e0`.

Equality boundaries are allocated once and have null pair measure. The
last two sectors are automatically long. Within off-cut and cut, all
above-cap phase pieces remain present. Excess has a strictly positive
actual volume minimum by RC2, continuity and compactness. Every positive-phase
piece has finite pair measure and contributes at most a constant times
`rho^(3/2)*(1+rho^3)*exp(-rho*nu0)` after normalization.

The three signed moments, with this w convention, are

```math
\begin{aligned}
\int_0^\infty z^jK_4(z^2)\,dz
 &=-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2),
 &j&>-1,\\
\int_0^\infty z^jK_4(z^2)\,dz&=0,
 &j&=0,1,2,\\
\rho^{3/2}P_o(\rho)&\longrightarrow0,
 &\rho^{3/2}P_c(\rho)&\longrightarrow0,
 &\rho^{3/2}P_e(\rho)&\longrightarrow0.
\end{aligned}\tag{RC14}
```

For off-cut subtract the actual quadratic density of RC5 before taking
absolute values, and set `z=sqrt(rho)*w`. The bounded remainder quotient
tends to zero and is dominated by a multiple of `z^2*|K_4(z^2)|`.
For cut use RC11 in `P_c=integral K_4(rho*w^2) dN_c(w)` and integrate the
primitive remainder by parts. The rescaled majorant is a multiple of
`z^4*|K_4'(z^2)|`, again integrable. The three polynomial primitive terms
are killed by the same moments after differentiation. Artificial cap
boundary terms, subtracted polynomial tails and the actual above-cap
pieces are positive-phase tails, not dropped terms. No absolute-kernel
bound before subtraction would prove these limits.

The actual complete long primitive therefore also has a cubic Peano jet.
Its bounded remainder quotient discharges CP7's dominated dilation-increment
condition after the constant phase rescaling
`w_here=sqrt(pi/24)*w_CP5`. This does not assert that CP7 requires a jet,
that a jet forces CP8's optional logarithmic-derivative bound, or that the
weaker signed criterion fails on every other geometry.

Use S30 at the **same fixed delta**, as discharged in CP2: compact causal
tubes, a finite normal/face atlas, smooth positive conformal metric and unit
fields supply its actual locality, phase, root and temporal-shell thresholds.
Here no joint chart is needed. Restore any finite source and target
partitions at finite density, including every ordered off-diagonal pair,
before using the sphere symmetry in RC3. Their derivatives sum to zero;
no weighted-cell version of the rotational reduction is assumed. The whole
physical point term is assigned **exactly once** to short:

```math
\begin{aligned}
S_g^\delta(\rho)&=\frac4{\sqrt6}
 [\sqrt\rho\,\mu_g(M)-\rho^{3/2}P_s(\rho)],\\
\mathcal A_{\rho,4}
 &=S_g^\delta-\frac4{\sqrt6}\rho^{3/2}(P_o+P_c+P_e),\\
S_g^\delta(\rho)&\longrightarrow\mathcal T_g,
 &\mathcal A_{\rho,4}&\longrightarrow\mathcal T_g.
\end{aligned}\tag{RC15}
```

The equality is exact at every positive density. The last line follows
from S30 and RC14, not from fitting a finite action value. There is no
extra subtraction in the observable, altered target or shrinking cutoff.
A second compatible fixed cutoff gives the same complete action by the
same exact split; no uniform cutoff limit is claimed.

### Boundary and partner audit

| Physical or artificial part | Retention and estimate |
| --- | --- |
| Both endpoint measures and times | RC3, including the time fraction and its full Jacobian; RC4/RC7 use the actual interior density as well |
| Antipodal family and secondary transition | RC2 physical union; RC8–RC11 include all of it, not a geodesic sum |
| Moving circle/time closing contacts | RC6 straightens b before expansion; xi and both signs of v remain; RC10 differentiates the actual j |
| Regular nearly-null complement | RC4–RC5, not a positive-volume assertion |
| Long circle-axis partners | Full spatial boost and smooth even extension at theta zero; R_delta stays positive |
| `tau=delta`, `tau=4`, `theta=d` | Both radial roots and the signed-direction-specific outer roots in RC5 |
| Fixed cut cap and positive-volume complement | Full capped RC9 primitive, integration-by-parts boundaries and exponential tails |
| Circle seam and sphere poles | Quotient density is periodic; physical circle lifts are injective; two-distance/polar coordinates cover physical points, not extra boundaries |
| Endpoint partitions and cutoff shells | Entire ordered double sum restored; one strict temporal cutoff used throughout; no macroscopic shell declared negligible |
| Point and true spacelike faces | S30 includes the point once and the complete face compensation; unit-field normal flux is zero, not independently deleted |

## 8. Separate original-law expectation transfer

Let O be the same selected measured order as `SphereCircle.measuredOrder 20`,
but let mu now be the **weighted** restricted geometric measure
`omega * (dt dA dz)|M`. Do not reuse the unweighted abbreviation
`SphereCircle.probability 20 4 rho` for this different metric volume.
The law is the unchanged construction `FinitePoisson.law (rho • mu)`.

The point space remains standard Borel, the order is closed and measurable,
and mu is finite and atomless by its bounded smooth density on the compact
slab. Ambient interval containment was proved in section 1. Removing just
the two endpoints leaves the RC2 volume unchanged. Thus all hypotheses of
the existing arbitrary-measure theorem
`MeasuredOrderBDG4.expectation_eq` are met. This is a written specialization
of that checked finite-density theorem, **not a newly compiled weighted
sphere-circle instance**.

For clarity, the unchanged layer observable and its actual count means are

```math
\begin{aligned}
A^{\mathrm{disc}}_{\rho,4}(C)
 &=\frac4{\sqrt6\sqrt\rho}[N-L_0+9L_1-16L_2+8L_3],\\
\mathbb E N&=\rho\mu(M),\\
\mathbb E L_k
 &=\rho^2\int_{x\prec y}
 e^{-\rho V_g(x,y)}\frac{(\rho V_g(x,y))^k}{k!}
 \,d\mu(x)\,d\mu(y),\\
\mathbb E A^{\mathrm{disc}}_{\rho,4}
 &=\mathcal A_{\rho,4}\longrightarrow\mathcal T_g.
\end{aligned}\tag{RC16}
```

Ordered pairs are not divided by two. Null relations and antipodal partners
are not removed from interval counts. The first and second factorial
moments bound the absolute action by a constant times `N+34*N*(N-1)`,
so the observable is genuinely integrable. The polynomial with coefficients
`1,-9,16,-8` and factorial denominators is exactly K4. Only **after** RC15
is proved does the positive-density equality transfer the mean limit.
There is no exchange of a random limit with expectation under a varying
law, and no variance, probability, almost-sure or sample-wise theorem.

## 9. Nontrivial instances, coverage and verification

The following examples obey the metric hypotheses directly; their targets
are calculated from RC1, independently of interval or action coefficients:

```math
\begin{aligned}
\Omega=1&:\qquad \mathcal T_g=320\pi,\\
\Omega=1+t^2/16&:\qquad \mathcal T_g=\frac{1522}{3}\pi,\\
\Omega=1+\tfrac14\cos(\pi z/10)&:\qquad
 \mathcal T_g=320\pi\left[1+\frac{1+3(\pi/10)^2}{32}\right].
\end{aligned}\tag{RC17}
```

The second has genuine time-dependent curvature; the third has spatially
varying curvature and metric volume. Both retain the same focusing null
relations and nonzero Weyl tensor. Arbitrary simultaneous smooth positive
time/circle dependence is covered as well, not merely these two factors.
For constant Omega=c, target and volume scale as `c^2` and `c^4`, while the
pair measure scales as `c^8`; these different powers are useful negative
controls against freezing the phase or omitting an endpoint density.

| Coverage | Established here | Explicit residual ownership |
| --- | --- | --- |
| Corrected positive theorem | All RC1 factors, with actual long cancellation and complete canonical deterministic/expected limit | Other curved metrics and spatial dependence on the sphere require new interval/contact estimates: #151/#81 |
| Focusing | Continuous family of minimizing meridians, both secondary-transition sides, all closing partners | Arbitrary caustic types, folds, cusps, multiplicity and mixed contacts are not classified: #151/#81 |
| Geometry/strata | A non-conformally-flat compact-Cauchy slab with two spacelike faces and empty joint | General nonempty joints, null/mixed strata, other topology/dimensions and general G-SS coverage remain #81/#24 |
| Existing positive controls | Sphere-circle constant factor recovered; controlled conformal variable-joint results preserved, not absorbed into a smaller contract | No contraction of those earlier classes or of the original #151/#81/#24 quantifiers |
| Negative result | #164's complete written quartic obstruction and its separate certificate remain unchanged | It refutes unconditional coverage; failure of a sufficient bound elsewhere is not automatically an obstruction |
| Verification | Written analytic proof plus finite geometric/symbolic diagnostics | Independent mathematical acceptance and any genuine formal port remain #94/#86; an AI audit is supporting evidence only |
| Probability | Actual measured order, weighted volume and unchanged finite Poisson law | No sample-wise theorem, rate or new compiled asymptotic result |

`curved4_corrected_convergence.py` and its tests check the full four-coordinate
diamond measure, actual weighted phase against independent polar/clock
integration, circle-axis partners, quotient seams, both transition sides,
antipodes, moving closing fibres, both endpoint factors, both signed circle
directions, the two time roots, inverse-coefficient algebra, the strict
summability threshold, canonical Mellin zeros, independent targets and the
unchanged layer polynomial. Floating quadrature and finite ranges **do not
prove** RC8/RC11 or a continuum limit. They are not another Arb certificate
and do not fit a full-action asymptotic.

```sh
.venv/bin/python -m unittest -v test_curved4_corrected_convergence
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
node --check site/home-3d.js
node --check site/order-fraction-worker.js
```

No Lean source, checker, dependency, build configuration or toolchain is
changed. No fresh Lean audit is necessary or claimed. The PR records actual
local/CI results, live GitHub equation rendering and its bounded feedback
snapshot separately. No issue is closed, no agent launched, and nothing
merged or deployed by this delivery.
