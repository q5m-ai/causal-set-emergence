# The geometric critical trace: statement, three routes and stopping point

**Conventional written research, not independent acceptance or new Lean
coverage.** Continuation of #156 / draft #184 from
`1e23e79e755d24ac1269e3bb16b617915e810f94`, on the same branch targeting
`issue-81-general-coverage`. The [single original-item crosswalk §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt)
retains the original acceptance. IU8's spherical remainder and CS's common-tip
theorem are inputs for checks, not new examples to prove again.

## 1. Exact obligation before choosing a proof route

### Geometric input and parameter domain

Fix an integer d at least two and an originally admitted smooth Lorentzian
null/mixed member. Its ambient geometry is time-oriented and globally
hyperbolic; the open region M has compact closure and the stipulated whole
ambient-interval containment. Intrinsic and embedded orders are identified
only where that containment has actually been proved. Use the original closed
order, Lorentzian volume, canonical minimal-layer constants and independently
constructed finite Poisson law. All required null fronts, overlaps, tips,
focal/cut contacts and moving closure remain. The lemmas below do not require
smooth descriptions of the two clock endpoints of M.

Choose a smooth Cauchy temporal function t and its orthogonal timelike flow.
Fix one compatible positive physical temporal cutoff delta, independent of
rho. The clock product used below is an auxiliary enclosure, not an extra
physical wall. Constants can depend on this fixed geometry, d and delta;
no uniformity over all metrics or shrinking-cutoff assertion is intended.
The density parameter is `rho>0`; here `epsilon=1/rho` has **volume** scale,
not CS's squared-distance scale. Phase v ranges over the full positive
half-line. Fix a positive reference volume v_star for logarithms.

Let N be the **unit-field complete physical pair** sublevel primitive, with
both endpoint measures, extended constantly beyond its largest physical
volume. The diagonal and null-related pairs have product volume zero, without
changing their closed discrete order. Use IU's m, alpha_j, C_d, filter F_d and
signed exponential weight J. Let Q_pt be IU11's actual point primitive, with
`log(v/v_star)` in even dimensions. Define

```math
\begin{aligned}
\alpha&=2/d,& b&=1+2/d,& m&=\lfloor d/2\rfloor+1,\\
B_M(v)&=\mathcal F_d[N-Q_{\mathrm{pt}}](v),\\
M_b&=\int_0^\infty z^bJ_{m+1}(z)\,dz
       =(b+1)^{m+1}\Gamma(b+1)>0.
\end{aligned}\tag{GT1}
```

### Required geometric output, not an admissibility hypothesis

Construct from geometry a nonlocal filtered germ G_M and a finite geometric
coefficient T_M, in the original normalization. On scopes where they are
already known, T_M must reproduce the independently defined bulk, joint and
any proved finite nonlocal terms. A correction is allowed to have surviving
fractional or logarithmic orders; neither a finite list nor a classical
expansion is presumed to exist universally. A fixed extension of G_M away
from zero must have controlled growth, so the following integrals exist.
The full correction and finite coefficient must be invariant together under
a change of reference volume. Set

```math
\begin{aligned}
L_M&=-\frac{T_M}{\beta_d C_dM_b},\\
E_M(v)&=B_M(v)-G_M(v)-L_Mv^b,\\
\lim_{\epsilon\downarrow0}\epsilon^{-b}
 \int_0^\infty J_{m+1}(z)E_M(\epsilon z)\,dz&=0,\\
\Gamma_M(\rho)&=-\beta_d C_d\rho^b
 \int_0^\infty J_{m+1}(z)G_M(z/\rho)\,dz.
\end{aligned}\tag{GT2}
```

**GT2 is the exact unresolved trace obligation, not a theorem or assumption
on M.** G_M may not be defined as B_M, an unexplained difference from the
action, or an assumed limit. Its coefficients/data and T_M must first be
identified independently from geometry. With that input, GT2 would give
`A_rho,d = Gamma_M(rho)+T_M+o(1)` by IU11. That algebraic consumer does not
supply the geometric input. A catalogue of the existing corrections is not
a general replacement theorem.

The required remainder is the displayed **complete signed integral**. In
particular, no separate source/target-sector trace or weighted-test theorem
is added to unit-observable acceptance. If a proof uses compact z intervals,
it must also account for both ends: vanishing compact integrals together with
vanishing signed tail limsups is sufficient. Absolute uniform integrability
is stronger and optional. Pointwise `E_M(v)=o(v^b)` is also sufficient, not
necessary. No matching tail can be dropped because a formal kernel moment
is zero. If short and long cancel, the cancellation belongs in E_M before
any limit. These distinctions are essential for comparison with CS.

## 2. Audit IU9–IU13 before consuming the filter

Write `D_v=v*partial_v`. Ordinary averaging satisfies `(D_v+1)H=I` in
distributions. Thus `(D_v+1)^(m+1) F_d N=product_j(D_v-alpha_j)N`.
Its adjoint for dv is `-D_v`, while
`-K_d'=product_j(1+(D_z+1)/alpha_j)exp(-z)`. This recovers IU10's sign and
factor C_d, without differentiating the physical primitive. For finite signed
pair measures, cutoff approximation is legitimate: the extra factor v in
every Euler integration removes the lower boundary term, and polynomial
exponential decay removes the upper one. The point subtraction has only
polynomial/logarithmic growth and obeys the same argument.

There is also a direct geometric check of the filter. If c_l are IU10's
coefficients, its one-sided derivative and true endpoint values are

```math
\begin{aligned}
\Phi_d'(r)&=-\sum_{l=0}^m c_l\frac{\log(1/r)^l}{l!}
                           &&(0\lt r\lt1),\\
\Phi_d(0)&=1/C_d,&\Phi_d(1)&=0,&
 |r\Phi_d'(r)|&\le C r(1+|\log r|^m).
\end{aligned}\tag{GT3}
```

The extension by zero above one is continuous; crossing that moving phase
edge contributes no omitted delta to the first derivative. The whole
primitive N, in contrast, is extended **constantly**, not by zero. Its tail
in the Stieltjes identity is `N(V_max)*K_d(rho*V_max)`. Zero extension inserts
an artificial downward jump there. Polynomial subtractions have their own
full tails and cannot be cut off without their corresponding error.

For positive s, the exact power and logarithmic responses are

```math
\begin{aligned}
\kappa_d(s)&=\Gamma(s+1)\prod_{j=1}^m(1-s/\alpha_j)
              =s\widehat K_d(s),\\
\int_0^\infty K_d(\rho v)\,d[v^s\log^k(v/v_*)]
 &=\rho^{-s}\sum_{j=0}^k {k\choose j}\kappa_d^{(j)}(s)
                         [-\log(\rho v_*)]^{k-j}.
\end{aligned}\tag{GT4}
```

These are absolutely justified parameter derivatives, not analytically
continued divergent unsigned integrals. The simple zeros remove pure powers,
not their logarithmic partners. In even dimensions `b=alpha_m`: a primitive
`v^b*log(v/v_star)` supplies a finite term although `v^b` is killed. Higher
logarithmic powers can still give density logarithms and must remain in G_M.
In odd dimensions the pure critical power generally survives.

For the even point term, `kappa_d(1)=0` and
`kappa_d'(1)=Khat_d'(1)`. Changing v_star changes Q_pt by a multiple of v,
which F_d annihilates. In odd dimensions the point uses the nonzero
`Khat_d(1)`. Both give exactly `a_d*mu(M)/(beta_d*rho)`, before any limit.
Hence GT1–GT2 use precisely IU11's original point normalization, not a
renormalized action. Finite ordered endpoint partitions sum to N, and their
diagonal products sum to the physical point weight. IU13's overlap fibres
remain indispensable and are not replaced by single-tip diamonds.

**Audit disposition:** no blocking discrepancy is found in these identities.
They prove neither GT2 nor any pointwise geometric expansion. In particular,
GT4 must not be read backwards to define a geometric coefficient by an action
limit. All later estimates retain the entire signed J integral.

## 3. Route one: derive coarea for the whole physical clock union

This route goes beyond continuity of the old clock inverse. It supplies a
locally absolutely continuous density and an actual leading coefficient, but
not the critical trace. No finite route list or smooth inverse at a focal
point is assumed.

### Uniform clock control without selecting a winning geodesic

In the orthogonal Cauchy splitting write the ambient metric as
`n(t,x)^2 dt^2-h_t(dx,dx)`. For a spatial path c, its future null lift obeys
`dt/du=F(t,c,c')`, where `F=sqrt(h_t(c',c'))/n`. On the compact causal enclosure,
F and its first two t derivatives are bounded by constants times the auxiliary
spatial speed; F is bounded below by a positive multiple of that speed.
All contributing causal paths have bounded auxiliary length, since their
clock duration is bounded and their speed is uniformly bounded.

For a fixed spatial path, solve backwards from terminal time t. Its starting
time b_c(t) has derivatives satisfying common bounds

```math
\begin{aligned}
0\lt c&\le b_c'(t)\le C,& |b_c''(t)|&\le C b_c'(t),\\
b_{q(t,z)}(x)&=\sup_c b_c(t),&
 c h\le b_{q(t+h,z)}(x)-b_{q(t,z)}(x)&\le C h.
\end{aligned}\tag{GT5}
```

The first derivative is the exponential of the integral of `-F_t` along
the lift. Differentiating that ODE once more bounds its logarithmic derivative
by the integral of `abs(F_tt)` times the bounded first variation. This proves
the first line uniformly, rather than estimating a Jacobi inverse.

Here is why the family in the supremum can be fixed. Enlarge the compact
causal enclosure and clock interval slightly. Consider all spatial paths in
its compact projection with the common length bound. Smoothly extend the
positive optical coefficients outside the clock interval to define their
backward ODEs on a common domain. Any path whose departure is above the
physical lower clock stays in the original time interval and uses the actual
metric. A path departing below that clock contributes zero. Every contributing
physical causal path is included; no physical wall is introduced. Null lifts
give the latest departure along a fixed spatial path, so their supremum agrees
with the actual past cone on the retained departure range. Below that range
only the zero positive-width value is used; no inequality subtracts infinite
thresholds. No maximizer or measurable choice is needed. The uniform monotone
Lipschitz inequalities pass to this supremum on finite retained ranges. The analogous
forward infimum proves the same bounds for arrival as a function of source
clock time, on each retained finite-arrival range.

For fixed p and terminal spatial label z put
`W(t)=V(p,q(t,z))`, `a=a_p(z)`, `h=t-a`. On each intermediate physical flow
line x the width is `[b_{q(t,z)}(x)-a_p(x)]_+`. GT5 gives a uniform bound by
C*h: for every fixed path its positive width is zero at t=a, since a positive
width would make p chronologically precede its first arrival. Apply the uniform
path bound before taking the supremum, even if the earlier physical departure
threshold is infinite. All physical intermediate
points are in the compact enclosure. With the genuine volume density j,
Fubini and Lipschitz differentiation therefore give, for almost every t>a,

```math
\begin{aligned}
\Sigma_{p,z}(t):=W'(t)
 &=\int_{b_{q(t,z)}(x)>a_p(x)}
 j(b_{q(t,z)}(x),x)\,\partial_t b_{q(t,z)}(x)\,d\sigma(x),\\
W'(t)&\ge c\,W(t)/h>0.
\end{aligned}\tag{GT6}
```

For a fixed intermediate x the equality `b=a_p(x)` is crossed at most once,
by GT5. Fubini justifies the displayed derivative for almost every t even
if an entire set of x opens at one exceptional time. Such changes are not
removed from W or from its primitive.

There is a useful additional one-sided bound. For each spatial path,
`b_c''+C*b_c'>=0`. The function
`[integral_{a_p(x)}^{b_c(t)} j(r,x)dr]_+` satisfies the analogous inequality
with a common larger C, by bounded `partial_t log(j)` and GT5. In the variable
`u=exp(-C*t)` this means convexity. Taking the supremum over paths, and then
integrating over physical x, preserves convexity. Consequently
`W''+C*W'>=0` in distributions: `exp(C*t)*W'(t)` has a nondecreasing
representative. Its distributional derivative is a positive Radon measure.
This is a count-free bounded-variation statement, not a claim that W is
smooth through a change of routes.

### The actual coarea density, including moving closure

For long pairs at sufficiently small volume the contained final short-null
segment argument of CP6 gives `W(t)>=c*h^(d/2)` in every d. Its local squared
separation is bounded below by c*h and the actual local volume ratio is
positive; only this short segment, not the long ray, needs a normal chart.
If the first arrival had gap less than delta/2, the long condition would
force a fixed positive-volume diamond instead. Thus the constants are uniform
on all retained small-volume long fibres, including cut/focal ones.

Combine this lower bound with GT6. The whole inverse T is locally Lipschitz
away from volume zero. On its active, unsaturated part its derivative obeys

```math
\begin{aligned}
0\le T_{p,z}'(v)&=1/\Sigma_{p,z}(T_{p,z}(v))
                 \le C v^{\alpha-1},\\
n_M^\delta(v):=\frac{dN_M^{\delta,V}}{dv}
 &=\int_M\int_Y
  \frac{j(T_{p,z}(v),z)}{\Sigma_{p,z}(T_{p,z}(v))}
  \mathbf1_{\ell_{p,z}\lt T_{p,z}(v)\lt m_+(z)}\,d\sigma(z)\,d\mu(p),\\
0\le n_M^\delta(v)&\le C v^{\alpha-1}.
\end{aligned}\tag{GT7}
```

In the display the comparisons in the indicator mean strict physical
inequalities; equality endpoints are treated by the continuous clipped
primitive. Here `ell=max(a_p(z),m_minus(z),t(p)+delta)` as in IU2. The derivative
bound applies on the retained small-volume long fibres, not on a diagonal
family with delta tending to zero. Equivalently their inverse is uniformly
Lipschitz in `v^alpha`. This does not rehabilitate NA1's folded coordinate.

To justify coarea, GT6 gives a positive derivative lower bound on each compact
positive-volume interval. W is Lipschitz, so its exceptional differentiability
set has a volume-null image. The inverse is locally absolutely continuous;
the integrable bound in GT7 extends this to zero on active long strips.
Clipping an absolutely continuous increasing inverse at the actual lower and
upper clocks preserves absolute continuity. Its density is exactly the
indicator in GT7, with no endpoint delta: the primitive opens continuously
from zero and closes continuously to a constant. Outside that indicator the
integrand is defined as zero without evaluating an inverse or a quotient on
an empty fibre; after saturation the clipped inverse has derivative zero.
Tonelli then proves the whole density. Both source and target measures and every overlap remain.
Bounded signed endpoint fields can be inserted without differentiating them;
they are not required as additional trace tests in GT2.

### What regular arrivals actually supply

For each p, almost every finite arrival spatial label is reached by a unique
nonconjugate null generator. The arrival graph is locally Lipschitz;
differentiability fixes the terminal null direction by its smooth supporting
short cones, hence the generator by backwards ODE uniqueness. The conjugate
endpoint images have spatial measure zero by Sard on the countable smooth
initial-direction/affine-parameter charts. These are almost-everywhere facts,
not permission to discard normalized focal neighborhoods.

At such an arrival use null Fermi coordinates along the generator, affine
parameter s in `(0,L)` and a parallel `(d-2)`-screen. Let eta be the clock
pairing with its terminal tangent and D(s) the sum of the two cone Hessians,
the positive screen index form. Its actual independent coefficient is

```math
\begin{aligned}
A_d(p,z)&=\frac{2^{d/2}\omega_{d-2}}{d}\eta^{d/2}
            \int_0^L\frac{ds}{\sqrt{\det D(s)}},\\
W(a+h)&=A_d(p,z)h^{d/2}+o(h^{d/2}),\\
W'(a+h)&\sim\tfrac d2 A_d(p,z)h^{d/2-1},\\
v^{1-\alpha}T_{p,z}'(v)&\longrightarrow\alpha A_d(p,z)^{-\alpha}.
\end{aligned}\tag{GT8}
```

Here omega_n is the Euclidean unit n-ball volume; in d=2 the empty determinant
and omega_0 are one. The screen integral of
`(eta*h-Z^T*D*Z/2)_+` gives the displayed factor. This extends CR1's actual
calculation, not its spacelike boundary argument. Near either tip,
`det(D)^(-1/2)=O(s^((d-2)/2))`; the omitted length-epsilon tip contributes at
most `C*h^(d/2)*epsilon^(d/2)+C*h^d`. On the interior the faithful cone Taylor
bounds and rescaling give dominated convergence. Compact causal-curve control
confines the interval to an arbitrarily small generator tube as h tends to
zero. Take h to zero first, then the tip length to zero, proving the second
line. No uniform higher expansion near the exceptional set is claimed.

The derivative asymptotic is **not** obtained by differentiating an o term.
Use the monotone representative `exp(C*t)*W'(t)` from GT6. Its forward and
backward secant bounds between h and `(1+eta_0)*h` sandwich its divided value.
The second line gives the power-law secant limits; then send eta_0 to zero.
This proves the last two lines, including the d=2 exponent one case, at almost
every phase value (or with the monotone representative).

Null faces require a different equality-mask argument from CR3. For fixed
source spatial label x and target label z, arrival `a_{q(s,x)}(z)` is strictly
increasing in s, with GT5's bounds. Therefore equality to either fixed Borel
clock boundary `m_minus(z)` or `m_plus(z)` has at most one source time. Fubini
makes those equality masks product-volume-null, even for singular null faces;
no spacelike transversality of a face is assumed. Equality at the temporal
cutoff is spatially null at a regular arrival, because a null graph meets a
Cauchy time level transversely; irregular arrivals were already null.

GT7 now dominates the **normalized coarea density**. Use its one-sided
derivative representative, or equivalently interpret the density limit as
an essential limit. Let `L_M^delta(rho)` denote the original long pair action,
`-beta_d*rho^b*integral K_d(rho*v)*n_M^delta(v)dv`. With R_delta denoting
regular arrivals strictly inside both endpoint and temporal masks, it gives

```math
\begin{aligned}
b_1&=\int_{R_\delta}j(a_p(z),z)A_d(p,z)^{-\alpha}
                         \,d\mu(p)\,d\sigma(z),\\
g_M(v):=v^{1-\alpha}n_M^\delta(v)&\longrightarrow\alpha b_1,\\
N_M^{\delta,V}(v)&=b_1v^\alpha+o(v^\alpha),&
L_M^\delta(\rho)&=o(\rho).
\end{aligned}\tag{GT9}
```

The last conclusion follows from the genuine first kernel zero and the full
tail identity. It is only a **subcritical long bound**. The short term and
point remain exactly in GT2; neither a complete finite limit nor a general
expected limit follows. This result removes a differentiability obstacle to
coarea and computes its first coefficient for these null/mixed masks. It does
not provide the extra volume order required at critical normalization.

## 4. Route two: direct signed control and a critical stability reduction

The geometric density above gives an exact signed scale-increment formula.
Extend g_M by its actual zero density beyond the physical phase support,
while N itself remains constantly extended. Since the alpha moment of Phi
is zero,

```math
\begin{aligned}
\mathcal F_dN_M^{\delta,V}(v)
 &=v^\alpha\int_0^1\Phi_d(r)r^{\alpha-1}
                   [g_M(vr)-g_M(v)]\,dr,\\
\frac{\mathcal F_dN_M^{\delta,V}(v)}{v^b}
 &=\frac1v\int_0^1\Phi_d(r)r^{\alpha-1}
                   [g_M(vr)-g_M(v)]\,dr.
\end{aligned}\tag{GT10}
```

This is a direct signed expression in the actual reciprocal projected-area
integral GT7. It keeps the entire interval of ratios, not just r close to one.
GT9 makes its numerator o(1), but critical order needs control after division
by v, and the appropriate independently computed surviving terms. No bound
on the positive primitive alone supplies this. Even this long expression
need not have a separate limit: the obligation is still the complete GT2.

### A geometry-derived reduction that is valid at critical order

Let `k=floor(d/2)`. On a fixed small clock-excess collar of long pairs, replace
only the **interior** volume density on each physical intermediate flow line
by its order-k Taylor polynomial at its actual arrival a_p(x). Keep the whole
width w, both physical endpoint measures, the source/target masks and every
route union. Define the auxiliary phase

```math
\begin{aligned}
w_{p,q}(x)&=[b_q(x)-a_p(x)]_+,\\
V_{[k]}(p,q)&=\int_Y\sum_{i=0}^k
 \frac{\partial_t^i j(a_p(x),x)}{(i+1)!}w_{p,q}(x)^{i+1}\,d\sigma(x),\\
|V_{[k]}-V|&\le C h^{k+1}V\le C V^{1+\eta},&
\eta&=\frac{2(k+1)}d>1.
\end{aligned}\tag{GT11}
```

Empty fibres contribute zero, without evaluating a derivative at an infinite
threshold. This is Taylor's theorem for a known smooth volume form,
**not** a desired expansion of the causal front or of N. GT5 bounds every
physical width by C*h. Positivity of the original density bounds the integrated
Taylor error by `C*h^(k+1)*V`; CP6's long collar bound gives the second inequality.
Choose the fixed collar small enough that the polynomial density is positive
and the two phases comparable. Outside it use the exact V. This auxiliary
replacement has no effect on the physical region, order, point or fixed
short/long cutoff; all complements are retained. No lower regularity beyond
the original smooth ambient metric is silently claimed.

Let N_[k] be the pair primitive of that auxiliary phase on the long part,
with the short part unchanged. GT3, including passage through r=1, gives

```math
\begin{aligned}
|\mathcal F_d(N_{[k]}-N)(v)|&\le C v^{\alpha+\eta}
                                             &&(0\lt v\lt v_0),\\
\rho^b\left|\int_0^\infty J_{m+1}(z)
 \mathcal F_d(N_{[k]}-N)(z/\rho)\,dz\right|
 &\le C\rho^{1-\eta}+o(1)\longrightarrow0.
\end{aligned}\tag{GT12}
```

For clarity, when either filter value is nonzero the actual volume is at
most 2*v. The mean-value bound is a constant times
`V^eta*(V/v)*(1+abs(log(V/v))^m)`. Its ratio factor is bounded, and the positive
long sublevel measure is at most `C*v^alpha`. This proves the first line
without a branchwise inverse. For the second, integrate the true signed
weight using its absolute **difference** bound; its polynomial-exponential
moments are finite. The portion with `z>v_0*rho` has a bounded pair primitive
and exponential decay. It is retained, not replaced by zero. The point and
short terms cancel identically between the two complete observables before
this estimate. No absolute bound on their uncancelled individual actions was
used. Thus GT12 is genuine complete critical stability, not just a leading
coefficient or a formal identity.

This reduction does not solve GT2: all difficult geometry is still in the
actual widths w. Its benefit is precise: smooth interior-density jets are
not the remaining obstruction, and freezing to a single endpoint density
would be wrong. The jets are evaluated over the **entire** null interval,
including macroscopic intermediate partners.

### Why the new coarea and one-sided bounds still do not imply the trace

The following is an abstract control, not a claimed Lorentzian realization
or an additional selected example. For `v<exp(-8)`, put
`U(v)=v^alpha*(1+1/log(1/v))` in d>2. It is increasing and concave, comparable
to v^alpha, with first coefficient one. Its inverse is convex and satisfies
all the scalar clock/coarea bounds above. In d=2 use the minus sign instead,
which has the same properties with alpha=1. Constant continuation outside
the fixed small interval is understood for the primitive.

Nevertheless the full filter has a nonzero slowly varying remainder. Writing
`L=log(1/v)` and using IU9's f_d,

```math
\begin{aligned}
\mathcal F_dU(v)
 &=\pm v^\alpha\int_0^\infty e^{-Lx}f_d(\alpha+x)\,dx,\\
\mathcal F_dU(v)&\sim
       \pm f_d'(\alpha)\frac{v^\alpha}{\log(1/v)^2},
 &f_d'(\alpha)&\ne0.
\end{aligned}\tag{GT13}
```

The plus sign is for d>2. To derive the integral, write
`1/(L+y)=integral_0^infty exp(-(L+y)*x) dx` in each repeated ordinary average.
The finite combination is exactly f_d(alpha+x); the pure alpha mode vanishes.
Substitution x=u/L and dominated convergence gives the second line. It is
not a guessed logarithmic expansion. Its normalized signed response has order
`rho/log(rho)^2`, with nonzero coefficient given by GT4's simple-zero derivative.
For this last passage split the actual z integral at one and at sqrt(rho).
On the first two pieces the logarithm ratio is bounded by one and two,
respectively; beyond sqrt(rho), exponential decay and the bounded continued
primitive dominate. This justifies the full signed moment, rather than an
unlicensed interchange with an unbounded integral of Mellin powers.
Thus concavity, bounded variation, the uniform inverse bound and the actual
first coefficient **do not by themselves imply critical control**. This
control cannot disprove the spacetime theorem; it identifies which additional
geometric information a successful proof must use. GT12 does not create that
information by smoothing the volume density.

## 5. Route three: try an independently geometric nonlocal correction

GT6 supplies a count-free geometric contact measure
`d[exp(C*t)*W'(t)]`. It records all intermediate-flow openings and all changes
of maximizing departure paths, with positive variation and bounded mass on
compact clock intervals. One candidate is to retain its singular/atomic part
as a nonlocal correction while applying a regular expansion to the rest.
This candidate fails the existing adversarial check: IF1's seven-halves
transition has a continuous second derivative, and IU12's nonzero growing
coefficient comes from a **joint** focal-parameter limit, not a delta in the
clock curvature measure. A singular-part-only correction would miss it.
The full absolutely continuous contact density cannot be discarded.

A second version retains the entire contact measure and reconstructs W by
two clock integrations, or retains all widths in GT11. That retains every
physical route, but evaluating the original kernel on this exact reconstructed
volume merely repackages the action. Calling its unexplained difference from
the local target a correction would be circular. GT12 permits a controlled
auxiliary replacement; it does not turn such a repackaging into independent
geometric coefficients.

A third version would extract all fractional/logarithmic coefficients from
a geometric Mellin continuation of those contact data. It works in IU's
proved spherical scope, but smoothness plus the new one-sided clock control
does not provide such a continuation generally. GT13 already demonstrates
that these scalar conclusions allow non-meromorphic slow variation. It is
not an admissible counterexample, nor a reason to impose a desired expansion.
A general proof could instead control GT10 and GT2 directly, without any
meromorphic expansion. Conversely, when geometric modes really are derived,
GT4 preserves all their logarithmic partners and matching terms; none can be
removed solely by labeling its pure power a kernel zero.

These are substantive failures of proposed **constructions**, not a proof
that a nonlocal corrected theorem is impossible. No exhaustive classification
of individual spacetimes is added as a new closure gate.

## 6. Adversarial checks and complete accounting

For the spherical product use the already derived C_T of IU7. Its raw
geometric mode is `C_T*v`; its filtered germ is `f_7(1)*C_T*v`, and its full
response is `5*beta_7*C_T*rho^(2/7)/128`, exactly IU12. IU8 supplies its
independent finite curvature/screen term and remainder. The clock density
is time independent, so GT11's phase equals the actual phase there: GT12
cannot falsely remove the focal term. Both opening and meridian matching
sides are those in IU7, not reconstructed from a retained positive sector.
This uses the completed theorem; it does not redo the family calculation.

For the curved conformal common-tip class, retain CS's already derived whole
partner fibre, curvature, signed profile mass and both tails. IU11 then gives
the GT2 **weak complete trace** with G_M zero and T_M equal to that independent
CS target. This does not infer a pointwise primitive jet or separate long and
short traces. GT11 retains density jets all along the physical null interval,
not just at its endpoint, and GT12 leaves the complete CS response unchanged.
It does not transfer CS's special map or fibre property to general intrinsic
or non-common-tip geometry. The two adversaries consequently require distinct
responses and are consistent with, not proofs of, the general reductions.

Every source/target partition is restored before using the unit-observable
GT2: their products sum to one, their diagonal products restore Q_pt, and
both cross orders and both-singular sectors remain. The single physical
short/long cutoff and every complement remain fixed. IU13 still requires
actual overlaps; no tip-action sum is introduced. The new coarea density is
of the already united physical volume, and the critical stability estimate
changes only an auxiliary phase after exact point matching.

No general deterministic GT2 has been proved. Therefore no new general
expected limit is asserted. The original finite-density Mecke identity is
available with its actual Borel order, exclusive intervals, atomless volume,
both intensities and finite factorial moments, but it cannot supply the
missing deterministic inference. Existing separate expectation conclusions
for IU8, CS and earlier complete scopes remain intact. No sample-wise claim
is made.

## 7. Decisive inference and original-contract disposition

**STILL BLOCKED.** The new geometric deductions are: count-free clock
one-sided control, an actual coarea density through route and cap changes,
its independently computed first coefficient with null-mask handling, and a
complete critical-order interior-density-jet stability theorem. None is a
new selected spacetime example. None supplies the missing complete trace.

The smallest remaining implication is now explicit: from the actual clipped
reciprocal projected-area integral in GT7, control the signed scale increment
in GT10 **at the extra volume order**, with independently computed surviving
nonlocal terms and the full integrated remainder GT2 after short/point
restoration. Ordinary first-order convergence, one-sided variation and smooth
interior density do not supply it. The overlap/focal/closure coupling of those
geometric data is the information still missing, not another filter identity,
a normalization constant, an expectation interchange or a Lean port.

A specialist result on that geometric signed scale increment is required to
advance this route. A parent scope decision would be required only to accept
a narrower endpoint instead of the original general theorem; none is adopted.
The canonical observable and original #156/#81/#24 acceptance are unchanged.
No claim is transferred to #177. Independent scrutiny/provenance/verification
remain #94/#86; #185's claim-to-Lean mapping remains deferred. The single
crosswalk, not this proof's list of deductions, determines original coverage.

`geometric_trace_diagnostics.py` and its 14 tests check finite clock/coarea
identities, density jets, filter derivatives, logarithmic moments, full tails,
normalization and the explicitly abstract slow control. Sampled errors do not
certify the geometric bounds, the critical remainder or independent acceptance.
No production definition, Lean source/checker, dependency or workflow is changed.
