# Actual general-metric signed short producers (#150)

**Written analytic proof, not a Lean theorem or independent human review.**
This continues [the geometric derivation](general-metric-short.md), using its
unchanged G-SS core, action, curvature convention, induced target and fixed
**temporal-gap** cutoff. It supplies GM-S1, then GM-S2, then GM-S3. The central
new input is an actual interval rescaling at the null edge, not an assumption
that the interval volume has a smooth positive factor. The final theorem is
for the **short action only**. No general long estimate, full-action limit or
expectation limit is inferred; #151/#81 retain those obligations.

Fix physical dimension d at least two, put N=floor(d/2), and use precisely
c_d, a_d, beta_d and K_d from [dimension-kernels](dimension-kernels.md).
Ordinary sphere measure includes the two directions in 2D. Geometry and all
smooth endpoint fields are fixed. Constants below can depend on their compact
neighborhoods, d and the chosen positive cutoff, never on density. Smoothness
is used to obtain finitely many derivatives for each fixed d; no new universal
C3 or minimal finite-regularity claim is made.

## 1. Actual thin-interval containment in source normal coordinates

Use the finite normal atlas and **whole-interval** locality lemma (G2) of the
companion note, also for its auxiliary sources. In an orthonormal normal frame
at a source x write the coordinate metric as g_x(X). Smooth dependence of the
exponential map gives smooth coefficients in x and X on the compact atlas;
Gauss's lemma and the normal-coordinate jet give

```math
\begin{aligned}
g_x(X)(X,W)&=\eta(X,W),&
g_x(vX)&=\eta+v^2G_x(v,X).
\end{aligned}\tag{S1}
```

More precisely, on a fixed coordinate box, g_x(vX)-eta and all its X derivatives
of any fixed order are bounded by C_k v squared; the same holds with any fixed
finite set of passive base/frame derivatives. This follows by Taylor with
integral remainder at X=0, where the metric's first derivatives vanish. We use
this explicit rescaled statement, not a claim that ordinary second derivatives
are of order |X| squared.

Choose a spatial direction omega, null vectors
L=(1,omega)/2, Q=(1,-omega)/2, and an orthonormal transverse frame E. Then
eta(L,Q)=1/2. Use finitely many angular frame charts if necessary; estimates are
uniform on their compact supports. Let

```math
\begin{aligned}
\xi&=vL+uQ,\qquad 0\lt u\le v,\qquad R=u/v,\\
y&=\exp_x\xi,\qquad
 X=v(AL+BQ+CE),\qquad z=\exp_xX.
\end{aligned}\tag{S2}
```

Choose v small enough that every ambient interval considered is in the normal
chart by (G2). Normal coordinate time is temporal there. If z belongs to the
actual interval, the source cone is exactly the tangent cone, so
A,B are nonnegative, |C| squared is at most AB, and temporal monotonicity gives
A+B at most 1+R. In particular A,B,C lie in a fixed compact box.

We need the stronger B=O(R), C=O(sqrt(R)) bound; an ordinary coordinate Taylor
error would not supply it. Let E_v be the difference between signed squared
geodesic separation for the rescaled metric g_x(vX) and its flat value, with
endpoints L+RQ and AL+BQ+CE. Smooth dependence of the short geodesic boundary
problem, together with (S1), gives E_v=v squared times a smooth bounded function
with bounded derivatives on this box. At R=B=C=0 the endpoints lie on the
same radial null geodesic. The difference and **all first endpoint variations**
vanish there: the first variation of squared separation is the metric pairing
with that radial tangent, and Gauss's lemma makes that pairing exactly flat
at both endpoints. This remains true at coincident endpoints and at A=0.
Taylor in (R,B,C), with A a passive compact parameter, consequently gives

```math
\begin{aligned}
|E_v(A,R,B,C)|&\le C_0v^2(R^2+B^2+|C|^2),\\
s_{g_x(v\cdot)}(L+RQ,AL+BQ+CE)
 &=(1-A)(R-B)-|C|^2+E_v.
\end{aligned}\tag{S3}
```

The smooth geodesic boundary problem here follows from the inverse function
theorem for the exponential map uniformly near the flat metric on a fixed
box; its needed derivatives follow by differentiating the geodesic ODE.
It is used only where normal-chart locality has already excluded other ambient
branches. Thus (S3) is about the actual interval, not a selected branch in a
possibly nonlocal interval.

If B is greater than 2R, temporal monotonicity implies 1-A at least B-R, and
the flat term is at most -B squared/4-|C| squared. For one uniform small v,
(S3) is strictly negative, contradicting causal separation from z to y.
Therefore every actual interval point satisfies

```math
\begin{aligned}
0\le A\le2,\qquad 0\le B\le2R,\qquad |C|\le2\sqrt R.
\end{aligned}\tag{S4}
```

This proves the necessary thin-tube containment, uniformly down to the null
edge. The argument does not infer it from small volume. When d=2 the transverse
space is zero-dimensional and the same B estimate applies.

## 2. Derive the smooth ratio phase from the real interval

Set e=sqrt(R) and pull back the actual metric by the linear normal-coordinate
map

```math
\begin{aligned}
X&=v(sL+e^2rQ+eZE),\\
\widehat g_{v,e}&=(ve)^{-2}X^*g_x,\qquad e\ne0.
\end{aligned}\tag{S5}
```

Both tips become the **fixed timelike** points (0,0,0) and (1,1,0), whose flat
squared separation is one. Here r is a null coordinate, not spatial radius.
The only potentially singular metric components are

```math
\begin{aligned}
\widehat g_{ss}&=g_x(X)(L,L)/e^2,&
\widehat g_{sA}&=g_x(X)(L,E_A)/e,\\
\widehat g_{sr}&=g_x(X)(L,Q),&
\widehat g_{AB}&=g_x(X)(E_A,E_B),\\
\widehat g_{rr}&=e^2g_x(X)(Q,Q),&
\widehat g_{rA}&=e\,g_x(X)(Q,E_A).
\end{aligned}\tag{S6}
```

Gauss's lemma along vsL says g(L,L)=g(L,E_A)=0 and g(L,Q)=1/2. Differentiate
its identity g_x(X)(X,L)=eta(X,L) in **any** coordinate direction at vsL. It also
says the first derivatives of g(L,L) vanish there; at s=0 this follows from
the normal-coordinate first jet. Hence the numerator of the first component
in (S6) vanishes to second order in e, and that of the second to first order.
Taylor's integral formula in e divides them smoothly by e squared and e.
There is no inverse power left. Using (S1) in the same formulas proves

```math
\begin{aligned}
\widehat g_{v,e}&=\eta_{\mathrm{null}}+v^2G(x,\omega,v,e;s,r,Z),\\
\eta_{\mathrm{null}}&=ds\,dr-|dZ|^2,
\end{aligned}\tag{S7}
```

with G smooth and all required derivatives uniformly bounded on a fixed
slightly enlarged box, for small |v| and |e| at most a little more than one.
The divisions and the v-squared factor commute by the same integral formulas.
This supplies a uniformly Lorentzian metric at e=0 too; no positive Taylor
inverse of the original volume has been presumed.

By (S4), the **entire actual interval** for positive v,e lies in that fixed
box. Conversely, the pulled-back causal relations inside it are exactly the
original ones. Choose a larger box and extend the metric by cutting off its
v-squared perturbation to zero outside a still larger box. This gives a smooth
uniformly near-Minkowski family on the whole rescaled space. Its time coordinate
(s+r)/2 is globally temporal with a uniform causal spatial-speed bound. Between
the tips time lies between 0 and 1; that speed prevents exit from the chosen
large box. Thus its interval agrees with the pulled-back actual interval.
Its volume is independent of these **controlled** extensions; arbitrary
noncausal extensions outside the box are not asserted harmless.

We record why its volume depends smoothly on these parameters. For a metric
sufficiently close to eta on this box, the two cones intersect each constant
(s+r)/2 slice in star-shaped balls about the spatial origin. Their radii in
a direction n are smooth: solve the null geodesic ODE from each tip, use its
strictly monotone time parameter, and invert its angular projection near the
identity. The radius divided by time-from-tip is smooth also at the tip.
The future and past radii meet at a unique smooth switching time near 1/2;
their time derivatives at the flat metric are +1 and -1, so the implicit
function theorem gives a uniform transverse margin. Integrate the smooth
volume density radially on each side of this moving switch. Rescaling the
radial and time intervals to [0,1] proves smooth parameter dependence by
compact differentiation under the integral. In d=2 this is the same argument
on the two spatial directions. This proof retains both cone tips and their
moving intersection, rather than differentiating an unrectified indicator.

Reflection Z to -Z carries the metric at e to the metric at -e, fixes both
tips, and preserves volume. The resulting volume is a smooth **even** function
of e. A smooth even function of e is smooth as a function of R=e squared on
the closed positive half-line: Taylor to arbitrary even order with integral
remainder proves the finite-order statement, including passive-parameter
bounds. Applying this to the actual interval just constructed proves

```math
\begin{aligned}
V(x,\exp_x(vL+uQ))&=c_d(uv)^{d/2}H(x,\omega,v,R),\\
H(x,\omega,0,R)&=1,\qquad H_v(x,\omega,0,R)=0,\\
H&=1+v^2h_2(x,\omega,R)+v^3E_H(x,\omega,v,R),\\
h_2&=-A_d\mathrm{Ric}_x(\Delta,\Delta)-B_dR_g(x)R,
\qquad \Delta=L+RQ.
\end{aligned}\tag{S8}
```

Here A_d and B_d are the explicitly derived coefficients in (G3).
H and E_H are smooth up to R=0 and R=1 with uniform derivatives of every fixed
finite order. H is positive and bounded away from zero after fixing a small
v cutoff. The determinant in (S5) gives the factor (ve) to power d, explaining
the power (uv) to power d/2 with the **same** c_d. To identify h_2, apply (G3)
at each fixed positive R and change midpoint curvature to source curvature.
Its resulting polynomial is the last line of (S8); smoothness just proved
extends the equality to R=0. This uses the bounded-rapidity calculation to
identify a coefficient **after** proving the null-edge bounds, not in place
of them. Derivatives of E_H follow from integral Taylor in v on the compact
parameter family. No conformal identity has been used.

## 3. A signed comparison estimate retaining every moving diagonal

Here is the analytic calculation needed for all three geometric producers.
Its hypotheses will be derived from their actual flattened integrals below.
Let k=0,1,2 count the number of source collar variables, and let p=3-k.
After the actual phase change, consider

```math
\begin{aligned}
a_\lambda(w,v)&=v^{d-3+k}\Psi(\lambda v,w/v^2),\\
B_\lambda(w)&=\int_{\nu_\lambda(w)}^{\epsilon}a_\lambda(w,v)\,dv,\\
\nu_\lambda(w)&=\sqrt w\,b(\lambda\sqrt w),\quad
 b(0)=1,\quad b'(0)=0,\qquad 0\le\lambda\le1.
\end{aligned}\tag{S9}
```

There may be additional passive compact parameters and fixed bounded outer
weights. Psi and b are smooth on the required compact domains. The factor
(1-U) to power d-2 from the true polar Jacobian is retained in Psi, but the
following bounds do **not** assume that all its differentiated boundary
values vanish. Choose a common phase collar where every moving lower endpoint
nu_lambda in (S9) is below epsilon/2. Use a smooth phase cutoff equal to one on a smaller
collar and supported in this collar. Terms outside it have a fixed positive
actual volume and are exponentially small after normalization. Differentiating
the original finite-density interpolation there creates only finitely many
polynomial factors in rho, still exponentially small. This device avoids any
claim that a low-dimensional zero extension through the upper cutoff corner
is three times differentiable.

For all mixed derivatives used below the chain rule gives

```math
\begin{aligned}
|\partial_\lambda^a\partial_v^b\partial_w^j a_\lambda|
 &\le C v^{d-3+k+a-b-2j},\\
|\partial_\lambda^a\partial_w^j\nu_\lambda|
 &\le C w^{(a+1)/2-j}.
\end{aligned}\tag{S10}
```

In the first bound v differentiation is at fixed w. Differentiating the
moving integral p times in lambda gives its integral of the p-th derivative
minus the following complete contact expression, evaluated at v=nu. In
(S11), subscripts on a denote **partial derivatives**, the unsubscripted a
means the current amplitude, and dots denote lambda derivatives of nu:

```math
\begin{aligned}
C_1&=a\dot\nu,\\
C_2&=2a_\lambda\dot\nu+a_v\dot\nu^2+a\ddot\nu,\\
C_3&=3a_{\lambda\lambda}\dot\nu+3a_{\lambda v}\dot\nu^2
 +a_{vv}\dot\nu^3\\
 &\quad+3a_\lambda\ddot\nu+3a_v\dot\nu\ddot\nu+a\dddot\nu.
\end{aligned}\tag{S11}
```

For p=3-k every interior derivative is v to power d times a smooth function
of lambda v and w/v squared. Every displayed contact term, and every further
boundary term from j derivatives in w, is bounded by
C w to power ((d+1)/2-j). Indeed each lambda derivative of the lower endpoint
costs the factor in (S10); a w derivative costs two powers of nu. Thus, for
Q_lambda=partial-lambda-to-power-p B_lambda, derivatives through N have finite
right limits obtained by integrating the zero-phase interior probes. Their
integrands are bounded by v to power d-2j, integrable for j at most N;
all boundary terms tend to zero. Split the v integral at a fixed positive
number to obtain uniform convergence, and then use the fundamental theorem
of calculus for the right derivatives.

For the next derivative the interior integral is bounded by the integral of
v to power d-2N-2 from nu to epsilon. Including **all** the boundary terms gives

```math
\begin{aligned}
|Q_\lambda^{(N+1)}(w)|&\le
\begin{cases}
 Cw^{-1/2},&d=2N,\\
 C(1+|\log w|),&d=2N+1.
\end{cases}
\end{aligned}\tag{S12}
```

Integral Taylor in w therefore bounds the remainder after the degree-N
polynomial by C w to power N+1/2 in even d and C w to power N+1 times
(1+|log w|) in odd d. Now take integral Taylor in lambda through order p-1.
For the **actual-minus-entire-interpolation-jet** density D this proves

```math
\begin{aligned}
D(w)&=B_1(w)-\sum_{a=0}^{p-1}\frac1{a!}
       \left.\partial_\lambda^aB_\lambda(w)\right|_{\lambda=0}\\
    &=\sum_{j=0}^N d_jw^j+\mathcal R(w),\\
|\mathcal R(w)|&\le
\begin{cases}
 Cw^{N+1/2},&d=2N,\\
 Cw^{N+1}(1+|\log w|),&d=2N+1,
\end{cases}\\
\rho^{1+2/d}\int_0^\infty K_d(c_d\rho w^{d/2})D(w)\,dw
 &\longrightarrow0.
\end{aligned}\tag{S13}
```

In the last line the phase cutoff and the exponentially small complement are
understood as above. To prove it, subtract the polynomial on the whole positive
half-line using the existing zero moments j=0,...,N. Divide the remaining
density by w to power d/2. The quotient tends uniformly to zero and is bounded
on the half-line (use the compact phase cutoff away from zero). Rescaling
w=(c_d rho) to power -2/d times z gives the integrable majorant
z to power d/2 times |K_d(z to power d/2)|. This is signed cancellation followed
by domination of the **pushed difference**, not absolute domination of the
original coordinate Taylor error. Constants and the errors are summable over
any fixed finite parameter atlas and endpoint-field family.

The derivative demand is finite and dimension-dependent: derivatives of Psi
through the mixed orders in (S10) with a+b+j at most N+4, and of b through
N+4, suffice. Below these are obtained by smooth ODE dependence, division with
integral remainder, even-variable substitution, and ordinary implicit-function
differentiation from the smooth metric/fields. In the even-variable step, j
ratio derivatives may require 2j derivatives in e; they are not identified
with j ordinary derivatives. We do not claim that historical C3 data supply
these bounds in arbitrary dimension.

### The low-dimensional diagonal is not silently zero

For the full-cone family k=0, b'(0)=0 makes nu-dot at lambda=0 zero. Its
second derivative need not vanish. In d=2 the density at the diagonal need
not vanish either, and the second-jet density includes

```math
\begin{aligned}
\left.\tfrac12\partial_\lambda^2B_\lambda(w)\right|_{\lambda=0}
 &=\tfrac12\int_{\sqrt w}^{\epsilon}a_{\lambda\lambda}(0,w,v)\,dv
       -\tfrac12a_0(w,\sqrt w)\ddot\nu_0,\\
\ddot\nu_0&=-\frac{2h_2(x,\omega,1)}d\,w^{3/2},\qquad
 a_0(w,\sqrt w)=\frac{\phi(x)}{2\sqrt w}\quad(d=2).
\end{aligned}\tag{S14}
```

This is a real order-w density term, not a negligible oriented strip. It is
part of the pushed physical second jet and its signed response cancels by
the j=1 kernel moment after the fixed-phase tails are accounted for. In d>2
the factor (1-U) to power d-2 makes this particular value zero. The proof of
(S13) uses (S11), not this special vanishing. For the face first jet nu-dot
at zero is zero in every dimension, and the corner model has no lambda
derivative. Thus no diagonal contribution is missing in any of the three
comparisons.

## 4. GM-S1: actual full-cone producer on the entire compact source collar

For x in the whole compact auxiliary source set use normal target coordinates
xi=v(L+RQ). The target density is the actual exponential Jacobian
j_x(xi)=sqrt(|det g_x(xi)|); the source measure d mu_g(x) is kept exactly.
At the reference radial-null cutoff v<epsilon the actual integral is

```math
\begin{aligned}
I_1(x)&=\int d\omega\int_0^\epsilon\int_0^1
 \frac{v^{d-1}(1-R)^{d-2}}{2^{d-1}}
 j_x(v\Delta)\phi(\exp_x(v\Delta))\\
 &\qquad{}\cdot K_d\bigl(c_d\rho(v^2R)^{d/2}H(x,\omega,v,R)\bigr)\,dR\,dv.
\end{aligned}\tag{S15}
```

Define its proof interpolation by replacing v with e=lambda v **inside**
j_x, phi and H, leaving the displayed physical polar measure and v squared R
unchanged. At lambda=1 it is exactly (S15). Put
Phi(e,R)=R H(x,omega,e,R) to power 2/d. By (S8), Phi_R=1+O(e squared),
so a fixed small epsilon gives a positive lower bound. Its inverse
R=U(e,zeta) and all required mixed derivatives are bounded by implicit
function differentiation. With w=v squared Phi, the pushed density is (S9)
with k=0 and

```math
\begin{aligned}
\Psi(e,\zeta)&=
 \left.\frac{(1-R)^{d-2}j_x(e\Delta)\phi(\exp_x(e\Delta))}
 {2^{d-1}\Phi_R(e,R)}\right|_{R=U(e,\zeta)}.
\end{aligned}\tag{S16}
```

The true diagonal solves w=nu squared H(x,omega,lambda nu,1) to power 2/d.
The implicit equation gives precisely b in (S9), including b'(0)=0.
Thus every hypothesis of (S10) has been **derived from the actual metric
interval**, including at R=0, rather than assumed. The physical second lambda
jet on the original fixed cone is exactly (G7), by (S8) and the independent
endpoint density/field jets. Fixed-density differentiation there is legitimate.
Its pushed form retains (S14). Equation (S13) proves the normalized actual-
minus-entire-second-jet estimate, uniformly in x and direction. Multiplication
by any fixed bounded source field and the actual source volume then preserves
convergence on the whole compact source domain, even up to both faces.

## 5. The selected temporal cutoff and the actual signed conversion

We now justify the cutoff used in the theorem, rather than rename epsilon.
For each of the full/face/corner integrals below, its flattened source has
x(v,R)=x_0+O(v) smoothly (x is constant for full), and its target is
exp_x(v Delta_x). The **actual** temporal gap is

```math
\begin{aligned}
q(v,R)&=\tau(\exp_{x(v,R)}(v\Delta_x))-\tau(x(v,R))\\
 &=v\,d\tau_{x_0}(\Delta_{x_0})+O(v^2).
\end{aligned}\tag{S17}
```

The leading coefficient is uniformly positive on the compact future directions.
At w=0, R=U(v,0)=0 exactly, so the v derivative of q(v,U(v,w/v squared))
is bounded positively for small v. The implicit function theorem gives a
smooth upper root v=V_delta(w) for q=delta on an annulus whose v is bounded
above and below by positive multiples of delta. After decreasing delta once,
all these roots lie in the normal/collar tubes. At fixed positive delta they
and all needed w derivatives have uniform compact bounds. The region away
from that root has the expected sign by monotonicity; for sufficiently small
phase the diagonal lies well below the root.

Consequently the signed difference between temporal-short and a reference
v-short integral is, near zero phase, the actual oriented density

```math
\begin{aligned}
B_{\mathrm{shell}}(w)&=
 \int_{\epsilon}^{V_\delta(w)} a_1(w,v)\,dv.
\end{aligned}\tag{S18}
```

Both endpoints in this expression are separated from zero, and the genuine
amplitude is smooth there by (S8) and the flattenings below. Its degree-N
Taylor polynomial has an O(w to power N+1) remainder. The signed moments
therefore prove its **normalized** response tends to zero. Its positive-phase
complement is exponentially small on the compact original domains. The same
argument applies to the model's affine normal-time cutoff in (G8); for its
Z K-prime term the moments have the same zeros, by integration by parts.
This proves the needed conversion, including its sign as specified in (G15).
It is not an assertion that arbitrary macroscopic or cut-locus shells vanish.

For full cones, (S15)–(S18) and (G8)–(G9) now prove **GM-S1** at every
sufficiently small fixed temporal cutoff:

```math
\begin{aligned}
S^{\mathrm{full}}_{\chi,\phi}(\rho)
 &\longrightarrow\mathcal B_{\chi,\phi}
 :=\int_M\chi(\Box_g\phi+R_g\phi/2)\,d\mu_g.
\end{aligned}\tag{S19}
```

The point term is allocated once to this full term. The actual truncated
physical short action still has the exact face and corner corrections (G10).
No small-collar-volume argument removes them.

## 6. GM-S2: flatten the entire actual single-face strip

Use a temporal-flow chart x=(t,z), t=tau, with future face t=f(z). Put
F(t,z)=t-f(z), alpha=dF, and choose a smooth orthonormal normal frame at each
source. For xi=v Delta_x define the actual future gap

```math
\begin{aligned}
d(x,v,R,\omega)&=F(\exp_x(v\Delta_x))-F(x)=vD(x,v,R,\omega).
\end{aligned}\tag{S20}
```

The divided difference D is smooth through v=0, with
D(x,0,R,omega)=alpha_x(Delta_x) bounded strictly positively, because alpha has
future timelike dual. Also d_t=O(v). The actual face term in (G10) is precisely
the source strip 0<a<d(f-a,z,v,R,omega), where a=f(z)-t. It is not a strip
with the source time frozen in d. For beta in [0,1] solve

```math
\begin{aligned}
a&=\beta vD(f-a,z,v,R,\omega),\\
\frac{da}{d\beta}&=\frac{vD}{1+\beta vD_t}.
\end{aligned}\tag{S21}
```

The defining function is strictly increasing in a, with derivative 1+O(v).
Its endpoint signs bracket a unique root between positive multiples of beta v;
conversely beta=a/d parametrizes the whole strip monotonically. Compact smooth
implicit-function bounds give all needed derivatives. This includes auxiliary
sources below the past face; J restores those, not an omission in F.

For interpolation set e=lambda v in the root a_e=beta e D(f-a_e,z,e,R,omega).
Use x_e=(f-a_e,z), target exp_x_e(e Delta_x_e), phase
Phi(e,R)=R H(x_e,omega,e,R) to power 2/d, and the **physical** depth factor
vD/(1+beta e D_t). The moving source is differentiated in this phase.
Since H=1+O(e squared) with uniform base derivatives, Phi_R=1+O(e squared).
The pushed face density is (S9) with k=1, and

```math
\begin{aligned}
W_e^F&=w(x_e)\chi(x_e)j_{x_e}(e\Delta)\phi(\exp_{x_e}(e\Delta)),\\
\Psi_F(e,\zeta)&=
 \left.\frac{(1-R)^{d-2}D\,W_e^F}
 {2^{d-1}(1+\beta eD_t)\Phi_R}\right|_{R=U(e,\zeta)},\\
w(x)&=\sqrt{|\det g(t,z)|}.
\end{aligned}\tag{S22}
```

Every numerator, denominator and mixed derivative here is controlled on a
fixed compact set by (S8), (S20) and (S21). The physical target measure is
j_x d xi; w is the **source** coordinate density. No endpoint measure has
been lost by using source orthonormal coordinates for the target. On R=1
the true diagonal again has the form (S9), with b'(0)=0. Therefore the k=1,
p=2 instance of (S11)–(S13) proves the normalized actual-minus-first-
interpolation-jet face estimate. It includes the moving diagonal strip and
all mixed source-time derivatives. The parameter z ranges over the entire
physical spatial side of this chart; it need not be a joint collar or a
regular height level. Constants are uniform there. The temporal shell (S18)
has the same smoothness after (S21), so the actual shared cutoff is restored.

### Evaluate the full face jet, not just its geometric part

All quantities next are evaluated at the face point p=(f(z),z). Let
T=partial_t at fixed z, let n_tilde=g inverse alpha, and put
s=g inverse(alpha,alpha), Q=w chi phi. For a fixed normal-frame vector Delta
write A=alpha(Delta), B=(nabla squared F)(Delta,Delta). Differentiating the
actual geodesic gap and the root in (S21) gives, after beta integration,
the complete first/two-displacement face jet

```math
\begin{aligned}
Q\,\alpha(\xi)K_d(Z)
 +\left[\frac Q2\nabla^2F(\xi,\xi)
 -Q\,\alpha(\xi)T(\alpha(\xi))
 -\frac12\alpha(\xi)^2TQ
 +w\chi\,\alpha(\xi)d\phi(\xi)\right]K_d(Z).
\end{aligned}\tag{S23}
```

In T(alpha(xi)), the coefficients of xi in the smoothly varying orthonormal
frame are held fixed. To check every term, at e=0 the root has a_e=beta e A
plus O(e squared). The depth quotient expands as
A+e[B/2-2 beta A T A]; the source product w chi phi contributes
-e beta A TQ; target displacement contributes e w chi d phi(Delta).
Multiplying and integrating beta gives (S23). The exponential target Jacobian
and H have no linear e term in source normal coordinates. Their first possible
face contribution has displacement degree three and is in the proved signed
remainder, not discarded by a coordinate-volume estimate.

The linear kernel response vanishes. The positive-pair sign for F reverses
(G8)'s tensor response. Writing $`\alpha_A=\alpha(E_A)`$ gives
$`s=\eta^{AB}\alpha_A\alpha_B`$ and
$`2\eta^{AB}\alpha_A T(\alpha_B)=T s`$. The differentiated components include
frame variation; replacing them by coordinate partial derivatives of the
one-form would be incorrect. Hence (S23) has the actual limiting coordinate density

```math
\begin{aligned}
\mathcal F&=-Q\Box_gF+T(Qs)-2w\chi\,\widetilde n(\phi)\\
 &=w\{\phi\widetilde n(\chi)-\chi\widetilde n(\phi)\}
       -\partial_{z^i}^{\mathrm{trace}}(Q\widetilde n^i),\\
\partial_{z^i}^{\mathrm{trace}}&=\partial_{z^i}+f_i\partial_t.
\end{aligned}\tag{S24}
```

For the second equality use Box F=w inverse partial_mu(w n_tilde^mu) and
s=n_tilde^0-f_i n_tilde^i; expand the whole divergence, including density,
metric, frame and both trace derivatives. This proves the identity without
assuming an extrinsic-curvature cancellation. Finally d Sigma_g=w sqrt(s) dz
and n_+=n_tilde/sqrt(s), so the divergence theorem on the physical spatial
side gives **GM-S2**:

```math
\begin{aligned}
\beta_d\rho^{1+2/d}F_{\chi,\phi}
 &\longrightarrow\mathcal N_{\chi,\phi}-\mathcal T_{\chi,\phi},\\
\mathcal N_{\chi,\phi}&=
 \int_{\Sigma_+}(\phi n_+(\chi)-\chi n_+(\phi))\,d\Sigma_g.
\end{aligned}\tag{S25}
```

Here $`\mathcal T`$ is precisely the compensating joint flux (G13), summed over the chart
pieces. Smooth source weights kill artificial edges; if sharp pieces are
used, their extra divergence fluxes are retained on both sides. The past-face
flux of the bulk is still the negative term in (G14); it has not been replaced
by (S25). For unit fields N vanishes, whereas T generally does not.

## 7. GM-S3: the actual two-boundary corner, including its source dependence

In a regular joint height chart z=Z(y,s), h(Z)=s, write the source as
x=(f(Z(y,s))-a,Z(y,s)). Let d(s,a,v,R,omega) be the **same actual gap** (S20)
in these variables. Both d_s and d_a are O(v). The true corner domain is
0<s<a<d(s,a,...). Put alpha=beta+(1-beta)gamma for beta,gamma in [0,1] and
solve the coupled root by a single variable b:

```math
\begin{aligned}
b&=d(\beta b,\alpha b,v,R,\omega),\qquad
 s=\beta b,\quad a=\alpha b,\\
\left|\frac{\partial(s,a)}{\partial(\beta,\gamma)}\right|
 &=\frac{(1-\beta)b^2}{1-\beta d_s-\alpha d_a}.
\end{aligned}\tag{S26}
```

The derivative of the right side of the root equation with respect to b is
O(v), so a common fixed small cutoff gives a unique positive smooth root
b comparable to v. Conversely beta=s/d and alpha=a/d recover every point
of the actual domain; gamma then parametrizes alpha in [beta,1]. Thus this
is an exact flattening, not a hinge approximation. For the Jacobian, first
use independent (beta,alpha); the rank-one determinant of the implicit map
(s,a)=d(s,a)(beta,alpha) is d squared divided by 1-beta d_s-alpha d_a.
Then multiply by 1-beta. In particular the term involving d_a must remain:
the source-dependent general-metric gap is not the old conformal coordinate
gap independent of source time.

Let G(y,s) be the actual weighted spatial height-chart Jacobian; at zero it
sums to dA_{h=0}/|dh|. For interpolation replace physical v by e=lambda v in
the root b_e=eD(beta b_e,alpha b_e,e,R,omega), while keeping the **physical**
depth Jacobian v squared times its smooth quotient. Define x_e from this root.
The ratio phase is R H(x_e,omega,e,R) to power 2/d. All implicit denominators
are bounded away from zero, so the actual pushed corner amplitude has k=2
in (S9), with

```math
\begin{aligned}
W_e^J&=G(y,s_e)w(x_e)\chi(x_e)j_{x_e}(e\Delta)\phi(\exp_{x_e}(e\Delta)),\\
\Psi_J(e,\zeta)&=
 \left.\frac{(1-\beta)D^2(1-R)^{d-2}W_e^J}
 {2^{d-1}(1-\beta d_s-\alpha d_a)\Phi_R}
 \right|_{R=U(e,\zeta)}.
\end{aligned}\tag{S27}
```

The d derivatives in this formula are evaluated at displacement e, not v.
Source-time, height-root, frame, metric, chart, partition and target-field
variations are all differentiated in Phi_R and Psi_J. They are smooth with
compact mixed bounds from (S8) and (S26). On the true diagonal this also gives
(S9), including b'(0)=0 for its **diagonal function** (distinct from the depth
root b in (S26)). Consequently the k=2,p=1 instance of (S11)–(S13) proves

```math
\begin{aligned}
\beta_d\rho^{1+2/d}(J-J^{\mathrm{tan}})&\longrightarrow0.
\end{aligned}\tag{S28}
```

The moving-diagonal contact a nu-dot is retained. After w differentiation it
has exactly the powers required in (S12), including in d=2; no orientation
strip is thrown away. The temporal-shell argument (S18) applies on this same
flattened compact parameter domain, restoring the selected cutoff exactly
before its vanishing normalized response is used.

At e=0 in (S27) the source is the actual joint point, D=alpha_+(Delta), H=1,
and the target normal Jacobian is one. Integration of beta,gamma supplies
one-half and the summed height Jacobian supplies dA/|dh|. Therefore its
**derived** tangent model is the one evaluated in (G13), not a chosen target:

```math
\begin{aligned}
-\beta_d\rho^{1+2/d}J&\longrightarrow
 \int_{h=0}\frac{w\chi\phi s_+}{|dh|}\,dA,\\
-\beta_d\rho^{1+2/d}J-\mathcal T_{\chi,\phi}
 &\longrightarrow\int_J\chi\phi\coth\theta\,dA_g.
\end{aligned}\tag{S29}
```

The second line is **GM-S3**, using the independently proved induced measure
and normal discriminant (G12). It adds the actual face compensation from
(S25), including its generally nonzero unit-field value. Both endpoint measures
are present in (S27). In 2D the transverse height chart is zero-dimensional
and its empty Gram determinant is one, so every joint point is counted once.

## 8. Quantified short theorem, partition cancellation and the #151 boundary

**Theorem (general-metric short producer).** For each d at least two, each
fixed smooth G-SS region and smooth Cauchy temporal function, and each fixed
finite family of smooth real endpoint fields on a neighborhood of its compact
auxiliary tubes, there is delta-star>0 such that for every fixed
0<delta<delta-star, the canonical strict-temporal-short action satisfies

```math
\begin{aligned}
S^\delta_{\chi,\phi}(\rho)&\longrightarrow
 \int_M\chi(\Box_g\phi+R_g\phi/2)\,d\mu_g\\
 &\quad+\int_{\Sigma_+}(\phi n_+(\chi)-\chi n_+(\phi))\,d\Sigma_g
 +\int_J\chi\phi\coth\theta\,dA_g.
\end{aligned}\tag{S30}
```

To prove it choose one cutoff meeting the finitely many locality, null-tube,
phase-inverse, face-root, height-root and temporal-shell bounds above. The
exact identity (G10) holds for each source chart at every density. Insert
(S19), (S25) and (S29); the two T allocations combine exactly as in (G13).
All comparison constants can be maximized over the finite geometric/field
family, and all error integrals are dominated by the explicit compact bounds
in (S10)–(S13), so finite summation is legitimate **after** the estimates.

A source partition multiplies chi in the bulk and joint and differentiates it
in N; its derivatives sum to zero because the partition sums to one near the
actual faces. Target partition **weights** require all ordered labels; Box
and normal derivatives of their sum, which is one, vanish. The product rule
then retains Box(phi) and the original endpoint-field normal derivatives;
it does not set those derivatives to zero. In particular the summed face
flux remains phi n(chi)-chi n(phi) for the original fields. This proves
cancellation of artificial chart and partition boundaries, retaining every actual partner and every
true face/joint contribution. No equality of chart labels is imposed, including
for overlapping charts on the same physical interval. All components and
positive-height critical points outside the regular joint collar remain.
Empty-joint compact-Cauchy slabs use only the full and single-face arguments.
For unit fields (S30) is exactly the independent half-curvature plus joint
target. It is a short result, not the full canonical action theorem.

The proof also evaluates the **local** signed conversion (G15) between any
two sufficiently small cutoffs of the temporal/radial-normal/affine kinds used
here: full, face and corner shell responses separately vanish by (S18), and
their finite-density sum is still the exact signed difference. Equality is
allocated to long throughout. A different long cutoff retains the opposite
signed term; there is no replacement of a macroscopic or focusing shell by
this local result. The complete actual long domain, all cut/conjugate branches,
and their possibly nonzero signed response remain #151's independent task.
No unfinished conclusion of #149 or #151 was used: only the established
canonical kernel moments and exact interfaces were consumed.

### Instantiation at the companion's seven-dimensional slab

The [#151 continuation at `db69142`](https://github.com/q5m-ai/causal-set-emergence/blob/db691421624f0e598fe9e80a660cccaac4db499a/notes/seven-dimensional-focusing-obstruction.md)
now records a written complete-action focusing obstruction, not a universal
zero long producer. It is not used as a lemma above. Its selected ultrastatic
unit-sphere times four flat circles has compact complete Cauchy slices; the
open time slab is precompact and ambient causally convex by time monotonicity.
Its two spacelike compact boundary slices have empty joint, and scalar
curvature is two in the fixed convention. These directly verify the unchanged
G-SS hypotheses. Instantiating (S30), rather than duplicating a special-case
short proof, gives

```math
\begin{aligned}
X&=S^2_1\times(\mathbb R/20\mathbb Z)^4,\qquad
 M=(-2,2)\times X,\\
S^\delta_{1,1}(\rho)&\longrightarrow
 \tfrac12\int_M R_g\,d\mu_g=\mathrm{Vol}_g(M).
\end{aligned}\tag{S31}
```

For every sufficiently small fixed shared temporal cutoff this is a **finite
short** limit, consistent with the companion's leading-scale short statement
O16. It does not cancel or estimate its nonlocal focusing term. The companion's
O3 proof and any resulting corrected umbrella statement still require their
own verification; this local theorem neither endorses a universal finite
full-action target nor silently removes this geometry from the core.

## 9. Acceptance and verification

| #150 item | Derived analytic/geometric output | Verification boundary |
| --- | --- | --- |
| Actual interval and endpoint data in every dimension | (S1)–(S8), actual thin containment, smooth null-edge phase and metric-derived second jet; (S15)–(S16) retain source and target measures | Written geometric proof; not a formal port |
| GM-S1 actual full-cone remainder | k=0 instance of (S10)–(S14), (S16), temporal shell, then (S19) | Uniform on the whole compact source collar, not bounded rapidity only |
| GM-S2 entire single-face producer | Actual implicit strip (S21), derived mixed bounds, k=1 comparison, complete jet/divergence (S23)–(S25) | Both oriented bulk face fluxes remain (G14) |
| GM-S3 actual joint comparison | Coupled moving roots/Jacobian (S26), k=2 comparison (S28), independent target plus actual compensation (S29) | No bare-wedge or conformal-invariance substitution |
| Remainders, dimensions and contacts | Explicit parity bounds (S12)–(S13), full moving-contact ledger (S11), nonzero 2D term (S14) | Smooth core; no assertion of optimal finite regularity |
| Finite atlas, all partners, common cutoff | (G10)–(G15), now with the summable estimates; (S17)–(S18), (S30) | General nonlocal long producer remains #151 |
| Independent target | Metric contraction (G3)–(G9), Gram/coarea (G12), actual compensated identification (S29) | Not defined by the limiting action |
| Flat, completed conformal, curved/variable-angle controls | Existing #76/#136 tests plus the continuation regressions described below | Diagnostics are not the proof of the estimates |

The continuation diagnostics exercise the null-rescaled metric of the genuinely
nonconformally-flat sphere-circle product, actual near-null interval volume
from its metric distance integral, the parity remainder bounds and all three
moving-contact formulas (including the low-dimensional nonzero contact), the
source-dependent face root and corner Jacobian, and the general face-flux
algebra. Earlier tests retain actual completed polynomial/nonpolynomial
conformal integrals, nonconstant endpoint fields, independent variable-angle
geometry, both measures and ordered partition/cutoff restoration. These are
regressions of the general proof, not new example-based theorem substitutes.

For clarity, the product-interval diagnostic uses the exact ultrastatic formula
V equal to the spatial integral of the positive part of T minus the two
metric distances. In sphere Fermi coordinates (ell,b) and circle coordinate z,
the spatial density is cos(b/a), and each spherical distance satisfies
cos(distance/a)=cos(b/a)cos((ell-ell_tip)/a). It integrates ell from -u/2 to
(v-u)/2+u/2, including **both end caps**, and solves the genuine transverse
lens boundary. The cutoff is below both spatial cut scales. Its source/target
sphere separation is (v-u)/2 and its time separation is (v+u)/2. Thus its
near-null test is an actual geometric interval integral, not the H Taylor
polynomial. The synthetic signed-density test is separately labeled as a test
of (S9)–(S13), and its constants are dimension-dependent. High-precision zero
probes are evaluated by a convergent series: direct subtraction of nearly
equal terms times v to power -3 is numerically unstable even at high precision.

No Lean source, checker, dependency or build input changes. These written
producer proofs have not been compiled and have no independent human
mathematical review yet; #86 retains those distinct verification obligations.
The proof is not certified by passing Python, Markdown or CI checks. No full
G-SS action/expectation theorem, rate, shrinking-cutoff uniformity, noncompact
tail, degenerating-angle estimate or sample-wise convergence is claimed.
