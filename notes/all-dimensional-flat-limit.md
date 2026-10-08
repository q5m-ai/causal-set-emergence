# Dimension-indexed flat two-face producers and limits (#149)

**Written theorem, not a new Lean result or independent human review.** For
every integer dimension at least two, this note proves the deterministic and
then expected limit for **every G-SS region in Minkowski space**, without an
assumed graph presentation, global causal envelope or combined slope budget.
The proof is dimension-indexed, not an inference from the existing 2D–6D
examples. Section 10 states the residual distinction between this theorem and
G-SS on an arbitrary flat manifold; in particular flat quotients are not
silently included. #149/#81/#24 are not resolved in that broader reading.

Use [the shared producer interface](dimension-producer-interface.md),
[the independent G-SS contract](general-contract.md#3-a-precise-non-vacuous-general-core-candidate),
[the dimension kernel](dimension-kernels.md), and [the separate expectation
bridge](../formal/DIMENSION_EXPECTATION.md). The bounded written 5D/6D
corollaries in [#132](dimension-five-six-short.md#7-go-narrowstop-ledger-and-matched-global-limit-contracts)
already exist; adding their short and long pieces is not new progress here.

## 1. Quantified theorem and regularity

Fix an integer d at least two and Minkowski space with signature (+,-,...,-).
Let M be a nonempty bounded open ambient-causally-convex region. Its entire
frontier consists of two compact embedded spacelike hypersurfaces with
boundary, Sigma-minus and Sigma-plus, respectively past and future for M.
Each is achronal, their relative interiors are disjoint, and their common
boundary is exactly a compact embedded spacelike joint J. Their conormals at
J are independent. There are no further strata. All components are retained.
These are precisely the Minkowski instances of G-SS, not analytic premises.

Smoothness suffices. More explicitly the following proof works with C-to-the-r
faces and joint, where

```math
\begin{aligned}
r=r(d)&=\max\{3,\lceil d/2\rceil+1\},\\
N&=\lfloor d/2\rfloor,\quad q=d/2,\quad n=d-1.
\end{aligned}
\tag{A1}
```

This is a sufficient bound, not a minimality assertion: it is 3 in dimensions
2–4, 4 in dimensions 5–6, and grows thereafter. It does not change any old
C3 contract. The induced positive metric on J is minus the ambient metric
restricted to its tangent space; in dimension two its measure counts each
endpoint once. Both face normals are future unit timelike. Independently set

```math
\begin{aligned}
\mathcal J(M)&=\int_J\frac{C}{\sqrt{C^2-1}}\,dA_J,
\qquad C=g(n_-,n_+)>1.
\end{aligned}
\tag{A2}
```

**Theorem.** For every such fixed region, there is delta-star>0 such that
for every fixed 0<delta<delta-star the actual strict-v-short action, with the
physical point once, tends to (A2), and the actual signed equality-long action
tends to zero. Consequently

```math
\begin{aligned}
\mathcal A_{\rho,d}(M)&\longrightarrow\mathcal J(M),\\
\mathbb E_{\mathrm{Pois}(\rho\,dx|_M)}
 A^{\mathrm{disc}}_{\rho,d}&\longrightarrow\mathcal J(M).
\end{aligned}
\tag{A3}
```

The action, layers and law are the unchanged independent objects in the
shared interface, not defined by this limit. Geometry, cutoff and margins are
fixed before density varies. No rate for the full action, shrinking-cutoff
uniformity, small-angle uniformity or sample-wise conclusion is asserted.
The following sections prove the producers before their assembly.

## 2. Graph coordinates are a consequence, not a hypothesis

Let pi be spatial projection in any fixed inertial frame. Its differential on
a spacelike hypersurface is invertible: a vector in its kernel would be
vertical timelike. Achronality makes pi injective on each entire face, since
two different points on the same vertical line are timelike related.
Compactness and the inverse function theorem, including boundary charts,
therefore identify each face with a compact embedded spatial domain.

Every nonempty vertical section of M is one bounded open interval. Indeed
any two points of the section have their entire intermediate vertical segment
in M by ambient interval containment. Its endpoints are on the frontier.
The past/future orientation puts the lower endpoint on Sigma-minus and the
upper on Sigma-plus. Neither can be in J: J is also on the other labeled
achronal face, which would then contain two vertically separated points.
Conversely a face-interior point is approached by vertical interior points
on its region side. Taking closures proves that the two projection images
are the same compact domain K, whose interior is Omega=pi(M), and whose
boundary S=pi(J) is a compact regular hypersurface. Thus

```math
\begin{aligned}
M&=\{(t,x):x\in\Omega,\ l(x)\lt t\lt f(x)\},\\
h&=f-l>0\ \text{on }\Omega,\qquad h=0\ \text{on }S.
\end{aligned}
\tag{A4}
```

Here f,l are C-to-the-r up to K. Independence of the two conormals is exactly
dh nonzero on S. Standard extension through smooth boundary charts and a
finite partition extends f,l to a neighborhood of K. Their actual derivatives
on K have norm strictly below one; compactness and continuity preserve
independent strict bounds on a smaller neighborhood. Choose its width so
that every sufficiently short translated segment from K remains there.
Also h>0 in that neighborhood precisely on Omega: the implicit function
theorem gives its sign on both sides of S, and compactness excludes other
zeros near K. No extension to all space or global Lipschitz constant is used.
In particular neither h nor its positive part has to be strictly Lipschitz.

A compact manifold has finitely many components; all boundary components,
including inner boundaries, are in S. Compact regular S gives a uniform
noncritical collar. Points of positive height outside that collar, including
all height critical points, remain in the fixed bulk integration domain.
In dimension two S is a finite regular zero set, not an arbitrarily chosen
two-point joint. A nonempty bounded Minkowski instance cannot have empty J:
a compact boundaryless spacelike face would project to a nonempty subset of
Euclidean space both open and compact. Compact-Cauchy slabs on flat quotients
are a different case, explicitly retained in section 10.

## 3. Actual short overlap and finite-order primitive

For a real C-to-the-r spatial source weight w near K define the actual overlap
V_w(z) by integrating w at the source and the indicator of M at the translated
target. Write z=(tau,b), with tau at least |b|. For sufficiently small z the
independent local bounds on f and l select the intersecting time endpoints.
They also show that positivity of the gap forces x+b in Omega: writing the
gap as h(x+b)+l(x+b)-l(x)-tau makes h(x+b)>0. Therefore, with no missing
partners or artificial exterior points,

```math
\begin{aligned}
q_z(x)&=\tau-f(x+b)+f(x),\\
V_w(z)&=\int_\Omega w[h-q_z]_+\,dx\\
 &=V_w(0)-\int_\Omega wq_z\,dx
       +\int_{0\lt h\lt q_z}w(q_z-h)\,dx,
\qquad V_w(0)=\int_\Omega wh\,dx.
\end{aligned}
\tag{A5}
```

This is local in displacement, not a global graph-envelope assumption.
The weight may be signed. In particular, the proof covers the steep symmetric
capsule of section 9, for which the old combined budget is impossible.

Cover the entire compact S by finitely many height charts x=Phi_i(y,a),
h(Phi_i)=a, with compactly supported partition weights. Their weighted
Jacobians W_i are C-to-the-(r-1), on fixed compact tangential boxes and a
common two-sided height interval. In dimension two each tangential box is a
single point with counting measure. The height derivative of q_z is bounded
by a constant times |b|. For all sufficiently small z it is less than one-half
in absolute value. The implicit function theorem gives a unique C-to-the-r
root T_i(y,z) of a=q_z(Phi_i(y,a)), with uniform collar clearance. The moving
collar term in (A5) is the sum of

```math
\begin{aligned}
I_i(z)&=\int dy\int_0^{T_i(y,z)}
 W_i(y,a)[q_z(\Phi_i(y,a))-a]\,da.
\end{aligned}
\tag{A6}
```

The oriented integrals extend the formula to a full small displacement ball;
there it need not be the actual spacelike covariogram. Its first parameter
derivative has no upper-endpoint term because the gap vanishes at T_i.
The differentiated integrand is jointly C-to-the-(r-1). Rescale the oriented
height interval to [0,1]; compact domination permits r-1 further derivatives
of this first derivative. Thus I_i is C-to-the-r, despite the one derivative
lost by the chart Jacobian. The bulk term is on the fixed compact domain and
has the same regularity. This constructs the extension; no Taylor jet is an
admissibility field.

Let p=grad f, g=grad h, k=|g| on S. Taylor expansion of the constructed
extension, with the summed zero-height Jacobian equal to dA_S/k, gives

```math
\begin{aligned}
\widetilde V_w(\tau,b)={}&V_w(0)-\tau\int_\Omega w
 +\int_\Omega wp\cdot b+\frac12\int_\Omega wD^2f[b,b]\\
 &+\frac12\int_S\frac{w}{k}(\tau-p\cdot b)^2\,dA_S+R_w(z),\\
|D^jR_w(z)|&\le C_w|z|^{3-j}\quad(0\le j\le3),\\
|D^jR_w(z)|&\le C_w\quad(4\le j\le r).
\end{aligned}
\tag{A7}
```

For j=3 the first bound means boundedness. These are Taylor integral estimates
for the actual derivatives, not just a value-only cubic bound. Constants are
finite for fixed geometry and w; choose the displacement cutoff below one.

Ordinary sphere moments follow from reflection and rotation invariance:
first and off-diagonal second moments vanish, all diagonal moments agree,
and their sum is the sphere area s_d. This remains true for the two atoms in
2D. Hence the angular overlap is

```math
\begin{aligned}
\int_{S^{d-2}}\widetilde V_w(\tau,r_0\omega)\,d\omega
 &=C_w^{(0)}+L_w\tau+Q_w\tau^2+U_wr_0^2+\int R_w\,d\omega,\\
C_w^{(0)}&=s_dV_w(0),&L_w&=-s_d\int_\Omega w,\\
Q_w&=\frac{s_d}{2}\int_S\frac{w}{k}\,dA_S,&
U_w&=\frac{s_d}{2n}\left(\int_\Omega w\Delta f
                  +\int_S\frac{w|p|^2}{k}\,dA_S\right).
\end{aligned}
\tag{A8}
```

In particular the future Hessian has not been discarded.

## 4. All-dimensional sharp bases and signed responses

Use sigma=tau squared minus r_0 squared and v=tau+r_0, with exactly the
Jacobian j_d in the shared interface. The four actual basis densities are

```math
\begin{aligned}
F_{d,a}(\sigma)&=\int_{\sqrt\sigma}^{\delta}j_d(\sigma,v)a\,dv,\\
a&\in\{1,\tau,\tau^2,r_0^2\},\quad 0\lt\sigma\lt\delta^2.
\end{aligned}
\tag{A9}
```

They are zero above the cutoff. For a=tau to power p times r_0 to power k-p,
let A_l be the coefficients of (1-X) to power d-2+k-p times (1+X) to power p,
and put D=d-2+k. Direct integration of the finite Laurent polynomial gives

```math
\begin{aligned}
F_{d,a}(\sigma)&=\frac1{2^{d-1+k}}\sum_l A_l\sigma^l
\begin{cases}
\displaystyle\frac{\delta^{D-2l}-\sigma^{(D-2l)/2}}{D-2l},&D\ne2l,\\
\displaystyle\log\delta-\tfrac12\log\sigma,&D=2l.
\end{cases}
\end{aligned}
\tag{A10}
```

Both moving endpoints are evaluated. This formula is valid in every integer
dimension at least two, without a finite table. In particular F_constant in
2D has a logarithmic divergence at zero; it is still locally integrable.
The following exact identities are especially useful:

```math
\begin{aligned}
F_{d,\tau}&=\frac{(\delta-\sigma/\delta)^{d-1}}{2^d(d-1)},\\
F_{d,\tau^2}-F_{d,r_0^2}&=\sigma F_{d,1},\\
(d-1)F_{d,\tau^2}+F_{d,r_0^2}
 &=\frac{(\delta+\sigma/\delta)(\delta-\sigma/\delta)^{d-1}}{2^{d+1}}.
\end{aligned}
\tag{A11}
```

For the last identity change to fixed tau: j_d dv equals one-half r_0 to power
d-3 times d(tau), and differentiate tau times r_0 to power d-1. Its lower
endpoint is zero even in 2D. Thus the linear mode is a polynomial, and the
nonpolynomial quadratic coefficients are 1/d and -(d-1)/d times sigma times
the constant mode. All remaining terms are polynomials in sigma.

The nonpolynomial part of F_constant is alpha_d times sigma to power q-1
in odd dimensions, and alpha_d times sigma to power q-1 times log(sigma) in
even dimensions, where

```math
\begin{aligned}
\alpha_{2N+1}&=\frac{(-1)^N\sqrt\pi\,\Gamma(N)}{4\Gamma(N+1/2)},\\
\alpha_{2N}&=\frac{(-1)^N}{2^{2N}}\binom{2N-2}{N-1}.
\end{aligned}
\tag{A12}
```

For odd d, expand the fixed-tau polynomial (tau squared minus sigma) to power
N-1 and evaluate its lower endpoint. Its coefficient is minus one-half the
integral from zero to one of (t squared minus one) to power N-1; the ordinary
beta integral gives (A12). For even d, the v-to-power-minus-one coefficient
in (A10) is (-1) to power N-1 times the central binomial coefficient, and the
lower log contributes minus one-half. These are ordinary convergent primitive
computations, not analytic-continuation assignments to divergent integrals.

Integration by parts in each factor of the actual kernel recurrence proves
the shared Mellin formula: the boundary term z to power a times a
polynomial-exponential vanishes for a>0. Finite polynomial expansion also
proves absolute convergence. Differentiation in the Mellin exponent is
justified by power/log integrable envelopes on compact substrips above -1.
Thus

```math
\begin{aligned}
\int_0^\infty\sigma^j\log\sigma\,
 K_d(c_d\rho\sigma^q)\,d\sigma
 &=(c_d\rho)^{-2(j+1)/d}
 \left(M'_d(j)-\frac2d\log(c_d\rho)M_d(j)\right).
\end{aligned}
\tag{A13}
```

Define H0,H2 to be M_d(q-1),M_d(q) in odd dimensions, and their derivatives
in even dimensions. Products in the Mellin formula and the Gamma recurrence
now give, for all N in the stated ranges,

```math
\begin{aligned}
\frac{s_d\alpha_d}{c_d}H0&=\frac{a_d}{\beta_d},\\
H2&=-d\Gamma(1+2/d)H0&& (d\text{ odd}),\\
H2&=-\frac d2\Gamma(1+2/d)H0&& (d\text{ even}),\\
-\beta_dc_d^{-1-2/d}\frac{\alpha_d}{d}H2&=\frac2{s_d}.
\end{aligned}
\tag{A14}
```

For clarity, the odd first product is
alpha_d M_d(q-1)=1/[d(d-1)(d+1)]; combine it with the specified odd pair/point
ratio. In the even case
M'_d(N-1)=(-1)^N/[N squared times (N+1)] and
M'_d(N)=(-1) to power N+1 times Gamma(1+1/N)/[N(N+1)].
Substitution of (A12), the even pair/point ratio and factorials proves both
even identities. No normalization is inferred by requiring a target limit.

The constant mode therefore cancels the physical point divergence exactly
up to a vanishing normalized tail. The critical quadratic response is
2(Q_w-n U_w)/s_d. Integer powers through N vanish by signed moments;
higher integer powers have normalized density exponent (d-2j)/d<0. The
linear mode consequently vanishes, but is not asserted identically zero at
finite density. At even roots the density-log term in (A13) vanishes; the
logarithmic derivative does not. Extend (A10) above delta squared only to
compute these moments. Its difference from the actual zero-extended density
is a finite sum of powers and power/log terms bounded away from zero. Splitting
the exponential in half proves exponential smallness of each normalized tail.
This justifies the extension without changing the action or its cutoff.

## 5. Critical-order remainder with the moving endpoint retained

Here is an all-dimension estimate, including 2D–4D where differentiating the
whole moving integral too many times would create boundary terms. For one
direction put F(v,sigma)=j_d R_w(tau,r_0 omega). On 0<=sigma<=v squared,
with 0<v<=delta<=1, the displacement is comparable to v, and its sigma
derivative has norm at most 1/v. It is affine in sigma. The actual derivative
bounds (A7), Leibniz and

```math
\begin{aligned}
\partial_\sigma^i j_d&=
 \frac{(-1)^i(d-2)!}{2^{d-1}(d-2-i)!}
 v^{d-3-2i}(1-\sigma/v^2)^{d-2-i},\\
&\hspace{2em}0\le i\le d-2.
\end{aligned}
\tag{A15}
```

(the derivatives beyond d-2 are zero) prove

```math
\begin{aligned}
|\partial_\sigma^jF(v,\sigma)|&\le C_{d,w}v^{d-2j}
\quad(0\le j\le N+1).
\end{aligned}
\tag{A16}
```

For derivatives of R above three, boundedness implies the weaker required
v-to-power-(3-j) bound because v<=1. Thus (A1) supplies every derivative used.
The constants are uniform in direction and summable over the finite collar.

Define b_j by integrating the actual zero probes
partial-sigma-to-power-j F(v,0)/j! over 0<v<delta and the whole sphere,
for j=0,...,N. These probes are integrable: d-2j is at least zero. Let P be
their degree-N polynomial. Taylor's integral remainder at **fixed v**, not
formal differentiation of a moving integral, gives the exact error split

```math
\begin{aligned}
B_R(\sigma)-P(\sigma)={}&\int d\omega\int_{\sqrt\sigma}^{\delta}
 \left[F(v,\sigma)-\sum_{j=0}^N
       \frac{\partial_\sigma^jF(v,0)}{j!}\sigma^j\right]dv\\
 &-\sum_{j=0}^N\frac{\sigma^j}{j!}
   \int d\omega\int_0^{\sqrt\sigma}\partial_\sigma^jF(v,0)\,dv.
\end{aligned}
\tag{A17}
```

The second line is the entire moving-lower-end contribution. Each term is
bounded by a constant times sigma to power (d+1)/2; none was dropped. The first
line is bounded by C sigma to power N+1 times the integral of v to power
d-2N-2 from sqrt(sigma) to delta. Consequently

```math
\begin{aligned}
|B_R(\sigma)-P(\sigma)|&\le
\begin{cases}
C\sigma^{N+1/2},&d=2N,\\
C\sigma^{N+1}\left(1+\log\dfrac{\delta}{\sqrt\sigma}\right),&d=2N+1.
\end{cases}
\end{aligned}
\tag{A18}
```

The logarithm is nonnegative on this domain. Above delta squared B_R=0 and
the explicitly bounded probes bound P. Thus (B_R-P)/sigma to power q is
globally bounded on the positive half-line and tends to zero at zero. The
signed polynomial moments cancel first. Substituting
sigma=(c_d rho) to power -2/d times u then leaves a constant multiple of an
integrand dominated by u to power q times |K_d(u to power q)|, integrable by
the Mellin bounds. Dominated convergence proves the normalized remainder
vanishes. No universal positive Taylor inverse, finite even second height
moment or zero odd first height moment was used. This proves the actual short
producer, not just a power-counting proposal.

## 6. Independent target, Hessian and partition flux

Combining sections 3–5 leaves

```math
\begin{aligned}
\lim_{\rho\to\infty}S^\delta_{w,1}
 &=\frac{2(Q_w-nU_w)}{s_d}\\
 &=\int_S\frac{w(1-|p|^2)}k\,dA_S-\int_\Omega w\Delta f\\
 &=\int_S\frac{w(1-|p|^2+p\cdot g)}k\,dA_S
     +\int_\Omega\nabla w\cdot p\,dx.
\end{aligned}
\tag{A19}
```

The whole-domain divergence theorem has outward normal -g/k, not +g/k. It
applies to all components and inner boundaries. It retains a potentially
nonzero source-derivative term even when w has zero joint trace.

Here is the independent metric identification in any dimension. The joint
graph x maps to (f(x),x); on its spatial tangent plane the positive Gram
matrix is I minus p_T tensor p_T, with determinant 1-|p_T| squared. The two
future unit normals are (1,p)/sqrt(1-|p| squared) and
(1,p-g)/sqrt(1-|p-g| squared). Computing their Lorentzian inner product and
subtracting one from its square gives

```math
\begin{aligned}
A&=1-|p|^2+p\cdot g>0,\\
A^2-(1-|p|^2)(1-|p-g|^2)&=k^2(1-|p_T|^2),\\
\coth\theta\,dA_J&=\frac{1-|p|^2+p\cdot g}{k}\,dA_S.
\end{aligned}
\tag{A20}
```

The positivity follows from both slopes being below one; the right side of
the middle identity is positive by k>0 and the spacelike tangent metric.
Area is defined by these actual Gram matrices in charts. Under chart change
both Gram determinants transform by the square of the coordinate determinant,
so their positive area densities agree on every overlap. Compactness gives
finite area, a positive angle margin and integrable weight. In 2D the tangent
matrix has size zero and determinant one; S has counting measure, so (A20)
counts **all** endpoints once. This recovers #92's geometry without defining
the target from the coefficient.

For a finite spatial source partition w_i with sum one near K, sum (A5)
exactly at every density before taking limits. The source derivative terms
sum to zero, as do all artificial chart fluxes. The unweighted coefficient is
therefore precisely (A2). For arbitrary smooth spacetime source and target
partitions use the complete ordered double sum from the shared interface:
it reconstructs the unweighted overlap identically, including its point
weight, before (A7) is differentiated. Thus the sum of all its derivatives
is exactly the unweighted derivative. This proves cancellation in the total
sum, not a claim that each doubly weighted short piece has no flux. No
individual doubly weighted short-limit formula is needed or asserted here.

## 7. Actual long producer on pair space, without global envelopes

The actual long density is the shared polar/null formula with the actual
covariogram. Bounded M and fixed delta give bounded displacement support and
bounded j_d there, hence a bounded measurable compactly supported B_long.
Weighted overlaps with bounded smooth weights have the same bounds.
Nonnegative transport followed by signed Fubini proves exactly

```math
\begin{aligned}
L^\delta_{\chi,\phi}(\rho)
 &=-\beta_d\rho^{1+2/d}\int_0^\infty
 B^\ge_{\chi,\phi}(\sigma)K_d(c_d\rho\sigma^{d/2})\,d\sigma.
\end{aligned}
\tag{A21}
```

We now derive its critical jet from the geometry of actual endpoint pairs.
This replaces the global graph-envelope monotonicity used by the bounded
#78 proof; it does not assume an overlap jet or discard contacts.

**Null-active compact set and endpoint clearance.** Consider limits in
(closure M) squared of actual future-causal pairs in M, with v>=delta and
sigma tending to zero. This is a compact set of nonzero future-null pairs.
The whole straight segment of each approximating pair lies in M by ambient
interval containment; therefore the limiting segment lies in its closure.
The source cannot lie on the future face, and the target cannot lie on the
past face, including their joints. At a future face the local region lies on
the past side of a spacelike defining hypersurface. Its defining covector
has strictly positive pairing with every nonzero future causal vector, so
the segment would immediately leave the closure at a source on that face.
Reverse the direction at a target on the past face for the other exclusion.
This also excludes J because it belongs to both faces. Compactness upgrades
these exclusions to a positive distance from the forbidden endpoint strata
at the fixed cutoff. Interior height critical points are irrelevant.

All sufficiently small nonnegative-sigma long pairs lie in any fixed
neighborhood of this set, by the subsequence characterization. Choose a smooth
localization equal to one there and supported where only these strata occur:
source interior or past face, target interior or future face, never either
joint. If the active set is empty there are no sufficiently small-phase pairs
and the conclusion follows directly from the fixed positive phase gap.

**Submersion away from the cutoff.** On nonzero null pairs r_0>0, the functions
sigma=(delta_t) squared minus spatial distance squared and v=delta_t+r_0
are smooth with independent differentials. The sigma covector at either
endpoint is nonzero null. It cannot be proportional to a timelike face
conormal. Thus sigma restricts to a submersion on every one of the retained
pair-space strata, including the product of the two faces. Equivalently the
differentials of sigma and all active face defining functions are independent.
This uses actual face tangents, not genericity of a translated spatial gap.

**Cutoff contacts.** Choose delta_L>0 sufficiently small. Whenever a null pair
on past-face times future-face has v<delta_L, its two face conormals are
independent. Otherwise compactness supplies a sequence with v tending to
zero and dependent unit conormals; the endpoints converge to the same point
in the intersection J, contradicting its transverse conormals. This proves
the choice, rather than making cutoff regularity an admissibility field.
At v=delta<delta_L, the differentials of sigma, v and both active face
functions are independent: a linear combination of the first two has endpoint
components (-xi,xi); to be a combination of the two face covectors would
make xi proportional to both independent conormals, hence zero. Independence
of d(sigma),dv then finishes the argument. With zero or one active face,
the free endpoint gives the same rank conclusion without a conormal condition.
Thus all contacts at the cutoff are included, not just almost every direction.

**Finite rectification and regularity.** The submersion theorem now supplies
C-to-the-r coordinates with sigma as one coordinate and each active face
function as a separate coordinate. At cutoff patches retain v as another
coordinate. Choose a finite cover and compactly supported smooth partition
on slightly larger patches of the localized compact set. In the pulled-back
integral each actual domain is a fixed product of half-spaces for the face
coordinates and, where needed, v>=delta. The density is C-to-the-(r-1): one
derivative is spent on the absolute Jacobian. Zero extension of compact
partition supports places everything in fixed boxes. Its derivatives through
r-1 have a common integrable compact bound. Differentiation under the remaining
coordinates constructs a C-to-the-(r-1) density in sigma on a two-sided
interval about zero. It agrees with the actual right-hand pushforward, by
(A21) and uniqueness of densities, with its continuous representative.
The polar representative agrees for positive sigma near zero: its covariogram
is continuous and its bounded long integral is continuous there. Values at
zero do not affect the action and may be taken from the constructed extension.

For even d=2N, (A1) gives at least C-to-the-N, hence the degree-N Taylor
polynomial plus little-o(sigma to power N). For odd d=2N+1 it gives at least
C-to-the-(N+1), hence the degree-N polynomial plus O(sigma to power N+1),
which is little-o(sigma to power N+1/2). All coefficients are derivatives of
finite compact integrals and are finite. Combining bounded support with this
jet and the signed moment argument following (A18) proves

```math
\begin{aligned}
L^\delta_{\chi,\phi}(\rho)&\longrightarrow0
\quad\text{for every fixed }0\lt\delta\lt\delta_L.
\end{aligned}
\tag{A22}
```

This holds for bounded C-to-the-r endpoint weights, including every ordered
pair of finite smooth partition entries. Their finite sum is dominated by the
sum of the compact bounds. No null/cutoff/contact stratum is deleted to obtain
it; their moving boundaries were rectified. There is no assertion for arbitrary
large cutoffs, where parallel face conormals can obstruct this proof.

## 8. One common cutoff, complete action and separate expectation

Let delta_S be the short-geometry bound in section 3 and choose once
0<delta<min(delta_S,delta_L,1). At every positive density the strict-short and
equality-long domains partition **all** future pairs. The cutoff surface is
null for the pair volume, but equality is assigned to long even before that
fact is used. The physical point belongs to short once. The signed action
identity is therefore exact; (A19) with w=1 and (A22) prove the deterministic
part of (A3). No shrinking-cutoff interchange is needed. Any two sufficiently
small fixed choices give the same target. For arbitrary partition atlases
the exact complete ordered double sum restores the same observable before
this argument is applied.

For disconnected M, causal pairs between different connected components are
in fact absent in Minkowski space: an ambient causal segment with endpoints
in M would be a connected path entirely in M. This is a **consequence** of
containment, not a same-component modification of the selected order. All
cross-chart pairs within each component remain. Every joint component and
hole contributes its induced area in (A2).

Finally discharge the separate expectation hypotheses. Bounded open M is
Borel and has finite product Lebesgue volume. That measure is atomless; the
ambient Minkowski causal relation and closed/exclusive intervals are Borel.
Null intervals and removed endpoints have zero volume in every d>=2.
Ambient containment, a geometric input already used above, identifies the
restricted interval volume with the actual Minkowski value c_d sigma to
power d/2. The finite Poisson law with intensity rho times restricted volume
is therefore the existing dimensional instance. The genuine finite-order
layer counts are bounded by the square of the total count, whose Poisson
second moment is finite. The separate Mecke/interval-count identity gives
expectation equal to the unchanged full action at every rho>0, with its
published factorial layer coefficients. Apply that equality only now to the
proved deterministic limit. In 2D the action is dimensionless; no Planck
power with denominator d-2 is introduced. In 4D this is the previously proved
coordinate/action/law compatibility, not a redefinition of the observables.

## 9. Nonvacuity and controls (not substitutes for the quantifiers)

For every d, let 0<s<1 and take the symmetric capsule

```math
\begin{aligned}
l(x)&=-\frac s2(1-|x|^2),\qquad
f(x)=\frac s2(1-|x|^2),\qquad |x|\lt1.
\end{aligned}
\tag{A23}
```

Each face has independent slope at most s, and the strict clipped envelopes
are causal. The sphere joint is regular, the center is a retained positive
height critical point, and the future Hessian is minus s times the identity.
For s=3/4 this includes #90's witness outside every transported old combined
budget. The independently computed joint target is s_d(1+s squared)/(2s).
Completing the square in the **actual** gap in (A5), with v_n the unit spatial
ball volume, gives for every future causal displacement

```math
\begin{aligned}
V(\tau,b)&=\frac{2sv_n}{d+1}
 \left[1-\frac\tau s-\frac{|b|^2}{4}\right]_+^{(d+1)/2},\\
V_{x_1^2}(\tau,b)&=\frac{2sv_n}{(d+1)(d+3)}
 \left[1-\frac\tau s-\frac{|b|^2}{4}\right]_+^{(d+3)/2}
 +\frac{b_1^2}{4}V(\tau,b).
\end{aligned}
\tag{A24}
```

The active ball is centered at -b/2. It lies in both original unit balls:
its radius R obeys R+|b|/2<=1 whenever the gap is positive and tau>=|b|,
using s<1. Endpoint selection is therefore justified, not inferred from a
quadratic model. For w=x_1 squared the source flux is
-2s v_n/(d+1), nonzero. For w=1-|x| squared the joint trace is zero but the
source flux is 2s(d-1)v_n/(d+1), also nonzero. The signed partition
2x_1 squared and 1-2x_1 squared cancels its two fluxes only after summation.

Planar ellipsoids, the ball/sine and cosine families, annular profiles with
regular inner boundary, and finitely many spacelike-separated copies all
instantiate sections 1–2 in every dimension. Small smooth perturbations of
(A23) retain both independent slope margins and joint regularity and yield
variable angle. Their positive-height critical points need not be removed.
In 2D multiple separated intervals give every endpoint in the counting sum;
in higher dimensions annuli retain both sphere components. These are
hypothesis checks for the universal theorem, not new dimension-by-dimension
producer proofs. The original checked 2D/3D/4D and written C4 5D/6D contracts
are recovered wherever their geometric hypotheses instantiate this theorem;
none is strengthened by it.

`dimension_flat_producers.py` and `test_dimension_flat_producers.py` test the
finite Laurent algorithm against independent integration, ordinary sphere
normalization, Mellin/log responses and unequal point/pair constants, actual
moving-endpoint remainders, the steep capsule's genuine overlap and nonzero
Hessian/source flux, and finite-density ordered partition/cut allocation.
They are executable diagnostics, not an arbitrary-region theorem checker.

## 10. Exact coverage, residual ownership and verification

| Quantifier / obligation | Result of this note | Boundary |
| --- | --- | --- |
| Every integer d>=2 in Minkowski G-SS | Actual short and long producers, independent target, full deterministic and separate expectation theorem | Written, not a new Lean proof; no finite list replaces the quantifier |
| Graph/atlas presentation | Projection derived from achronality and containment; finite height and pair-space charts; no global envelope/combined budget | A global Minkowski inertial frame is used, not supplied on a general flat manifold |
| Finite regularity | Sufficient r(d) in (A1), with actual derivative counts | No all-dimensional C3 claim or assertion of optimality |
| Components, holes, endpoint counting, critical heights | Retained in (A4)–(A8), (A20), pair-space proof and exact assembly | No extra null/tip/crease strata |
| Weighted producers | Spatial source short with explicit flux; arbitrary smooth endpoint-weighted long; exact complete double-sum restoration | No unsupported individual doubly weighted short-limit formula |
| Flat quotient / nontrivial flat ambient topology | **Not proved here** | #151/#81 own actual interval-volume phase, multiple routes/cut sets and full-action remainder; zero curvature does not discharge them |
| General metric | Normalization and compatible signed interface only | #150 short, #151 nonlocal, #81 assembly; neither conditional input nor a successful flat theorem completes these |
| Verification / review | Conventional proof and symbolic/numerical controls | #86 retains a dimension-indexed formal port and independent human review; no unnecessary port is claimed |

The residual flat-manifold blocker is precise: replace the affine interval
law and pair-space submersion/clearance proof of section 7 by a theorem for
the **actual** volume phase on the selected ambient-order intervals, including
multiple null routes and cut loci, and combine it with compatible local short
producers at one fixed geometric cutoff. Compact-Cauchy flat slabs with empty
joint must be included. #151 is the existing native owner under #81; this is
not a new pilot task or an asserted obstruction to the complete action. If
“flat core” in #149 includes those manifolds, #149 remains incomplete there.
No counterexample, corrected general target, or universal G-SS completion is
asserted. #81/#24 remain open.

No Lean source, checker, dependency or build input is changed. The new
all-dimension geometric-to-analytic proof is **not** certified by the existing
conditional Lean cancellation theorem, or by Python/Markdown CI. An eventual
formal port requires the integrated source/warnings/transitive-axiom gate
after its final Lean-affecting change. Independent human mathematical and
physical review is outstanding for this written theorem, particularly the
projection and null-active pair-space arguments.

Reproduce the diagnostic and authoring checks with:

```sh
.venv/bin/python -m unittest -v test_dimension_flat_producers
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

Refs #149, #150, #151, #81, #86, #24.
