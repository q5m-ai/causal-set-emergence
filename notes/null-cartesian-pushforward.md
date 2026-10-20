# Signed Cartesian pushforward through two moving null fronts (#156)

**Written analytic continuation; not Lean-checked or independently accepted.**
This proves a critical-order **long-pair theorem**, including a geometrically
specified nonlocal term, rather than another finite-density identity. It also
handles arbitrary finite smooth-sheet selection at seams and higher contacts
on that long support. It does **not** prove the remaining complete action at
singular tips/diagonal multi-front contacts or in general intrinsic metrics.
The single original-contract crosswalk remains [required coverage §8](null-mixed-required-coverage.md#8-original-contract-reconciliation-after-the-general-front-attempt).

**Subsequent gluing continuation:** [NG](null-complete-gluing.md) audits NX2,
its signed remainder and selector trace, then proves a different two-normal
estimate and complete gluing for finite null polyhedra and the full round
bicone. [DL](null-two-dimensional-gluing.md) treats the actual two-dimensional
logarithms; [FL](null-floor-level-matching.md) handles finite-sheet strict-floor
contacts. NX13 and this note's stopping discussion remain historical steps,
not the current boundary of those now-completed cases. General moving-null
singular contacts and intrinsic physical unions still block the original
contract. The precise current crosswalk remains the one linked above.

## 1. Inputs audited and exact theorem domain

The starting head was `d3d46e74c4fd89010c98178e5df588cc7ceba970`, verified
against PR #184 and its remote branch; the unchanged target/base was
`issue-81-general-coverage` at `3ae22f792325634607be5fd518303ff25a404dda`.
[NF](regular-null-front-limit.md), [NP](null-product-focusing-obstruction.md),
[TC](null-tangency-matching.md) and [NA3](null-closure-audit.md#7-intrinsic-correction-np-rules-out-a-universal-local-jet-repair)
were read as proofs, not consumed from issue state. Their source claims and
historical receipts are preserved. The uses here are NF's actual rest-diamond
map and dimensional moments, not its strictly spacelike long inverse. NP's
complete obstruction and NA3's local-repair impossibility constrain §11; they
are not estimates for these conformal intervals.

**TC interpretation.** Its extra measure is twice the induced screen measure
on a persistent **union-type** floor/crease coincidence. The two single-sheet
one-sided traces each contribute one, and the intersection trace contributes
zero. This is not a doubled coefficient at every regular SN joint, nor a
universal zero contribution from creases. The audit corrects one directional
word in TC §4: raising the floor moves its contact **to the future**, as TC7's
unchanged derivative already shows. No coefficient or theorem hypothesis is
changed. Nothing below replaces TC1 by an assumed unit-area formula. The present calculation has a different normal
Jacobian and cannot copy TC's squared-gap estimate.

Fix an integer $`d\ge2`$, $`n=d-2`$, $`m=\lfloor d/2\rfloor+1`$, a globally
conformally Minkowski metric and $`A=\Omega^d`$ smooth positive on the compact
causal enclosure. Let $`M=F\cap P`$ be bounded, with $`F`$ a future set and
$`P`$ a past set. Thus every closed physical interval is contained in $`M`$.
Use the unchanged action, dimensional kernel and both endpoint measures.
Fix one smooth physical temporal cutoff $`\psi`$, equal to one below
$`\delta/2`$ and zero above $`\delta\gt0`$. Long has $`1-\psi`$ and **no point**.

Consider any compactly supported weighted part of long for which each actual
endpoint front has a finite local representation by smooth null sheets up to
the whole support. Finite unions/intersections of their past/future sides,
dependent normals, tangential sheet ties and arbitrary finite multiplicity
are allowed. Equivalently in the charts used below, a front is a finite
min/max of its actual smooth sheet graphs. No regularity or rank of the
sheet-selection interfaces is presumed. This includes polyhedral tips made
from such sheets, but **not** a cone apex at which its constituent sheet has
no smooth extension. An atlas covering only the regular part does not prove
uniform control on its omitted singular ends.

**Theorem NX-long.** For every such fixed weighted long part, its normalized
pair integral has the geometric limit NX9 below, with an $`o(1)`$ remainder.
This is valid in every dimension, for arbitrary fixed conformal density and
all its actual sheet-selection masks. It may have a nonzero long contribution;
no cancellation premise is added to geometry. The corresponding long action
contribution is minus $`\beta_d`$ times that limit. Contributions with one
endpoint strictly inside its front, and the fixed-positive-phase complement,
are included and vanish at this normalization.

## 2. Joint normal integration: the actual first-power gap

Use null Cartesian coordinates $`(u,v,y)=(t+x_1,t-x_1,x_\perp)`$, with
volume Jacobian $`1/2`$. Choose the null axis so that the selected sheets are
actual graphs $`u=f(v,y)`$, $`u=g(v,y)`$, and the displacement
$`v=q_v-p_v`$ is bounded below on the selected long chart. Finitely many axes
and smooth pair partitions cover the compact support: the physical gap is
$`(\Delta u+\Delta v)/2`$, not either null coordinate alone.

In dimension two there need not be one axis making both opposed sheets into
such graphs. Instead partition the base at the finitely many vertical null
segments. On each base interval each lower/upper u bound is constant, absent,
or empty; the vertical conditions are fixed base masks. If a bound is absent,
invert the physical phase in that unrestricted endpoint u coordinate. No
endpoint mask then moves with phase, and the ordinary signed moments give a
vanishing critical complement as in §8. Empty domains contribute nothing.
The remaining two-bound case is exactly NX1. This handles opposed rays without
claiming an impossible common graph axis or discarding a physical partner.

For fixed base variables $`b=(p_v,q_v,y_p,y_q)`$, set

```math
\begin{aligned}
h(b)&=g(q_v,y_q)-f(p_v,y_p)-|y_q-y_p|^2/v,\\
B(b)&=v h(b),\qquad p_u=f+x,\quad q_u=g-z,\\
x,z&\ge0,\qquad r=x+z\le h(b),\\
\sigma(p,q)&=B-vr,\qquad
\ell=\tfrac12\left(v+g-f-r\right).
\end{aligned}\tag{NX1}
```

Here $`x,z`$ are the **two endpoint normal distances in these coordinates**.
The causal domain is their real triangle, not a tangent wedge substituted
for a curved region. The interval volume is still the whole physical
$`c_d\sigma^{d/2}a(p,q)`$, where $`a`$ is NF's actual normalized diamond
integral. Every normal ratio is present: write $`x=\alpha r`$,
$`z=(1-\alpha)r`$, $`0\le\alpha\le1`$, so $`dx\,dz=r\,dr\,d\alpha`$.

Near its closing set $`B=0`$, use the **actual** phase coordinate
$`\xi=(V/c_d)^{2/d}=\sigma a^{2/d}`$. At the normal vertex define
$`H=B a_b^{2/d}`$, where $`a_b`$ is the same interval factor evaluated at
$`x=z=0`$. Positivity and compactness give
$`\partial_r\xi=-v a^{2/d}+O(\sigma)\lt0`$ on one common collar.
Thus $`r=(H-\xi)L`$ with $`L`$ smooth positive, and the exact contribution is

```math
\begin{aligned}
P_\rho^{\mathrm{close}}
 &=\int db\,E_-(p_v,y_p)E_+(q_v,y_q)
   \int_0^1d\alpha\int_0^{H_+}
   (H-\xi)b(b,\alpha,\xi)K_d(c_d\rho\xi^{d/2})\,d\xi,\\
b(b,\alpha,0)\big|_{B=0}
 &=\frac{A(p)A(q)\,W(p,q)}{4v^2a_0(p,q)^{4/d}}.
\end{aligned}\tag{NX2}
```

The smooth amplitude includes both endpoint fields, all Jacobians, pair
partitions and the original $`1-\psi(\ell)`$, collected into $`W`$ in the
second line. The factors $`E_-,E_+`$ are the actual sheet selectors (§7), not
new endpoint measures. Smooth extension across negative $`B`$ is only an
algebraic extension of the positive interval factor; the physical domain
remains $`H\gt0`$. No spacelike pair is put into the observable.

The Jacobian is **one power of $`H-\xi`$**, not TC's square: one of the two
normal directions has become the phase variable. A classical smooth density
expansion is consequently too strong. For example the saddle $`B=X^2-Y^2`$
has a logarithmic **boundary-gap** density even with a Gaussian smooth weight
(§6). The full normal-integrated pair density consequently contains
$`-\tfrac12\xi^2\log\xi`$ in four dimensions: its second derivative is that
boundary-gap density. Deleting this term would delete a critical
even-dimensional response.
This is the evidenced failure of copying TC's normal-simplex remainder.
NA1's folded single inverse is not used.

## 3. Integrate the signed kernel before estimating the contact

Put $`\epsilon=(c_d\rho)^{-2/d}`$; this is an integration scale, **not** a
moving physical cutoff. The genuine dimensional moments give

```math
\begin{aligned}
\mathcal G_{d,j}(s)&=\mathbf1_{s\gt0}\int_0^s(s-u)u^jK_d(u^{d/2})\,du,\\
\mathcal G_d&=\mathcal G_{d,0},\\
\int_0^\infty s^k\mathcal G_{d,j}(s)\,ds
 &=\frac{\int_0^\infty u^{j+k+2}K_d(u^{d/2})\,du}
 {(k+1)(k+2)}=0\quad(0\le k\le m-j-3).
\end{aligned}\tag{NX3}
```

For $`0\le j\le m-2`$, both full moments of orders $`j,j+1`$ vanish.
Consequently $`\mathcal G_{d,j}(s)`$ also equals the integral from $`s`$ to
infinity of $`(u-s)u^jK_d(u^{d/2})`$. It decays exponentially at positive
infinity, is zero at negative arguments, and is $`O(s^{j+2})`$ at zero.
Two integrations by parts prove NX3; no divergent absolute double integral
is interchanged. An empty moment range asserts no extra zero.

Taylor-expand NX2's smooth amplitude in $`\xi`$ through degree $`m-1`$.
For $`j\le m-2`$ its terms are exactly
$`\epsilon^{j+2}b_j(b)\mathcal G_{d,j}(H/\epsilon)`$.
For $`j=m-1`$, the same primitive is bounded (its limit at positive infinity
is a finite kernel moment). That term and the integral Taylor remainder
are $`O(\epsilon^{m+1})`$ after all compact base integrations. Indeed the
latter is bounded by a constant times
$`\int_0^\infty\xi^m|K_d((\xi/\epsilon)^{d/2})|d\xi`$.
After critical normalization they tend to zero, since
$`m-1-n/2`$ is one in even dimensions and one-half in odd dimensions.

Let a hat denote Fourier transform with $`\widehat G(t)=\int G(s)e^{-its}ds`$.
For every finite number of logarithmic frequency derivatives,

```math
\begin{aligned}
|(t\partial_t)^k\widehat{\mathcal G}_{d,j}(t)|
 &\le C_k |t|^{m-j-2} &&(|t|\le1),\\
|(t\partial_t)^k\widehat{\mathcal G}_{d,j}(t)|
 &\le C_k |t|^{-j-3} &&(|t|\ge1).
\end{aligned}\tag{NX4}
```

The small-frequency bound is NX3 and Taylor's integral remainder. For the
large-frequency bound, integrate by parts $`j+3`$ times on the positive
half-line; the first nonzero one-sided derivative at zero is retained.
Euler derivatives preserve the same zero behavior and exponential tail.
The resulting last derivatives are integrable, also for half-integer $`d/2`$.
Thus these are actual bounds on the signed primitive, not formal symbols.

## 4. A uniform estimate that does not differentiate higher-sheet masks

The null graph equation is $`f_v=-|\nabla_y f|^2/4`$, and likewise for $`g`$.
Most importantly, the **flat squared boundary displacement** has

```math
\begin{aligned}
B&=v(g-f)-|y_q-y_p|^2,&
\partial_{y_p}\partial_{y_q}B&=2I_n,\\
\left|\int a(b)e^{i\lambda B(b)}e_-(p_v,y_p)e_+(q_v,y_q)
                     \,dy_pdy_q\right|
 &\le C\min(1,|\lambda|^{-n/2})\|e_-\|_2\|e_+\|_2 .
\end{aligned}\tag{NX5}
```

The second statement holds for smooth compact amplitude and arbitrary bounded
measurable endpoint selectors. Here is its proof, including the needed
uniformity. Regard the integral as the pairing of an oscillatory integral
operator with two $`L^2`$ functions. For its product with its adjoint, the
phase derivative in $`y_p`$ between two $`y_q`$ values is exactly twice their
difference. Repeated integration by parts gives a kernel bounded by
$`C_N(1+|\lambda||y_q-y'_q|)^{-N}`$. Choose $`N\gt n`$ and apply the elementary
Schur integral bound. The squared operator norm is $`O(|\lambda|^{-n})`$.
For small frequency use Cauchy–Schwarz on the fixed compact supports. No
derivative of either selector occurs. The fixed $`p_v,q_v`$ parameters are
then integrated on their compact domain. In dimension two there are no
transverse variables and the bound has exponent zero.

Do **not** replace $`B`$ by the conformal phase inside this argument: its
mixed derivative need not stay invertible away from the characteristic set.
Instead put the smooth positive factor into the Fourier amplitude:

```math
\begin{aligned}
\mathcal G_{d,j}(a_b^{2/d}B/\epsilon)
 &=\frac1{2\pi}\int_{\mathbb R}
 a_b^{-2/d}\widehat{\mathcal G}_{d,j}(t/a_b^{2/d})
                       e^{itB/\epsilon}\,dt .
\end{aligned}\tag{NX6}
```

All base derivatives required in NX5 obey NX4's same frequency envelopes;
they cost only Euler derivatives and bounded derivatives of $`a_b`$.
For $`j=0`$, the integrable majorant after division by $`\epsilon^{n/2}`$
is $`C|\widehat{\mathcal G}_d(t)||t|^{-n/2}`$, with the analogous derivative
bounds for the amplitude. Its small-frequency power is zero in even
dimensions and minus one-half in odd dimensions. At infinity it is at
most $`-3-n/2`$. This proves a uniform critical bound with **no classical
pushed-density smoothness and no selector derivative bound**.

For $`j\ge1`$, split frequency at $`|t|=\epsilon`$ and one, and use NX4–NX5.
After multiplication by the extra $`\epsilon^j`$, the bound is a sum of
$`O(\epsilon^j)`$ and
$`O(\epsilon^{m-1-n/2}(1+|\log\epsilon|))`$. Both vanish. This, together
with §3's remainder, is the summable error estimate required at critical
pair order. It keeps the genuine parity-dependent moment range.

## 5. The surviving geometric measure, without a cleanliness hypothesis

Only critical zeroes of $`B`$ can survive the preceding Fourier integral.
At such a point both endpoints lie on a common null ray tangent to their
respective sheets. The $`2n`$ transverse Hessian has rank at least $`n`$,
because its mixed block is invertible. The null graph equation also gives

```math
\begin{aligned}
\left(\partial_{p_v}+\tfrac12\nabla f\cdot\partial_{y_p}\right)h
 &=-\tfrac14|\nabla_{y_p}h|^2,\\
\left(\partial_{q_v}+\tfrac12\nabla g\cdot\partial_{y_q}\right)h
 &=\tfrac14|\nabla_{y_q}h|^2.
\end{aligned}\tag{NX7}
```

Differentiating at a critical zero shows that the two generator directions
are in the full Hessian kernel. Thus its rank equals the transverse rank.
These are geometric identities, not a clean-intersection assumption.

The parameterized Morse lemma, proved by solving for a nondegenerate
$n$-dimensional critical slice and integrating its quadratic Taylor matrix,
provides finite local coordinates $`(w,z)`$ with
$`B=\kappa(w)+Q(z)`$, $`Q`$ a nondegenerate signed sum of $`n`$ squares.
The remaining smooth function $`\kappa`$ is unrestricted: it can be flat,
oscillatory, or have a positive-measure zero set. The coordinate construction
uses a finite cover of the compact critical set and bounded inverse matrices.

First take smooth selectors. Stationary phase for the exact quadratic $`Q`$
gives the leading factor
$`\pi^{n/2}|t/\epsilon|^{-n/2}
 e^{i\pi\mathrm{sig}(Q)\mathrm{sgn}(t)/4}`$ times the amplitude at $`z=0`$.
This elementary formula follows by one-dimensional Gaussian regularization
in each signed coordinate. The error tends to zero under the integrable
NX4 majorant; small frequencies are bounded by NX5 before taking a limit.
At a fixed $`\kappa\ne0`$, the remaining integrable Fourier amplitude tends
to zero by the Riemann–Lebesgue lemma. At $`\kappa=0`$ it has the explicit
constant

```math
\begin{aligned}
C_d(Q)&=\frac{\pi^{n/2}}{2\pi}
 \int_{\mathbb R}\widehat{\mathcal G}_d(t)|t|^{-n/2}
             e^{i\pi\mathrm{sig}(Q)\mathrm{sgn}(t)/4}\,dt .
\end{aligned}\tag{NX8}
```

This is absolutely convergent, real, and independent of geometry. In $`d=2`$
its value is $`\mathcal G_2(0)=0`$. Dominated convergence in $`w`$ now proves
a limit and an $`o(1)`$ remainder, even at arbitrary zero sets of $`\kappa`$.
There is no interchange of a geometric family with density.

At almost every point of a smooth function's zero set with respect to ordinary
base volume, its first and second derivatives vanish. For first derivatives,
use the implicit-function theorem at a nonzero component; for a nonzero
second derivative use one-dimensional strict convexity and Fubini on a
smaller chart. Thus the surviving measure is carried by the **rank exactly
$n$ critical null-pair set**. Higher ranks have zero measure in these
coordinates and zero critical response by the proved bound, not by their
ambient measure alone.

Near rank $`n`$, the $`y_p y_p`$ Hessian block is invertible: writing the
transverse matrix as $`[D,2I;2I,E]`$, rank $`n`$ forces
$`E=4D^{-1}`$. Hence one may take $`w=(p_v,q_v,y_q)`$, solve
$`\partial_{y_p}B=0`$ for $`y_p=Y(w)`$, and set $`\kappa(w)=B(Y(w),w)`$.
Its nonzero normal signature and determinant are those of $`D/2`$.
The induced graph maps between endpoint transverse variables have bounded
invertible derivatives on these finite charts.

Define the following **geometric** functional by these charts and a smooth
partition on their critical sets:

```math
\begin{aligned}
\mathcal C_W(F,P)
 &=\sum_{i,j,\mathrm{charts}}\int_{\{\kappa=0\}}
 \frac{C_d(Q)\,A(p)A(q)\,W(p,q)\,E_i(p)E_j(q)}
 {4v^2 a_0(p,q)^{1+2/d}\sqrt{|\det(D/2)|}}
                       \,dp_v\,dq_v\,dy_q,\\
\lim_{\rho\to\infty}\rho^{1+2/d}P_\rho^{\mathrm{long},W}
 &=c_d^{-1-2/d}\mathcal C_W(F,P).
\end{aligned}\tag{NX9}
```

The factors are sheet geometry, induced coordinate volume, the quadratic
normal Hessian of the squared boundary displacement, and the following
independently derived light-ray mean:

```math
\begin{aligned}
a_0(p,q)&=\frac{\Gamma(d)}{\Gamma(d/2)^2}
 \int_0^1[s(1-s)]^{d/2-1}A(p+s(q-p))\,ds .
\end{aligned}\tag{NX10}
```

To derive NX10, slice the unit rest diamond at fixed longitudinal null
coordinate. Integrating the other null coordinate and the transverse ball
gives the weight $`[s(1-s)]^{(d-2)/2}`$; division by its beta integral
normalizes the actual whole-diamond average. This agrees with NF's null
trace, not an assumed curvature model. In NX9 the exponent of $`a_0`$
combines the two normal Jacobians with the $`n`$-dimensional stationary
quadratic scaling. It is not a fitted coefficient.

The determinant/volume combination is the ordinary quadratic-normal
change-of-variables density. Its transformation law proves invariance under
reparameterization and refinement; the chart partition counts each physical
critical pair once. No marked-null logarithm or arbitrary auxiliary measure
enters the definition. The functional is not the original action, nor its
residual: it is computed on the geometric critical null-pair set from NX8
and NX10 before taking any action limit.

## 6. Dimension checks and a logarithm that really survives

For positive definite $`Q`$, polar coordinates and two integrations by parts
in §3 give, for $`n\gt0`$,

```math
\begin{aligned}
C_d(Q_+)&=\frac{\pi^{n/2}}{\Gamma(n/2)}
 \frac{\int_0^\infty u^{d/2}K_d(u^{d/2})\,du}
 {(n/2)(n/2+1)},\\
C_3(Q_+)&=\Gamma(5/3)/3,\qquad
C_d(Q_-)=0,\\
C_d(Q_+)&=0\quad\text{for even }d\ge4,\\
C_4(X^2-Y^2)&=-\int_0^\infty\mathcal G_4(s)\log s\,ds
 =\sqrt\pi/24.
\end{aligned}\tag{NX11}
```

The last identity follows by differentiating the **actual** Mellin product:
$`\int\mathcal G_4=0`$ and
$`\int\mathcal G_4\log s=\frac12\int u^2\log u\,K_4(u^2)du`$.
The latter is $`-\sqrt\pi/24`$. A Gaussian transverse weight for the saddle
pushes to $`K_0(|s|)`$, the modified Bessel function, with
$`K_0(s)=-\log s+O(1)`$ near zero. Thus its logarithm, not a nonexistent
classical Taylor coefficient, supplies NX11. These are local signed-contact
responses, **not complete-action counterexamples**. The saddle is realized
by actual smooth null germs, not merely an arbitrary quadratic density. In
four dimensions take both sheet formulas from
$`u=y_1^2/v+y_2^2/(v+3)`$, the lower near $`p_v=-1`$ and upper near
$`q_v=1`$. Each satisfies the null graph equation directly. At these base
values their exact boundary squared displacement is

```math
\begin{aligned}
B&=(y_{p,1}+y_{q,1})^2
       -2(y_{p,2}-y_{q,2}/2)^2 .
\end{aligned}\tag{NX11a}
```

Both germs are smooth, while their common null congruence has passed a focal
value between them in one transverse direction. Compactly supported local
normal triangles use the actual flat interval, not a tangent-phase replacement.
This supplies a geometric check of the nonzero logarithmic response. It is
not a complete bounded-region obstruction: all other pairs and the point
would have to be restored before making that claim.

## 7. Seams and higher smooth-sheet contacts: retain the selectors jointly

For a finite min/max front, partition its base into Borel active-sheet sets,
resolving ties by a fixed label order. Their indicators sum to one; the same
holds at the other endpoint. For a causal pair, future/past containment
reduces the actual domain to the lower condition at $`p`$ and upper condition
at $`q`$. Consequently **all ordered active pairs** give exactly NX2. Each
uses the same physical interval, not a componentwise interval or independently
sprinkled configuration. No pairwise truncation or independence of normals
is involved. A three-or-more-sheet selector is the complete finite Boolean
selection, not several presumed independent two-face corners.

Approximate the two base selectors separately in $`L^2`$ by bounded smooth
functions. NX5–NX6 give a uniform, critically normalized error bounded by
their $`L^2`$ errors. This is why smoothing a seam here does not silently
exchange limits without a theorem. On the rank-$`n`$ critical graphs, both
endpoint projections have bounded density: the preceding invertible graph
maps and Cauchy–Schwarz give the same $`L^2`$ continuity for NX9. Smooth
approximation therefore proves NX9 for the actual unsmoothed selectors.
Positive-measure ties are counted once; where two smooth sheets agree on
such a set their relevant derivatives agree almost everywhere. No arbitrary
trace value is inferred from an ambient measure-zero convention.

This proves the long result through **all finite smooth-sheet seam/higher
selections on its compact support**, including dependent incidences. It does
not supply a missing smooth sheet through a genuine apex, or an estimate
uniform in the distance to one. It also does not remove TC's separate short
coincidence measure.

## 8. Complements, short consumer, and what cannot yet be restored

Away from the closing set, the actual phase inverse has a fixed collar and
fixed compact base domain, including its selectors. Taylor through $`m-1`$
and the original moments give normalized error $`O(\rho^{1-2m/d})`$.
The positive-phase complement and the subtracted tails are exponentially
small. At a closing zero with nonzero gradient, ordinary phase coordinates
for smooth selectors give zero limit; the same uniform $`L^2`$ estimate
passes this to the real selectors. Thus NX9 accounts for the **whole long
part satisfying §1**, not only a selected stationary sector.

There is also an actual short consumer at a **regular distinct-ray NN joint**.
Choose a vector field tangent to its upper sheet with lower defining
covector nonzero on it. Independence of the two conormals gives this field;
compactness makes its denominator uniformly nonzero for all sufficiently
small signed displacements. This is NF's short moving-domain transport,
which needs this rank, **not** strict spacelikeness of the lower face.
Its rest-diamond expansion, matched Mellin subtraction and dimensional
remainder therefore remain valid on this smooth weighted patch. The local
coefficient is NF13's curvature density plus the actual boundary divergence.
For lower and upper null graphs $`t=f(x)`$, $`t=g(x)`$, its independently
induced screen measure is

```math
\begin{aligned}
dA_g&=\Omega^{d-2}
 \frac{1-\nabla f\cdot\nabla g}{|\nabla(f-g)|}\,dS_x .
\end{aligned}\tag{NX12}
```

The Gram determinant on $`f=g`$ gives this expression; distinct rays make it
positive. The computed divergence has exactly this coarea density. Weighted
endpoint/generator terms are retained until the complete partition sum.
Thus the regular short coefficient is derived, not an assumed NN unit weight.

**The gluing problem is not finished by these facts.** At a diagonal contact
involving both fronts and several active sheets, the short transport may not
preserve all masks. NX5 is a fixed-long-gap estimate: its normal factor
$`v^{-2}`$ and rescaled phase coordinates do not remain uniformly bounded
as both endpoints approach that diagonal. Its $`L^2`$ approximation cannot
be cited there. All ordered partition terms and their opposite cutoff bands
still restore the original integral exactly at finite density, with the point
once in short, but a critical remainder for the missing diagonal/singular
parts is still required before a whole-action limit can be asserted.

## 9. A further tip attempt: a real bound, and its precise limitation

Test the missing uniformity on the actual lower past cone of the origin and
upper future cone of the origin, with $`p_v=-a\lt0`$, $`q_v=b\gt0`$. They bound
the future/past sets outside the origin's causal cones. Intersecting with a
fixed outer diamond gives the bounded future-set/past-set intersection
$`M=\{|t|\lt|x|,\ |t|+|x|\lt T\}`$; the small collar below lies inside its
outer faces. Containment is still the actual future/past-set argument.
No complete action of this region is asserted. In a common angular
collar the exact inner sheet graphs and gap are

```math
\begin{aligned}
f&=-|y_p|^2/a,\qquad g=|y_q|^2/b,\\
B&=\frac{|b y_p+a y_q|^2}{ab},\qquad v=a+b,\\
\left|\rho^{1+2/d}P_\rho^{\mathrm{collar}}(a,b)\right|
 &\le C\frac{(ab)^{n/2}}{(a+b)^2},\\
\int_{a+b\lt r}\frac{(ab)^{n/2}}{(a+b)^2}\,da\,db
 &=\frac{r^n}{n}\,\mathrm B(1+n/2,1+n/2)\quad(n\gt0).
\end{aligned}\tag{NX13}
```

The third line is a uniform bound for the **flat constant-density** exact
normal triangle, with endpoint angular cutoffs $`|y_p|\le ca`$,
$`|y_q|\le cb`$, independent of the normal variables. The normal Jacobian is
$`1/[4(a+b)^2]`$. The transverse oscillatory kernel is an exact Fourier
kernel with mixed derivative $`2I`$, so its norm constant is independent of
$a,b$ even though each cone's curvature diverges. The endpoint $`L^2`$ norms
supply $`(ab)^{n/2}`$; NX3–NX6 give the bound. Choose one fixed
$`r_0\lt\delta/(1+c^2)`$. For $`a+b\lt r_0`$ every point of this triangle has
$`\ell\lt\delta/2`$, so the original short cutoff is identically one; no new
density-dependent temporal split is being used. Changing variables to
$`a+b`$ and $`a/(a+b)`$ proves the last line. This controls both scale-separated
and comparable endpoints of that actual characteristic collar, and is more
than formal integrability of a proposed coefficient.

It does not control the complete tip action: other normal/angular sectors,
short point cancellation, true-sheet selections meeting the tip, and a
space/time-dependent physical interval still need their own uniformly
summable estimates. In $`d=2`$ the displayed bound has a logarithmic radial
divergence; the zero of NX8 does not justify multiplying it by infinity.
Nor does a cone calculation prove uniformity for arbitrary intrinsic focal
or boundary singularities. These are exact limitations of this second,
scale-aware attempt, not claims that the missing sectors diverge.

## 10. Original-law transfer, only at the proved level

For bounded $`M`$, the selected closed order and exclusive interval relation
are Borel, geometric volume is finite and atomless, and containment supplies
the actual interval volume in NX2. Reduced two-point Mecke, the original
layer factorials and both intensity factors give the expectation of each
bounded weighted long layer combination as its deterministic long integral
at every positive density. Finite second Poisson moments justify the finite
signed sum. Applying NX9 **after its deterministic proof** transfers the
proved weighted long conclusion. This is not a whole-action expectation
limit: §8's missing deterministic pieces remain missing. No sample-wise
claim or limit/expectation interchange is used.

## 11. Strongest correction actually supported, and stopping decision

The new precise correction is **NX-long on the geometric domain in §1**:
its complete long contribution is the nonlocal geometric critical-pair
functional $`-\beta_d c_d^{-1-2/d}\mathcal C_W(F,P)`$, with a proved
summable remainder. The functional uses the actual shared null rays, normal
Hessian, endpoint densities and whole-ray mean, not the action's residual.
It includes all smooth-sheet selectors on that support. Its completion with
the regular short coefficient is a valid local assembly, not yet a theorem
for every required complete region.

NP separately remains a complete admitted divergent asymptotic, and NA3
proves that no universal additive local-finite-jet repair reproduces it.
NX does not supply NP's intrinsic focal coefficient: its globally conformal
whole-diamond map and Cartesian mixed derivative do not exist across those
physical route unions. The strongest **complete-region** corrections already
proved are still NF/TC and NP at their exact scopes. They and NX together
are not a catalogue that can be declared the original general theorem.
No density-dependent subtraction is made to the observable.

**STILL BLOCKED under the original #156/#81/#24 contract.** The smallest next
inference on the conformal branch is a critically normalized, uniformly
summable **diagonal/singular-end gluing estimate for the actual joint-normal
formula**, including its point contribution. Compact smooth-sheet long
contacts and their finite higher selectors are no longer merely NA2's
finite-density identity. Intrinsic cut/focal unions additionally require a
geometric substitute for that interval map and rank calculation. Neither
smoothness of each face nor NX13 proves these missing estimates.

**Human input is now more useful than repeating this autonomous continuation.**
The highest-value next review is a mathematical analyst's scrutiny of NX2's
physical-phase Jacobian, NX4–NX6's uniform Fourier bounds, and the passage from
smooth selectors to the rank-$`n`$ geometric measure, followed by a strategy
for the singular-end gluing. This is a recommendation to #94/#86, not a
review request or an agent launch. #177 remains unresolved and separate.
A parent scope decision cannot repair an analytic gap; retain the original
contract unless the user explicitly chooses a different task endpoint.

For clarity, an **optional, unadopted scope proposal** would be: “Resolve the
universal finite-local-target assertion negatively by NP/NA3, and establish
NX-long's regular-sheet nonlocal correction, with the remaining whole-region
singular/intrinsic assembly explicitly owned by #81.” To use that as #156's
endpoint would minimally change original item 2 from all required targets to
those computed here, item 4 from complete required actions/corrected general
theorem to this negative-plus-producer result, and item 5's stopping clause
to permit those unresolved original tasks to move to #81; item 3 would need
the corresponding ownership amendment. It would **not** meet or amend #81
or #24's corrected-general-theorem criteria. No such changes are enacted or
recommended as mathematical completion. No exhaustive classification of
individual geometries is required by the present stopping decision.
