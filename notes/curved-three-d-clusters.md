# Curved 3D: audited coordinates and uniform active-cluster core bounds (#177)

**Written continuation, not the complete arbitrary-smooth theorem.** Starting
source: [PR #180 at `a500ba4`](https://github.com/q5m-ai/causal-set-emergence/tree/a500ba432e4daba64074e2f9e60922aadded8b77).
The verified integration target is `issue-81-general-coverage` at
`9e0068f91c219fe61984d20fdb3f6939eab907c4`, including the separately finalized
#176/#179 sources. Neither sibling theorem is used as a premise or edited.
[C3](curved-three-d-response.md), [F3](curved-three-d-focusing.md), the exact
[M3 ramp identity and quartic matching](curved-three-d-matching.md), and their
historical receipts are preserved. G-SS, the action, target, order, measures,
Poisson law and fixed-cutoff convention are unchanged.

The new output is an **unconditional physical bad-pair bound** near minimizing
conjugacy, uniform through vanishing quartic coefficients, flat states and
losing near-minimizers. Its actual volume exponent is 9/5, above the critical
5/3. It is not yet the missing signed whole-cluster matching on the complement.
This note records the foundation audit, the new bound, distinct further
attempts and a compatible diagnostic against a finite-branch shortcut.

## 1. Audit of M3.6: which compact inverse bounds are justified

### Compact rays, not merely compact endpoints

Fix the compact endpoint set and one positive temporal long gap. A finite
union of globally hyperbolic diamonds contains every relevant causal curve,
as in G3. On it the future null vectors normalized by d tau=1 form a compact
bundle. For an affinely parameterized ray with tangent v, initially normalized
by d tau(v)=1, put alpha=d tau(v) and w=v/alpha. Then

```math
\begin{aligned}
\frac{d\log\alpha}{d\tau}&=(\nabla^2\tau)(w,w),\\
e^{-CD}&\le\alpha\le e^{CD},&
e^{-CD}\Delta\tau&\le L\le e^{CD}\Delta\tau.
\end{aligned}\tag{CL3.1}
```

Here D is a fixed temporal range. The Hessian bound is on that compact
normalized bundle. Thus the affine lengths are bounded above and away from
zero. Initial data, lengths, positions and tangents lie in compact sets.
The achronal ray subset is closed by ODE dependence and closedness of
J+ minus I+. Compact phase-space control prevents finite-parameter escape;
geodesic completeness is not assumed.

A proper piece is unique: an alternative tangent at an interior joining
point would give chronological push-up for the original endpoints; equal
tangents give the same geodesic. It is also nonconjugate. To see the latter
precisely, a Jacobi field vanishing on a proper subinterval can be extended
by zero. Its screen index is zero. Nonnegativity of the full achronal null
index form forces its pairing with every test field to vanish. Integration
by parts leaves its derivative jump at an interior joining point. That
jump must vanish, forcing the Jacobi field to be zero by ODE uniqueness.
This uses the standard null second-variation theorem, not a test result.

**The uniform statement needs a fixed interior split margin.** Both proper
pieces then have lengths bounded away from zero. Their nonzero transverse
Jacobi factors have positive lower bounds on the compact ray/split set.
Timelike-flow transversality gives bounded endpoint inverses, and smooth
ODE dependence gives bounded derivatives of each required finite order on
smaller charts. Competing proper-piece branches cannot enter this compact
regular family: a convergent sequence would give either a second limiting
ray or contradict its local inverse. Apply the compact-control argument to
a compact neighborhood of these proper-piece endpoints for this last step.

This does not bound the full conjugate endpoint inverse or a split approaching
a tip. A finite **ray atlas** is not a finite list of paths per endpoint pair.
These distinctions fill in M3's compressed compactness argument.

### Actual clock factors and two independent controls

Use a fixed middle section. Let a parameterize its source-cone curve S(a),
and let U(a,p;x) be the broken arrival on the actual target timelike flow,
with labels p. At a stationary ray let r be the nonzero screen component of
S_a, and eta=g(v(L),T)>0 its terminal clock pairing. Let j solve the scalar
screen equation with j(0)=0,j'(0)=1, and let z solve it backwards with
z(L)=0,z'(L)=-1. Proper-piece bounds control j(m),z(m). The Wronskian and
actual clock second variation give

```math
\begin{aligned}
j'(m)z(m)-j(m)z'(m)&=j(L),\\
U_{aa}&=\frac{r^2}{\eta}\frac{j(L)}{j(m)z(m)},\\
U_{ap}v_p&=0,&
U_{aap}v_p&=\frac{r^2j'(L)}{\eta j(m)z(m)}\ne0,\\
U_{ap}e_p&=-\frac{r}{\eta z(m)}\ne0
 &&\text{at }j(L)=0.
\end{aligned}\tag{CL3.2}
```

Here v-p and e-p are projections of the terminal ray tangent and a unit
screen vector to the target flow labels. Extending the same initial ray
keeps its middle state fixed. Differentiating the Hessian along that extension
proves the third line; derivatives of its prefactors multiply j(L)=0.
For the last line the second-piece Jacobi variation has screen endpoints
zero and one, hence initial derivative 1/z(m). Differentiating junction
first variation supplies the stated clock factor. These label vectors are
independent because their span lifts to the null-orthogonal plane, which
cannot contain the timelike flow direction.

Scalar ODE uniqueness excludes simultaneous j(L)=j'(L)=0. Compactness on
the conjugate subset therefore bounds abs(j'(L)) away from zero. Thus M3.6's
matrix M is invertible with controlled inverse on smaller charts. This is
not the singular full endpoint map. No nonzero fourth derivative is used.

For an actual check, in the ultrastatic unit-sphere geometry take the source
at the north pole, the middle section at the equator and p=(X,Y) near the
south pole. The exact arrival is pi/2+acos(X*cos(a)+Y*sin(a)). At p=0 every
state is a minimum, but M has rows (sin(a),-cos(a)) and (cos(a),sin(a)), with
determinant one. Its full endpoint Jacobi factor sin(L) still vanishes at pi.
The test also varies the clock normalization rather than setting eta to one.

## 2. Endpoint weight, transported jets and clipping

The implicit equations U_a=0 and U_aa=2k give the exact identities

```math
\begin{aligned}
p_a&=M^{-1}(-2k,-6b)^T,&p_k&=M^{-1}(0,2)^T,\\
b&=U_{aaa}/6,&c&=U_{aaaa}/24,\\
\det D_{(a,k)}p&=-4k/\det M,\\
\partial_a b&=4c+U_{aaap}p_a/6,&
\partial_a c&=U_{aaaaa}/24+U_{aaaap}p_a/24,\\
d\mu_g(x)d\mu_g(y)&=
 \frac{4j_x(x)j_y(U+h,p)}{|\det M|}
 k\,dx\,da\,dk\,dh\qquad(k>0).
\end{aligned}\tag{CL3.3}
```

The derivatives of b,c are total derivatives with x,k fixed. The target
clock is U(a,p(x,a,k);x)+h; its h derivative is one. The remaining Jacobian
is block triangular, including the source block, so no clock or source
factor is missing.

**Wording repair:** the positive smooth factor in CL3.3 is the geometric
density. Signed endpoint fields and partition factors multiply it and may
vanish; their product is not asserted to have a positive lower bound. Actual
face/cutoff/closing indicators remain separate. On globally minimizing states,
a.e. ray uniqueness and the area formula give the exact physical measure
with a ray partition. Later we also use the area formula as a *counted upper
bound*, explicitly allowing several stationary preimages.

At a global minimum, positivity on a fixed state neighborhood gives
abs(b)<=C*sqrt(k). Cubic transport has error O(k+abs(b)). For a nonnegative
smooth chart cutoff psi and Lipschitz clipping,

```math
\begin{aligned}
\int_{\{|b|\lt s\}}\psi(b_a)^2\,da
 &=-\int\mathrm{clip}_s(b)(\psi b_a)'\,da\le Cs,\\
\int_{G_k}\psi c_+^2\,da&\le C\sqrt{k}.
\end{aligned}\tag{CL3.4}
```

The first two a derivatives of b are bounded on the whole smaller chart.
Level sets cause no extra term: b_a is zero almost everywhere on a fixed
level set. Enlarge s to contain the minimum band. The proof neither counts
components of G-k nor integrates along its boundary. Smooth geometric
weights and bounded fields can be dominated by a larger smooth cutoff.
An arbitrary indicator can restrict the nonnegative left side, but **must
not be differentiated as part of psi**. This audits M3.7–M3.8.

## 3. A contained physical lens and an integrated negative-defect bound

The following construction supplies the missing details behind M3.9's
transport-to-nearby-sections assertion, without assuming transported jets.
For a reference middle state a and any neighboring state a+z, start on its
source cone at an earlier central section. Follow that null generator to
the middle point and then the proper second piece to the target flow at
U(a+z,p). A small timelike advance of the earlier point changes this
constructed arrival by at most a fixed multiple of that advance. Both
connecting pieces have fixed positive length and bounded clock derivatives.

The central map (section, state, timelike advance) to physical points is
injective on a smaller ray chart, with bounded positive Jacobian. Its null
front is a regular proper-prefix cone and its third direction is timelike.
With t=U(a,p)+h and D(z)=U(a+z,p)-U(a,p), available clock width is a fixed
multiple of [h-D(z)]-positive. Shrink the chart and h range once so these
widths stay inside the fixed tubular neighborhood. Therefore

```math
\begin{aligned}
V(x,y)&\ge c_0\int_{-r_0}^{r_0}[h-D(z)]_+\,dz.
\end{aligned}\tag{CL3.5}
```

Every constructed point is causally between the physical endpoints;
ambient causal convexity puts it inside the region. The statement is true
for a stationary state which is **not** globally minimizing: negative D
increases the available width. Other routes only enlarge the actual V.
Disconnected state sublevels are allowed. Finite chart overlap costs at
most the chart count in an upper-bound argument, never a separate kernel
per route. This is a lower bound, not a formula replacing V.

At a global minimum, Taylor positivity and a bounded fourth derivative give
D<=C*(k*z^2+sqrt(k)*abs(z)^3+z^4). Taking state width a small multiple of
sqrt(h/(k+sqrt(h))) recovers M3.9's physical lower bound and its 8/5 and
fixed-positive-quartic 9/5 estimates. No tip inverse has been used.

### The stronger estimate uses the actual volume, not a fixed quartic margin

Write the stationary Taylor expansion through order five, with sixth-order
remainder bounded by M*abs(z)^6, and put q=c-positive. If V<=v, CL3.5 bounds
the integral of D-negative by C*v. Symmetry gives an upper bound for the
integral of D, hence

```math
\begin{aligned}
D(z)&=kz^2+bz^3+cz^4+dz^5+R_6(z),&|R_6(z)|&\le M|z|^6,\\
\int_{-r}^r|D(z)|\,dz&\le C(kr^3+qr^5+Mr^7+v),\\
\eta(u)&=u^3-\tfrac{11}{9}u^5,&
\int_{-1}^1u^5\eta(u)\,du&=0,&
\int_{-1}^1u^3\eta(u)\,du&=8/567,\\
|b|&\le C(k/r+qr+Mr^3+v/r^4).
\end{aligned}\tag{CL3.6}
```

Here d is a Taylor coefficient, not the spacetime dimension. The last line
follows by testing D against eta(z/r); even terms vanish and the fifth term
is annihilated. This controls losing near-minimizers without assuming their
defect is positive or dividing by their action gap.

Symmetry also shows that for each positive z, one of D(z),D(-z) is no greater
than k*z^2+q*z^4+M*z^6. Thus a measurable state set of width comparable to
sqrt(h/(k+sqrt(q*h)+h^(2/3))) has D<=h/2. CL3.5 proves, for every such active
stationary state with k>=0,

```math
\begin{aligned}
V(x,y)&\ge c\frac{h^{3/2}}{\sqrt{k+\sqrt{qh}+h^{2/3}}}.
\end{aligned}\tag{CL3.7}
```

No sixth coefficient is assumed nonzero: only a fixed smooth derivative
bound is used. This includes higher-order and infinitely flat germs.

An earlier direct positivity attempt also gives
abs(b)<=C*(sqrt(k*q)+k^(3/4)) at global minima. Test plus/minus r and 2r to
eliminate the fifth coefficient, then apply Young's inequality to obtain
D<=C*(k*z^2+q*z^4+z^6). That proves CL3.7 for global minima. The integrated
negative-part route above is genuinely stronger: it covers losing states
and arbitrarily small action gaps, including just-opening wells.

## 4. Uniform physical-phase core theorem

Define estimate scales, for v>0 and q>=0, by

```math
\begin{aligned}
qR^5+R^7&=v,&H(v,q)&=v/R,&K(v,q)&=v/R^3.
\end{aligned}\tag{CL3.8}
```

There is a unique positive R. R,H,K increase with v. These are auxiliary
scales; the physical cutoff does not move. Evaluating CL3.6 at this radius,
using an odd test annihilating the cubic moment for d and the symmetric
integral for c-negative, gives

```math
\begin{aligned}
|b|&\le C(k/R+v/R^4),\\
|d|&\le C(k/R^3+v/R^6),\\
|c|&\le C(k/R^2+v/R^5)
\qquad\text{when }V\le v.
\end{aligned}\tag{CL3.9}
```

The positive quartic part is already at most v/R^5. Constants absorb the
fixed sixth-derivative bound, not an inverse of that derivative.

Fix a sufficiently large constant B depending only on these chart bounds.
An active stationary state is **phase-bad** when h=t-U>=0 and
0<k<=B*K(V,q), using the pair's **actual V**. A physical pair is bad if it
admits such a state in one of the fixed inner ray charts. Smooth cutoffs on
larger charts dominate the inner-chart indicators. This is a fixed auxiliary
pair decomposition, not a new admissibility condition or a density-dependent
physical region.

**Core bound.** With actual bounded fields, both endpoint densities and any
physical masks retained,

```math
\begin{aligned}
|\nu_{\mathrm{bad}}|\{V\le v\}&\le C_Bv^{9/5},\\
\rho^{5/3}\int_{\mathrm{bad}}|K_3(\rho V)|\,|d\nu|
 &=O(\rho^{-2/15})\longrightarrow0,\\
N_{\mathrm{bad}}(w)&=O(w^{27/10}),&
Q_{\mathrm{bad}}(w)&=O(w^{37/10}).
\end{aligned}\tag{CL3.10}
```

Here w=(V/c3)^(2/3), exactly as in M3.1. The proof is as follows.

1. For V<=v, monotonicity gives k<=B*K(v,q). Put h=H*t in CL3.7. Since
   sqrt(q*H)<=K and H^(2/3)<=K, the lower bound divided by v grows like at
   least a constant times t^(7/6) for large t. Consequently h<=C_B*H.
2. For q<=v^(2/7), R is comparable to v^(1/7), H to v^(6/7), and K to
   v^(4/7). Direct integration of k dk dh over the fixed state/source
   charts gives O(v^2), without dividing by q.
3. In a dyadic band q comparable to u>=v^(2/7), the scales are
   R comparable to (v/u)^(1/5), H to v^(4/5)*u^(1/5), and K to
   v^(2/5)*u^(3/5). CL3.9 gives abs(b)<=C_B*v^(1/5)*u^(4/5).
4. Clip b at that last bound on the whole state chart. Cubic transport and
   CL3.4 bound the selected q-squared angular integral by the same order;
   the error (k+abs(b)) squared is smaller. The angular measure of this
   band is at most C_B*v^(1/5)*u^(-6/5). Multiplying by the actual k and h
   integrations gives C_B*v^(9/5)*u^(1/5). The dyadic sum converges uniformly
   at u=0. No fixed positive quartic margin or logarithmic loss remains.

For losing states this is first a bound on the **counted stationary-coordinate
measure**. The area formula counts all preimages; its bound dominates the
measure of pairs admitting a bad state. No finite multiplicity is assumed.
For k>0 a countable local-diffeomorphism cover suffices. The k=0 image has
zero pair measure, while every positive-k neighborhood has just been bounded.
Auxiliary selectors may be chosen measurable in the completed volume measure;
the original Borel action is unchanged. A compactness argument places all
sufficiently small-volume active rays near the compact minimizing-null ray
set; limiting a purported excluded causal ray would give another such ray.
The regular charts away from conjugacy remain part of the complement.

Dyadic volume bands control the genuine polynomial-exponential kernel in
absolute value. The positive-volume complement is exponential. This proves
CL3.10 for a sector of the *original* action, not for a substitute lens.

### What the complementary state estimate says

For v=V and s=k/K(v,q)>B, CL3.7 gives h<=C*H*s^(1/3). At screen scale
sqrt(h/k), CL3.9 bounds the normalized cubic, quartic and fifth perturbations
by C*s^(-1/3), C*s^(-2/3), and C*s^(-1), respectively; the sixth remainder
is bounded by C*s^(-7/3). Higher required derivatives have the corresponding
finite bounds. Taking B large once gives a uniform **local** Morse
neighborhood at the actual excess scale of every active good-side minimum.

This stronger definition is needed: the even-jet condition
k>sqrt(q*h)+h^(2/3) alone does not exclude a losing well's cubic barrier.
The tests exhibit that defect and show why the actual V must set the scale.
Local Morse neighborhoods do not yet give a whole-interval jet or a uniform
number of active wells.

## 5. A genuinely joint weighted contact bound

Let F be a target-face defining function evaluated at y=q(U+h,p(a,k)).
At a conjugate state and h=0, p-k points in the projected ray direction by
CL3.2, and y-k is a nonzero multiple of the null tangent. The timelike conormal
of a spacelike face therefore gives abs(F-k)>=c>0, persisting on smaller charts for small h.
Moreover y-a=(q-p+T*U-p)*p-a=O(k+abs(b)), so F-a has that bound too.

Rectify lambda=F, solving for k. At fixed lambda the cubic transport still
has form b-a=4c+O(k+abs(b)); its first two derivatives are bounded. Apply
clipping there, rather than differentiate a physical indicator. For globally
minimizing states with 0<k<=K and a target contact band I of width epsilon,

```math
\begin{aligned}
\int_{G,\ 0\lt k\le K,\ F\in I}
 q^2k\,|J\chi\phi|\,dx\,da\,dk
 &\le CK^{3/2}\min(K,\epsilon),\\
\int_{G,\ 0\lt k\le K,\ F\in I,\ F_-(x)\in I_-}
 q^2k\,|J\chi\phi|\,dx\,da\,dk
 &\le C\epsilon_-K^{3/2}\min(K,\epsilon).
\end{aligned}\tag{CL3.11}
```

These hold at fixed h, uniformly. The epsilon estimate uses dk=d lambda/F-k;
the K estimate uses fixed-k clipping. For the second line rectify the actual
source face independently in x; this change does not differentiate a or k.
Other physical masks may remain. It is **not** the false product
epsilon*K^(5/2). A compatible quartic diagnostic shows the lost K power.
For a closing mask take lambda-zero=m-plus(p)-U: changing h from zero moves
its actual indicator only in the width-h band 0<=lambda-zero<=h.

The old unweighted O(epsilon) contact bound can be justified without assuming
a translated local face is globally achronal. On the compact ray/hitting set,
the face conormal gives a nonzero hitting-time derivative. A finite implicit
function cover bounds the total hitting-map length; coarea and separation
of null and timelike conormals give the band bound. This repairs that
compressed translated-patch argument, without multiplying it by CL3.4.

Choose the single cutoff below one quarter of the compact short-locality
margin. A minimizing conjugate ray cannot lie in that local convex-normal
regime. Its smaller charts stay strictly above the cutoff. Thus the cutoff
indicator is one there; ordinary cutoff contacts remain in the regular
complement. This is a derived separation at one fixed cutoff, not a shrinking
cutoff or a deleted neighborhood. Allowed past-source/future-target contacts
remain; C3's spacelike-boundary argument supplies the forbidden-contact and
joint clearance for long pairs.

CL3.11 is a joint **positive-measure** estimate. It does not justify division
by q, singular inverse-phase weights, or a signed coefficient expansion.

## 6. Distinct attempts at the remaining whole-cluster matching

### One stiffness envelope instead of separate inverse action gaps

For D(z,k)=U(a+z,p(a,k))-U(a,p(a,k)), the exact implicit identities give

```math
\begin{aligned}
\partial_kD(z,k)&=z^2+O(|z|^3),\\
\tfrac12&\le\partial_k(D(z,k)/z^2)\le\tfrac32,\\
D(z,k)&=z^2A(x,a,z,k)[k-\gamma(x,a,z)],&\tfrac12&\le A\le\tfrac32.
\end{aligned}\tag{CL3.12}
```

The quotient extends smoothly at z=0 with value k. On a small fixed chart its
zero gamma exists smoothly with bounded derivatives. Minimization against
all states in a fixed local interval is equivalent to k>=max-z gamma.
This maximum envelope is Lipschitz and semiconvex, without counting its
maximizers. It treats close action gaps jointly and retains the real z-squared
factor rather than assuming a uniform gap derivative. Far states remain.

The envelope's second derivative need not be a smooth density. It records
minimum thresholds, not every active well width or physical overlap. No
critical expansion of Q follows merely from its semiconvexity.

### A common central generating family, without finite type

Let U(s,theta,p) be the proper-piece arrival from the source-cone point at
central affine section s. Null first variation gives U-s=g(l,v)/eta and
U-theta=g(l,J)/eta, where l is the second-piece tangent and J the source
angular variation. In a null frame write l=alpha*v+xi*e+xi^2*n/(2*alpha)
and J=j*e+beta*v. On smaller central charts alpha,j,eta are nonzero and
controlled. Then exactly

```math
\begin{aligned}
U_s&=\frac{\xi^2}{2\alpha\eta}
 =\frac{\eta}{2\alpha(-j+\beta\xi/(2\alpha))^2}(U_\theta)^2.
\end{aligned}\tag{CL3.13}
```

Integrating theta-prime equal to minus that smooth coefficient times
U-theta transports U by a smooth parameter-dependent diffeomorphism.
Critical states and their actual arrival clocks are preserved. Inverting
the positive starting-clock derivative gives the central physical thickness
as a positive part with a smooth weight. Thus central charts use one common
state potential for the whole cluster, not a kernel per well.

This transport is **not uniform at either tip**. The proper second piece
approaches the cut/conjugate endpoint map there; its actual minimizing route
can change, producing physical overlaps. F3's special resolved penalty must
not be silently promoted to a general two-tip proof. The central identity
alone does not supply that missing estimate.

### A viable fractional budget is still conditional on the missing producer

For a globally minimizing primary state put A=q+sqrt(k),
R0=sqrt(k/A), H0=k^2/A. Positivity at two radii controls the odd jets, so
D(R0*z)/H0 has uniformly bounded required derivatives and Hessian two at its
primary minimum. This gives local one-screen and central Morse expansions.
**If** the corresponding whole physical single-well inverse, including both
tips and densities, had the uniform expansion, its natural phase scale and
critical endpoint-weighted majorant would be

```math
\begin{aligned}
w_0&=k^{5/3}/A,&
kH_0w_0^{-5/2}&=k^{-7/6}A^{3/2},&
\int_{G_k}q^{3/2}\,da&\le Ck^{3/8}.
\end{aligned}\tag{CL3.14}
```

The angularly integrated majorant is at most
C*(k^(-19/24)+k^(-5/12)), integrable at zero. The first two hypothetical
coefficients are integrable as well. Dominated convergence could then restore
**both** coefficient tails across w0 comparable to w; an infinite cubic
coefficient would never be assigned a canceled value.

This is a conditional summability calculation, not the missing whole-interval
producer. A physical union's inverse is not a sum of single-well inverses.
Neither its opening coefficients nor its moving-mask remainder have been
identified by this calculation.

## 7. A compatible smooth germ defeats a remaining shortcut

Consider the **abstract**, fixed smooth generating family

```math
\begin{aligned}
U(u;X,Y)&=F(u)+X\cos u+Y\sin u,\\
F(u)&=e^{-1/u^2}\sin^2(\pi/u)\quad(u\ne0),&F(0)&=0,\\
F''(1/n)&=2\pi^2n^4e^{-n^2}>0,\\
n(a)&=(\cos a,\sin a),&t(a)&=(-\sin a,\cos a),\\
p(a,k)&=(F''(a)-2k)n(a)-F'(a)t(a),\\
\det M&=1,&\det D_{(a,k)}p&=-4k,\\
b_a&=4c+k/3,&\partial_kD(z,k)&=2(1-\cos z).
\end{aligned}\tag{CL3.15}
```

It is smooth and flat at zero, with accumulating strict wells. It satisfies
CL3.3's minimum-coordinate and transported-jet identities exactly. In addition,
its terminal covector (1,-cos(u),-sin(u)) is null for a timelike Minkowski
clock. An earlier polynomial-control attempt matched the minimum-coordinate
identities but put the terminal covectors on a parabola; that weaker algebraic
control did not establish this necessary eikonal compatibility. The circular
controls repair it. A Lorentzian **point-source** realization and complete
action are still not supplied. Extend F smoothly and nonnegatively around
the state circle, strictly positively outside this fixed small angle chart.

Choose a-star=1/n, p=-2A*n(a-star) and excess
h=2A*(1-cos(epsilon*a-star)) for a fixed 0<epsilon<1/4. Up to an additive
constant the potential is F(u)+2A*(1-cos(u-a-star)). Its sublevel cannot leave
abs(u-a-star)<epsilon*a-star. The interval contains a number of strict F
wells growing linearly with n. For each fixed n, sufficiently small positive
A preserves these finitely many wells by the implicit function theorem;
those in its inner half are active. Away from their neighborhoods F has a
positive minimum. Decrease A further so h lies below every local barrier.
The actual screen-panel volume tends to zero and every active curvature
exceeds B*K(volume,q) for any prescribed fixed B.

Thus **uniform local Morse estimates do not imply uniformly finitely many
active wells**, even for one fixed smooth germ with bounded derivatives and
these exact minimum-coordinate identities. Its action gaps can be much
smaller than its local Morse barriers. The diagnostics retain every active
sublevel component and compute the actual screen-panel integral, not merely
values at the wells. They are not a spacetime action calculation.

This defeats that shortcut, not convergence. An aggregate estimate could
still sum the wells. There is no new G-SS FAILS row, complete-action obstruction
or corrected target derived from this diagnostic.

## 8. Complete accounting and original acceptance

The materially sharper missing producer is now a **scale-uniform aggregate
physical-union ramp estimate on the phase-good active Morse clusters**,
including both tips, all action-gap openings and physical overlaps, actual
moving masks, and restoration of both legitimate subtractions. CL3.10 already
puts the phase-bad contribution beyond M3.2's critical order. It does not
supply the missing coefficients or the complementary remainder.

The original first subtraction, FCDC-3 and the complete quartic-focus result
remain unchanged. The actual short result is consumed only at C3 section 4's
discharged scope and one common fixed cutoff; no new complete assembly is
asserted. Exact A=S+L retains the point in short once, both measures, all
partners and all ordered source/target partition terms. The independent
curvature and induced curve/angle target are not fitted to a sector response.
The unchanged finite-density expectation identity remains separate and
cannot produce a new expected limit before the deterministic one.

| Original #177 item | Present output and remaining obligation |
| --- | --- |
| Arbitrary smooth metric, topology, atlas and minimizing multiplicity | M3 foundation audited without finite type; phase-core estimate includes flat and losing states. Original complete conclusion remains UNKNOWN |
| Actual interval unions and both endpoint measures | CL3.3 retains densities; CL3.5 is only a contained physical lower bound; CL3.10 evaluates the actual V and uses multiplicity only for a positive upper bound |
| Arbitrary action gaps and simultaneous contacts | Physical negative-defect control handles all gaps in the bad sector; CL3.11 is a joint weighted source/target contact bound. The signed good-cluster/mask estimate remains missing |
| Genuine critical remainder and signed moments | Bad ramp is beyond order 7/2. M3.1–M3.2 and their two genuine zeros are unchanged. No complete good-side ramp expansion or divergent-coefficient cancellation is asserted |
| Entire canonical action and independent target | Existing restricted complete results preserved; all regular/cutoff/tip complements and both subtraction restorations remain required for a new universal conclusion |
| Original-law expectation afterward | Existing finite-density bridge unchanged; no new arbitrary-metric deterministic or expected limit and no sample-wise claim |
| Adversarial scrutiny and evidence levels | Actual sphere/Jacobi/clock checks, higher/flat and accumulating compatible germs, integrated negative-defect and scale tests. Written source scrutiny and finite diagnostics are not independent acceptance |
| Residual ownership | No new complete-class WORKS or admitted FAILS row. Every missing original quantifier remains #177 under #81; #94/#86 retain final scrutiny, provenance and justified formalization |

## 9. Verification boundary

`curved_three_d_clusters.py` and its tests are finite diagnostics. They check
clock/Jacobian algebra, actual antipodal interval geometry, projection moments,
physical-scale exponents, joint-band bookkeeping and compatible accumulating
screen panels. They do not certify the general geometric inequalities or a
complete normalized action. No Lean/checker/dependency/build input changes,
new compiled theorem, independent mathematical approval or new acceptance
condition accompany this work. The PR separately records local full tests,
exact-head CI, live equation rendering and this continuation's single newly
authorized bounded feedback pass, preserving prior receipts.

Research proceeded in saved lemma checkpoints. The stopping point follows
substantive physical-volume, stiffness-envelope and central-transport attempts,
not readiness of another example note. The full goal remains **UNKNOWN**.

### Subsequent whole-union continuation

[UP3.1–UP3.17](curved-three-d-union.md) reconstruct the core/contact arguments
before consumption, derive count-free physical tip packing and a two-tip
Morse resolution, and use the actual null Hamiltonian to control the global
competing-state threshold. The aggregate opening head and critical cut-graph
budget do not yet give the required weighted half-order remainder with all
moving masks and coefficient restorations. The original conclusion remains
UNKNOWN; the preceding source and historical stopping receipt are preserved.

Refs #177, #180, #81, #24, #94, #86.
