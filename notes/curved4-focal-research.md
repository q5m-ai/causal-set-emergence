# Curved 4D continuation: a derived first coefficient and a realized quartic focus

**Written research, not a general limit theorem, a complete-action
counterexample, a Lean proof or independent human review.** This resumes
[CP5–CP8](curved4-physical-response.md) at PR #164 head `623a5bc` without
changing the physical primitive. There are two substantive advances:

1. For **every** original 4D G-SS member, geometry produces the first
   subtraction coefficient of the whole long primitive. It is not an
   admissibility assumption. The second coefficient and critical signed
   remainder are not supplied by this result.
2. The quartic degeneracy is realized in an explicit smooth curved 4D G-SS
   spacetime. Its physical interval integral and complete pair reduction are
   derived, not replaced by an optical ansatz. Its regular-side cubic inverse
   coefficients fail absolute endpoint domination. A fully matched scalar
   normal-form coefficient is identified, but its sign certification and
   transfer to the **complete physical action** remain open.

This is a materially sharper blocker than the absence of a branch-free
pushforward. The positive route fails at an actual nonintegrable higher jet,
not just an arbitrary scalar control. The negative route now has an admissible
metric and a physical lens, but not a completed obstruction. Section 7 states
exactly what remains. All earlier integrated results and the broader
#151/#81/#24 contracts are preserved.

## 1. What the original geometry adds to CP6

Fix the same temporal flow, actual measures, strict-short/equality-long
cutoff and CP5 primitive. The cutoff is positive, fixed and small enough for
S30, as discharged in CP1–CP2. For each source x, almost every spatial flow
label z whose finite arrival lies in the relevant compact time range is a
**regular null arrival**: it is reached by a unique null generator with no
conjugate endpoint. This is an almost-everywhere statement, not deletion of
normalized cut neighborhoods.

Here is the geometric justification, including both exceptional sets.

- The achronal future boundary is locally a Lipschitz graph over the chosen
  timelike flow. In a compact flow box the metric cones have a uniform opening;
  a graph with a larger local slope would contain timelike-related points.
  Thus its arrival function is locally Lipschitz wherever it is finite near
  a retained arrival. Rademacher applies in the spatial charts.
- At a differentiable graph point, the last short segment of each arriving
  null generator supplies a smooth supporting cone graph. Since the source
  precedes that short segment's initial point, this support touches from
  above. All support gradients must equal the graph gradient. Their null
  terminal directions therefore coincide; uniqueness of the backwards
  geodesic ODE makes the generator unique.
- Normalize initial null directions by the temporal covector at x. The map
  from two initial angular variables and affine length to the spatial flow
  label is smooth on its geodesic domain. A conjugate endpoint is a critical
  value of this three-dimensional map: the radial null direction projects
  transversely to the wavefront screen, so rank loss is precisely a screen
  Jacobi rank loss. Sard's theorem, on countably many parameter charts,
  makes these values spatial-volume-null. No bound on their neighborhoods
  or their number is asserted.
- There can be no earlier conjugate point on an achronal generator. At a
  unique nonconjugate endpoint, compact causal-curve control and the local
  endpoint inverse exclude an extra arrival branch nearby: otherwise a
  sequence of extra generators would limit to the unique one and contradict
  its local inverse. Consequently both cones are smooth near the interior
  of this one generator.

All these claims concern the actual ambient relation. Compactness bounds
causal auxiliary lengths and, by the geodesic ODE on that compact enclosure,
the normalized null tangent along any bounded temporal segment. It does not
provide a nondegenerate endpoint inverse on the exceptional set.

### A pointwise volume coefficient from the null index form

At a regular arrival y0, choose affine null Fermi coordinates along its
unique generator: s ranges from 0 to L, v is the conjugate null coordinate,
and Z is a parallel orthonormal two-dimensional screen coordinate. On the
line the metric is `2 ds dv - |dZ|^2`, with volume density one. Let X be the
clock vector at y0, and let eta be its positive pairing with the generator's
terminal tangent. The two cones, on a compact interior s segment, give

```math
\begin{aligned}
v_+(s,Z)&=\tfrac12 Z^T B_+(s)Z+O(|Z|^3),\\
v_-(s,Z;h)&=h\eta-\tfrac12 Z^T B_-(s)Z
                 +O(h^2+h|Z|+|Z|^3),\\
D(s)&=B_+(s)+B_-(s)>0,\\
A(x,z)&=\pi\eta^2\int_0^L\frac{ds}{\sqrt{\det D(s)}}>0.
\end{aligned}\tag{CR1}
```

The Hessians are constructed by differentiating the geodesic ODE with
endpoint variations. Their sum is the screen index form of the broken
Jacobi field with prescribed value at s and zero values at both endpoints.
That form is positive definite before the first conjugate endpoint. This
also follows by completing the index form to a square using an invertible
Jacobi matrix. Thus positivity is derived here, not a phase-inverse premise.
At the source tip D equals the identity divided by s plus a bounded matrix;
the analogous statement holds at the other tip. Its reciprocal determinant
square root is therefore of order s and L-s at the respective tips.

The actual interval is contained in any fixed tube about this generator
for sufficiently small h: otherwise compactness gives an interval point
outside the tube at h=0, contradicting uniqueness of the null interval.
Rescale Z by sqrt(h) and v by h on an interior segment. The two cone graphs,
positive index form and smooth volume density give dominated convergence.
The screen integral of the positive part of eta minus half its quadratic
form is pi times eta squared divided by the determinant square root.
Near the tips, the local normal cone and the other smooth cone bound the
screen radius squared by `C h s + C h^2`, and the v width by `C h` (with
L-s at the other end). The extra moving-tip pieces have volume of order
h to the fourth power. Each tip of affine length epsilon consequently has
volume at most `C h^2 epsilon^2 + C h^4`. First take h to zero, then epsilon
to zero. This proves the **actual**, pointwise formula

```math
\begin{aligned}
V(x,q(a_x(z)+h,z))&=A(x,z)h^2+o(h^2),\\
\frac{T_{x,z}(c_4w^2)-a_x(z)}{w}
 &\longrightarrow\sqrt{c_4/A(x,z)}
\end{aligned}\tag{CR2}
```

before a face clipping occurs. The constants in this tube argument may
blow up near a cut/conjugate contact. No uniform higher jet follows. In flat
null coordinates, D is the identity times `L/(s*(L-s))`; CR1 gives
`A=pi*eta^2*L^2/6`, agreeing with the original flat interval normalization.

## 2. A first coefficient for the whole physical primitive

Let R-delta denote the regular arrivals with
`m_minus(z) < a_x(z) < m_plus(z)` and `a_x(z)-tau(x) > delta`.
Then, for each fixed bounded smooth pair of endpoint fields,

```math
\begin{aligned}
b_1&=\sqrt{c_4}\int_M\chi(x)\,d\mu_g(x)
  \int_{\{z:(x,z)\in R_\delta\}}
  \frac{\phi(q(a_x(z),z))j(a_x(z),z)}{\sqrt{A(x,z)}}\,d\sigma(z),\\
N_{\chi,\phi}^{\delta}(w)&=b_1w+o(w),\\
\rho^{-1}L_{\chi,\phi}^{\delta}(\rho)&\longrightarrow0.
\end{aligned}\tag{CR3}
```

**Proof.** Use CP5, without differentiating its inverse. At a regular arrival
strictly inside the displayed masks, CR2 and continuity of the weighted
clock density give its divided strip limit. At a strict positive-volume
lower clock, or after the closing face, the strip is eventually empty.
The equality masks contribute no spatial measure: a smooth null graph
intersects a spacelike face or temporal level transversely; the joint
projection is lower dimensional. The nonregular arrival set is already null
by section 1. These facts give the pointwise limit for almost every (x,z).

CP6's **pointwise strip-width proof**, not merely its integrated bound,
gives a uniform bound on strip length divided by w over all retained small-
volume long fibres. Bounded j and fields and the finite actual source and
spatial measures supply the dominator. This is the important use of CP6:
it now justifies first-order averaging, including all exceptional
neighborhoods, but not third-order averaging. Measurability follows equally
from limits of the actual strip quotients, so no measurable choice of
Jacobi frames or generators is needed. Dominated convergence proves the
first two lines and absolute finiteness of b1.

For the last line use G5/CFT6 before a cubic subtraction, subtract only b1 w,
and use its zero signed moment. After dividing by rho, the scaled remainder
is bounded by a constant times `z^2*abs(K4'(z^2))` and tends to zero.
Positive-phase tails use CP6a. This is an improvement over the previous
order-rho absolute bound, **not** a finite-action limit. The physical point
and short term still occur exactly as in CP2, so the complete unit-field
action divided by rho also tends to zero. No expectation limit is inferred.

### Why the next positive step cannot be a uniform higher inverse jet

The first coefficient was not obtained by exchanging three derivatives
with endpoint integration. The following actual geometry shows why that
stronger maneuver fails. It also motivates a genuinely different route:
compute a matched fractional response instead of trying to force CP8.

## 3. An admissible metric realizing the degeneracy

Take the compact spatial three-torus with r and z periods 20 and x period pi.
Fix T=7/4 and put

```math
\begin{aligned}
Q&=\mathbb R_t\times
 (\mathbb R/20\mathbb Z)_r\times(\mathbb R/\pi\mathbb Z)_x
 \times(\mathbb R/20\mathbb Z)_z,\\
H(x)&=\tfrac14\sin^2(2x),\\
g&=dt^2-dr^2-dx^2-dz^2+H(x)(dt-dr)^2,\\
M&=(-T/2,T/2)\times\mathbb T^3,\qquad
 \mu_g(M)=400\pi T=700\pi.
\end{aligned}\tag{CR4}
```

The determinant is minus one, so **both** endpoint volume densities in
these coordinates are exactly one; this is a metric calculation, not a
probability normalization. The inverse metric pairs dt with itself as 1-H,
which is at least 3/4. The t slices are compact spacelike Cauchy surfaces.
Indeed the cone equation bounds coordinate speeds, and a causal curve with
finite limiting t has a spatial limit and extends. Thus the ambient metric
is globally hyperbolic. The open slab is precompact, and time monotonicity
separately proves containment of every ambient interval between its points.
Its frontier is precisely two smooth achronal spacelike slices, with empty
joint and no other strata. All original G-SS requirements hold.

Locally put u=t-r and v=(t+r)/2. Then

```math
\begin{aligned}
g&=2\,du\,dv+H(x)du^2-dx^2-dz^2,\\
\mathrm{Ric}_{uu}&=-\tfrac12 H''(x),\qquad R_g=0,\\
T_g&=0.
\end{aligned}\tag{CR5}
```

The Ricci sign is the repository convention. All other Ricci components
vanish. Since H-double-prime is nonzero, this is genuinely curved despite
its zero scalar curvature. The independent curvature-plus-empty-joint
target is therefore zero, without referring to an action coefficient.
No field-equation or energy-condition assumption is part of G-SS.

For a causal curve parametrized by t, the cone equation gives
`-5/3 <= dr/dt <= 1` and `abs(dz/dt) <= 2/sqrt(3)`.
For time spans below T these bounds exclude two different r or z lifts
between the same endpoints and exclude double projection of an interval.
Thus those two factors lift faithfully for the **whole** physical interval.
The x circle is not unfolded with multiplicity; all of its routes will be
retained by a variational minimum. In particular no finite branch list is
an input to the next formula.

### Exact physical interval, including every x route

For length L>0 define the actual mechanical action on paths on the x circle:

```math
\begin{aligned}
S_L(p,q)&=\inf_{\xi(0)=p,\ \xi(L)=q}
 \frac12\int_0^L\{\dot\xi(s)^2-H(\xi(s))\}\,ds,\\
x_0\preceq x_1
 &\quad\Longleftrightarrow\quad
 \Delta v\ge S_L(p,q)+\frac{b^2}{2L},\qquad L=\Delta u>0.
\end{aligned}\tag{CR6}
```

Here b is the unique lifted z displacement. The kinetic term is coercive,
the circle compact, and H bounded and smooth, so the infimum is attained.
For positive du the cone condition is exactly the displayed action
inequality; a linear added v excess realizes its converse. Segments with
du=0 can only increase v with x,z constant and do not lower that minimum.
Such endpoints form a pair-null set, not a neighborhood to discard.
The spatial winding paths in S are physical alternatives, not added volumes.

Put e=Delta v minus b squared/(2L). Intermediate v integration, then actual
z integration, gives

```math
\begin{aligned}
W(L,p,q,e)
 &=\frac43\int_0^L\sqrt{\frac{2s(L-s)}L}
   \int_{\mathbb R/\pi\mathbb Z}
   \{e-S_s(p,x)-S_{L-s}(x,q)\}_+^{3/2}\,dx\,ds.
\end{aligned}\tag{CR7}
```

This is the actual interval volume, not a geodesic sum: each intermediate
x and each allowed v,z point is counted once. The z centre is `s*b/L`;
its quadratic coefficient is `L/(2*s*(L-s))`. These give the factor 4/3
and the square root in CR7. Faithful r,z lifting and slab containment
justify using the whole intermediate domain. Every change of minimizing
x path is still inside the two functions S. This is CP4 in explicit form.

### Restore all endpoints and both time contacts before analyzing the focus

The source r,z integration has mass 400. Integration of both endpoint times
gives `T - Delta t`, not T. Since `Delta t=L/2+e+b^2/(2L)`, the complete pair
integral is

```math
\begin{aligned}
G(L,e)&=\frac43\sqrt{2L}\,(T-L/2-e)_+^{3/2},\\
P(\rho)&=400\int_{\mathbb R/\pi\mathbb Z}\!dp
 \int_0^{8T/3}\!dL\int_{\mathbb R/\pi\mathbb Z}\!dq
 \int_{S_L(p,q)}^{T-L/2}
 G(L,e)K_4(\rho W(L,p,q,e))\,de,\\
\mathcal A_{\rho,4}&=\frac4{\sqrt6}
       \{700\pi\sqrt\rho-\rho^{3/2}P(\rho)\}.
\end{aligned}\tag{CR8}
```

An e fibre with lower endpoint above upper is empty, not an oriented
integral. The bound S at least -L/8 implies that no causal slab pair has
L greater than 8T/3. All b partners are retained: the support from the time
contact is within the faithful z range. The corresponding r displacement
is also within the faithful range by the same cone bound. Thus extending
these lifted integrations to their displayed full supports neither loses
nor duplicates physical pairs.

For a fixed small temporal cutoff delta<T, write A=L/2+e. On causal pairs
A is nonnegative. The exact b-integrated short weight is zero for A at least
delta, and otherwise is

```math
\begin{aligned}
G_{\mathrm{short},\delta}(L,e)
 &=2\sqrt{2L}\left[(T-A)\sqrt{\delta-A}
                 -\tfrac13(\delta-A)^{3/2}\right],\\
G_{\mathrm{long},\delta}(L,e)&=G(L,e)-G_{\mathrm{short},\delta}(L,e).
\end{aligned}\tag{CR9}
```

The factor T in CR9 is unchanged. Using these weights in CR8 is the exact strict-short/equality-long split;
the physical point occurs only in short. The equality level is immaterial
for this continuous measured instance but is not reassigned. Fix one delta
below S30's thresholds and below pi/4. S30 then gives short action tending
to the independent value zero. Consequently any actual long obstruction
would survive in the complete action. Nothing below deletes CR8's other
pairs or presumes their response.

## 4. A quartic focal interval proved from this metric

Consider p=q=0 and L=pi. The central path is the unique global minimizer
with action zero. For a zero-winding real lift, the Poincare inequality on
[0,pi] and H(x) at most x squared give nonnegative action. Equality requires
both a sine path and H(x)=x squared almost everywhere, hence the zero path.
For winding k not zero, the action is at least
`pi*k^2/2 - pi/8`, strictly positive. Thus this is a null cut/conjugate
endpoint with a **unique minimizing generator**, not a sum over meridians.
Its screen Jacobi equation in x is the unit oscillator with zero mode sin s;
the independent z screen is regular.

The quartic control is not inferred solely from that Jacobi zero. Taylor
expansion of the actual potential gives

```math
\begin{aligned}
H(x)&=x^2-\tfrac43x^4+O(x^6),\\
\frac12\int_0^\pi(\dot\xi^2-H(\xi))\,ds
 &=\frac12\int_0^\pi(\dot\xi^2-\xi^2)\,ds
       +\frac23\int_0^\pi\xi^4\,ds+O(\|\xi\|_\infty^6),\\
C&=\frac23\int_0^\pi\sin^4s\,ds=\frac\pi4.
\end{aligned}\tag{CR10}
```

The needed small-action coercivity is global, not just formal Taylor.
The elementary cosine series and H at most 1/4 give
`x^2-H(x) >= (1/2)*min(x^4,x^2)` on the whole real line.
Decompose a zero-endpoint path as `a*sin(s)+b(s)`, with b orthogonal to sin.
The spectral gap gives quadratic action at least `3*integral b'^2/8`.
If its total action is at most a small e, it follows that
`integral min(x^4,x^2) <= 4e`, `abs(a) <= C0*e^(1/4)`, and
`abs(b(s)) <= sqrt(8e*min(s,pi-s)/3)`.
The bound on a follows by splitting the L2 norm at abs(x)=1 and applying
Cauchy–Schwarz on the smaller-amplitude part. Nonzero windings have the fixed
gap above. These estimates control the support of the **whole** physical lens.

For an interior split s, minimize with fixed intermediate x=a sin s.
On the complement of the zero mode the quadratic form is invertible;
the minimizing complement is of order a cubed, by its Euler equation and
the analytic implicit function theorem. Enforcing the intermediate value
changes the zero-mode coefficient by the same order. Hence the actual
broken action in CR7 is `C*a^4+O(a^6)`, uniformly on compact interior s
intervals. The analytic short-segment actions used here are unique: their
lengths are below pi and their second variations are positive by Poincare.
The winding gap excludes nonlocal replacements near these minimizers.

Putting this into CR7 gives

```math
\begin{aligned}
J&=\int_0^\pi\sqrt{\frac{2s(\pi-s)}\pi}\sin s\,ds,\\
B&=\int_{-1}^1(1-u^4)^{3/2}\,du
   =\tfrac12\mathrm B(1/4,5/2),\\
D&=\tfrac43 J C^{-1/4}B>0,\\
W(\pi,0,0,e)&=D e^{7/4}+o(e^{7/4}).
\end{aligned}\tag{CR11}
```

For the endpoint justification, coercivity bounds the x width by
`C e^(1/4)*sin(s) + C sqrt(e*min(s,pi-s))`. The positive v gap is at most e
because the complete broken action is nonnegative. The z width is bounded
by `C sqrt(e*min(s,pi-s))`. After division by e to power 7/4, the endpoint
integrals are bounded by a constant times epsilon to power 5/2 plus a term
tending to zero. Thus the interior limit extends to both physical tips.
This is an actual volume statement on the admitted metric, not CP11's
assumed optical law. It still concerns a single endpoint fibre and is not
by itself an action obstruction.

### The unfolding comes from endpoint parameters, not chosen coefficients

Keep p=0; write L=pi+Delta and let q be a small real target lift. On an
interior split the quadratic oscillator actions are
`(x^2/2)*cot(s)` and
`((x^2+q^2)/2)*cot(L-s)-x*q*csc(L-s)`.
At x=a sin s their leading perturbations are `-Delta*a^2/2-q*a`.
The quartic term is CR10. Weighted rescaling therefore yields the actual
family limit

```math
\begin{aligned}
\lambda^{-7/4}W(\pi+\lambda^{1/2}\alpha,0,
                    \lambda^{3/4}\beta,\lambda E)
 &\longrightarrow\frac43 J\int_{\mathbb R}
   (E-Cu^4+\tfrac12\alpha u^2+\beta u)_+^{3/2}\,du.
\end{aligned}\tag{CR12}
```

This includes both competing-well sides. A zero profile means zero limiting
volume, not a positive inverse margin. Bounds are uniform for compact
rescaled parameter sets. To justify them, rescale the path interval to
[0,pi], subtract the small affine endpoint interpolation, and use the same
spectral decomposition. Young's inequality absorbs the perturbations
`O(abs(Delta)*a^2+abs(q*a))` into the positive quartic term plus
`O(Delta^2+abs(q)^(4/3))`. The complementary quadratic form remains coercive.
Thus a is of order lambda to power one-quarter, the complementary derivative
norm of order sqrt(lambda), and the two tip bounds used in CR11 persist.
Taylor and the implicit function theorem on interior splits then prove CR12;
no full-domain derivative or geodesic multiplicity expansion was presumed.

This contact is not confined to a specially chosen source in the geometry.
At the middle split, the analytic broken-action germ has nonzero fourth
state derivative. The derivatives of its first state derivative with
respect to q and of its second state derivative with respect to L are
nonzero, as the two coefficients above show. Apply the implicit function
theorem to its first three state derivatives, with unknown state, L and q.
For every source p in a small open interval there is a nearby quartic
contact. The global minimizing property persists there: bounded-action
paths are compact, paths outside the original minimizer neighborhood have
a fixed gap, and inside it the quartic contact is a strict minimum.
Thus the exceptional geometry has a genuine source family. This statement
does not yet compute its averaged signed coefficient.

## 5. Why termwise cubic domination fails on an actual contact family

Normalize the leading quartic coefficient and introduce its **derived**
unfolding coordinates A,B; they are smooth local endpoint coordinates with
nonzero Jacobian. On the regular A-positive, B=0 side the reduced volume is

```math
\begin{aligned}
\mathcal V(E,A,0)
 &=c A^{-1/2}E^2
   \left(1-\frac{E}{4A^2}+\frac{35E^2}{128A^4}
          +O(E^3/A^6)\right),\qquad c=3\pi/8,\\
E(A,w)&=c^{-1/2}A^{1/4}w
       +\frac1{8c}A^{-3/2}w^2
       -\frac{25}{256c^{3/2}}A^{-13/4}w^3+O_A(w^4).
\end{aligned}\tag{CR13}
```

Here w=sqrt(volume) **for this normalized profile**, not a changed physical
phase. Fixed positive constants restore CR12 and c4. Derive the first line
by using the signed coordinate `v=u*sqrt(A+u^2)` in the positive-part
integral and Taylor expanding its actual inverse Jacobian. Its even terms
are `A^(-1/2)`, `-(3/2)*A^(-5/2)*v^2` and
`(35/8)*A^(-9/2)*v^4`. The three elementary beta integrals give the displayed
coefficients. Inversion gives the second line; in particular its cubic
coefficient is **not zero**.

These are also the leading regular-side coefficient asymptotics of the
physical family, up to its positive smooth coordinate and measure factors.
To justify this use CR10's analytic interior-split actions in the regular
wedge `E/A^2` small and `B/A^(3/2)` in a compact small interval. Rescale the
state by sqrt(A). The positive quadratic Hessian gives a uniform inverse on
this *rescaled regular wedge*, not through A=0. The following endpoint
calculation is needed before differentiating; CR12 alone would not suffice.

For p=q=0 and L=pi-delta, write the actual broken action as
`Q2(s,L)*x^2+Q4(s,L)*x^4+Q6(s,L)*x^6+...`. Direct variation of the oscillator
boundary problem gives

```math
\begin{aligned}
Q_2&=\frac{\sin L}{2\sin s\sin(L-s)},\\
Q_4&=d(s)+d(L-s),\qquad
 d(l)=\frac{2}{3\sin^4l}\int_0^l\sin^4t\,dt.
\end{aligned}\tag{CR13a}
```

The sixth coefficient of a segment is bounded by a constant times l near
zero and by a constant times `(pi-l)^(-7)` near pi. Indeed its direct sixth
potential term costs at most `(sin l)^(-6)`; the change of the minimizing
path is the quartic forcing squared against the oscillator Dirichlet Green
kernel. The forcing costs at most `(sin l)^(-3)` and that kernel at most
`(sin l)^(-1)`. At a short segment use the rescaled bounded-interval Green
kernel instead. These prove the stated bounds from the actual action ODE.

Near s=0, put eta=s+delta. Up to fixed constants the common volume factor
`F=sqrt(2*s*(L-s)/L)*Q2^(-1/2)` is `delta^(-1/2)*s*sqrt(eta)`.
The Morse-coordinate calculation of the volume coefficients involves F,
`F*Q4/Q2^2`, `F*Q4^2/Q2^4` and `F*Q6/Q2^3`, respectively. Their scaled
absolute bounds are

```math
\begin{aligned}
\delta^{1/2}|F|&\le C s\sqrt{s+\delta},\\
\delta^{5/2}|FQ_4/Q_2^2|&\le C s^3/(s+\delta)^{3/2},\\
\delta^{9/2}|FQ_4^2/Q_2^4|&\le C s^5/(s+\delta)^{7/2},\\
\delta^{9/2}|FQ_6/Q_2^3|&\le C\delta s^4/(s+\delta)^{7/2}.
\end{aligned}\tag{CR13b}
```

The first three have integrable bounds uniform in delta; the last tends to
zero and is bounded by a constant times sqrt(s). The other tip is identical.
On an interior segment the leading limits are exactly the quadratic/quartic
profile; the sixth-action term is lower order. Dominated convergence now
proves the needed asymptotics of the first three *volume* coefficients,
then inversion gives CR13. In a small B/A^(3/2) band the rescaled minimizing
path and Green kernel vary smoothly. The simple small eigenvalue stays a
positive multiple of A, its eigenfunction has simple zeros at the two tips,
and the remaining Dirichlet spectrum has a positive gap. The same Green
bounds, uniformly in that band and in the small source family, give CR13b
with changed constants. This proves continuity of the limiting inverse
coefficients on the band, rather than inferring it from a pointwise profile
limit. Smooth time-weight derivatives contribute only less singular powers
than the cubic inverse term.

By continuity the cubic coefficient has this nonzero sign and size on a
band `abs(B) < epsilon*A^(3/2)`, with a fixed small epsilon. Its absolute
endpoint integral contains

```math
\begin{aligned}
\int_0^{A_0} A^{-13/4}\,A^{3/2}\,dA
 &=\int_0^{A_0}A^{-7/4}\,dA=\infty.
\end{aligned}\tag{CR14}
```

The source family, both endpoint measures and G at the contact have positive
smooth densities; G(pi,0)>0 since T>pi/2. They do not remove this divergence.
Nor is it an artifact of holding the lifted null coordinate L fixed instead
of using CP5's timelike clock. Clock advance h changes both unfolding
parameters A,B by O(h), and changes the normal excess by a positive multiple
of h at the contact. In the regular rescaling `E=A^2*e`,
`B=A^(3/2)*b`, these parameter changes have extra factors A and sqrt(A),
respectively. The same inverse/Green bounds therefore make the clock-change
corrections lower order. Equivalently, the worst extra cubic-jet products
have size `A^(-11/4)`, rather than `A^(-13/4)`; the leading coefficient is
multiplied by the nonzero clock-transversality factor. The spatial label
change is nonsingular: on the null graph the derivative of the lifted r
displacement with respect to L is minus the mechanical energy minus
`1/2+b_z^2/(2*L^2)`, which is bounded away from zero. Here b-z is the original
z displacement, not the rescaled unfolding variable. Thus the CP5 clock
and actual spatial measures retain the same failure of absolute domination.
This defeats the route of integrating the regular cubic inverse jet under
an absolute coefficient majorant on this admissible metric. It does **not**
defeat every signed method, and it does not prove that the aggregate physical
primitive has a nonzero fractional term: the competing-well and regular-side
subtractions still have to be matched.

## 6. Match the normalized model before assigning a sign to a sector

This section is a **scalar normal-form calculation**, not a claim that the
entire CR8 action can be replaced by this model. Write
`P(u)=u^4+A*u^2+B*u` and let a be its global minimizer. Put
`k=A+6*a^2`. Global minimality is equivalent to k at least 4a squared,
since the translated polynomial is
`v^2*(v^2+4*a*v+k)`. The equal-minimum boundary has parameter measure zero;
its neighborhood is retained. Set a=sqrt(k)*r, with r in [-1/2,1/2].
The parameter change and actual profile are

```math
\begin{aligned}
A&=k-6a^2,\qquad B=8a^3-2ka,\\
|dA\,dB|&=2k^{3/2}\,dk\,dr,\\
f_r(E)&=\int_{\mathbb R}(E-u^2-4ru^3-u^4)_+^{3/2}\,du,\\
\mathcal V(h+P(a),A,B)&=k^{7/2}f_r(h/k^2).
\end{aligned}\tag{CR15}
```

For the **complete model** parameter region k<R, its sublevel primitive is
therefore exactly

```math
\begin{aligned}
N_R(v)&=\frac49\int_{-1/2}^{1/2}\int_0^\infty
    \min\{R^{9/2},(v/f_r(E))^{9/7}\}\,dE\,dr.
\end{aligned}\tag{CR16}
```

This includes both minima and every approach to the equal-minimum boundary.
It does not keep only a bounded rescaled sector.

Put p=9/7, c=3pi/8, and define Phi(E) as the integral of f_r(E) to power
minus p over r. Its two small-E coefficients are

```math
\begin{aligned}
a_0&=c^{-p},\\
a_1&=c^{-p}\left[-\frac p6+
 \frac12\left\{\int_0^1(1+t^2)^{-p}\,dt-1\right\}\right],\\
\Phi(E)&=a_0E^{-2p}+a_1E^{1-2p}+O(E^{2-2p}).
\end{aligned}\tag{CR17}
```

The regular minimum contributes the averaged first correction
`-p*integral(5*r^2-1/4) dr=-p/6`. The other term cannot be omitted:
at r=1/2-eta the second well has depth `4*eta+O(eta^2)` and the same
quadratic coefficient at eta=0. On its opening layer eta between 0 and E/4,
the leading volume is `c*(E^2+(E-4*eta)^2)`. Both r endpoints contribute;
putting `t=1-4*eta/E` gives exactly the second term in a1. Ordinary Morse
coordinates in these two uniformly nondegenerate wells, with their moving
opening boundary included, give the stated O remainder. Away from their
neighborhoods the zero-energy polynomial has a positive lower bound.

At infinity Phi is of order E to power -9/4, by quartic rescaling. Thus the
following ordinary, subtracted integrals converge:

```math
\begin{aligned}
I={}&\int_0^1\{\Phi(E)-a_0E^{-18/7}-a_1E^{-11/7}\}\,dE
       +\int_1^\infty\Phi(E)\,dE
       -\frac7{11}a_0-\frac74a_1.
\end{aligned}\tag{CR18}
```

This fixes the matching constant; it is not the positive integral over a
selected sector. For detail, average the actual inverse profiles over r,
writing this function as g(t). The primary wells give first coefficient
`c^(-1/2)` and regular second coefficient `-1/(12*c)`. On each opening layer
put `q=sqrt(t/c)` and `eta=q*y/4`. The divided inverse e solves
`e^2+(e-y)_+^2=1`, hence `e=(y+sqrt(2-y^2))/2` for y between zero and one.
Both layers add `(1/(2*c))*integral_0^1(e-1)dy` to the second coefficient.
Thus the complete inverse average and CR16 become

```math
\begin{aligned}
g(t)&=c^{-1/2}t^{1/2}
       +c^{-1}(\pi/16-1/3)t+O(t^{3/2}),\\
N_R(v)&=\frac47 v^{9/7}\int_{v/R^{7/2}}^\infty
                      g(t)t^{-16/7}\,dt,\\
N_R(v)&=\frac8{11}c^{-1/2}R^{11/4}\sqrt v
   +2c^{-1}(\pi/16-1/3)Rv
   +\frac49 I v^{9/7}+O_R(v^{3/2}).
\end{aligned}\tag{CR16a}
```

The same two-well Morse calculation gives the stated inverse remainder;
at infinity g has order t to power 4/7. Subtracting both small-t terms makes
the remaining integral converge at both ends. Integration by parts followed
by the monotone substitution `t=f_r(E)` identifies its constant with CR18
and the factor 4/9. Equivalently cut off at a small positive E before making
the substitution, retain both explicit boundary terms, and take its finite
part. The boundary expansions have half-integer t powers; since 9/7 is not
a half integer, none contributes a constant at the moving lower endpoint.
This is a matched **model** coefficient, without an arbitrary continuation
of a divergent integral.

Finite quadrature gives positive values near 0.6 for I; the implementation
reports the actual finite truncations and refinements. It is **not a
certified sign proof**, and no fitted value is substituted into an action.
In particular, omitting the equal-minimum correction in a1 leaves a divergent
matching expression, even though the putative sector power is unchanged.

If the physical primitive were proved to contain a nonzero matched term
`C_phys*v^(9/7)` with a controlled remainder, its canonical signed long
response would be

```math
\begin{aligned}
-\beta_4\frac97 C_{\mathrm{phys}}\,
 \Gamma(9/7)\prod_{j=1}^3\left(1-\frac{18}{7j}\right)
 \rho^{3/14}.
\end{aligned}\tag{CR19}
```

The product is positive. This is the actual volume-phase normalization,
not CP5's c4-scaled phase, and follows by convergent gamma integrals.
**C-phys has not been established for the complete metric region.** CR19
therefore remains a response calculation, not a divergence theorem.

## 7. Complete-action ledger and the materially sharper blocker

The competing routes have now been executed far enough to distinguish their
failures:

| Route | What geometry actually produced | Exact remaining failure |
| --- | --- | --- |
| CP7 signed dilation without a classical cubic jet | General CR3 constructs b1 from the original G-SS geometry, with genuine averaging domination | No universal b2 or critical dilation bound; the first-order proof cannot be differentiated twice |
| Regularity of the inverse-strip primitive | Almost-everywhere regular null tubes and a geometric leading coefficient; actual cusp CR14 defeats termwise cubic absolute domination | Cancellation across the singular endpoint layers is still uncomputed |
| Realized degenerate geometry | Explicit G-SS metric, physical interval CR7, full pair/clock weights CR8–CR9, actual quartic focus and its unfolding | Matched physical coefficient and remainder, its sign, and the full regular/other-contact complement are not proved |

The next negative-route obligations are now concrete, not “find a possible
optical model”:

1. Establish a rigorous sign enclosure for the convergent matched integral
   CR18, rather than relying on its quadrature.
2. Transfer this model coefficient through the **actual** CR7 family after
   source averaging, using a uniform subtracted estimate from the regular
   wedge through the competing-minimum transition. CR12's compact scaled
   limit alone is not such an estimate; CR14 identifies the nonintegrable
   endpoint power that must be matched.
3. Control every remaining CR8 pair: all source p, all minimizing paths in S,
   all other cut contacts, the regular nearly-null complement and closing
   time fibres. Do not presume they cancel or share the model coefficient.
   Restore the same fixed-cutoff weights in CR9, then the short limit with
   its single physical point. Only that can establish disagreement with
   the independently computed zero target.

The first step alone would still not complete the second or third. No new
no-caustics core, finite-branch admissibility assumption or density-dependent
region is introduced. The metric is selected because it realizes the
specific general blocker, not as a replacement of the original quantifier
by another standalone success example. A positive general theorem would
have to explain cancellation for this admitted family as well.

The finite-density expectation transfer is separately valid: CR4 supplies
finite atomless geometric volume, the actual ambient causal order is closed,
CR6–CR7 define Borel physical intervals with proven containment, and finite
Poisson second moments control the exclusive ordered layer counts. The
existing generic bridge thus identifies the expectation of the unchanged
observable with CR8 at each positive density. It supplies neither a limit
nor divergence until the deterministic calculation above is finished.

**Stopping status:** the general question remains unresolved. The strongest
new unconditional statements are CR3, the admissibility/physical reductions
CR4–CR9, and the realized focal behavior CR11–CR14. No corrected general
curved-4D limit theorem is claimed. #151/#81 retain the signed analysis and
complete-action decision; #81/#24 retain their broader contracts. Independent
human scrutiny and justified formalization remain final #94/#86 obligations.

## 8. Diagnostics and verification boundary

`curved4_focal_geometry.py` and its tests check the actual metric determinant,
curvature convention, causal/time weights, the physical pendulum action and
its volume integral, quartic coefficient and scaling, regular-side inverse
coefficients, parameter Jacobian, matched-model subtraction and signed
normalization. Actual-geometry and model-only routines are labeled separately.
Neither numerical agreement nor a normal-form power count certifies a
complete-action obstruction. The PR records observed local/CI/browser checks.
No Lean/checker/dependency/build input is changed and no Lean audit or new
compiled geometric theorem is claimed. No agent launch, merge, deployment,
issue closure or scope change is authorized here.

Refs #151, #81, #24, #94, #86.
