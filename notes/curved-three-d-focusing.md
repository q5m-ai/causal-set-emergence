# Three-dimensional quartic focusing: complete action and the general blocker

**Written scoped theorem, not universal curved-3D coverage.** This continues
[C3.1–C3.9](curved-three-d-response.md) past the regular conformal-cover theorem.
We remove the flat z factor from the admitted 4D focal metric and rederive
its **3D** physical interval, pair measure, signed response and whole-action
assembly. The 4D counterexample is not inherited: the resulting 3D action
converges to its independently zero target.

All reused sources are integrated at
`d2cbbc12dbfee6376140a2137013f3d409adfdbf`:
[CR4–CR12](curved4-focal-research.md),
[the one-dimensional minimizer classification CG1–CG9](curved4-focal-globalization.md),
and [CO3–CO11's actual composition geometry](curved4-complete-action-obstruction.md).
Only the unchanged circle path-action facts and their endpoint normal form
are reused. CO's extra Gaussian transverse integration, Mellin pole, signed
kernel and certified model coefficient are **not** used. All prior files and
certificates stay byte-identical. No unmerged #175 claim is a premise.

## 1. Admitted curved geometry and exact complete observable

Let T=7/4, with r period 20 and x period pi:

```math
\begin{aligned}
Q&=\mathbb R_t\times(\mathbb R/20\mathbb Z)_r
                    \times(\mathbb R/\pi\mathbb Z)_x,\\
H(x)&=\tfrac14\sin^2(2x),&
g&=dt^2-dr^2-dx^2+H(x)(dt-dr)^2,\\
M&=(-T/2,T/2)\times\mathbb T^2,&\mu_g(M)&=20\pi T,\\
u&=t-r,&v&=(t+r)/2,\\
g&=2\,du\,dv+H(x)du^2-dx^2,&
\mathrm{Ric}_{uu}&=-H''(x)/2,\qquad R_g=0.
\end{aligned}\tag{F3.1}
```

The determinant has absolute value one: **both** endpoint densities are one.
The inverse metric gives g-inverse(dt,dt)=1-H>=3/4. Coordinate causal speeds
are bounded, so an inextendible causal curve cannot end at finite t on the
compact spatial torus; the t slices are Cauchy. The slab is nonempty,
precompact and ambient causally convex by monotone t. Its frontier is exactly
two compact smooth spacelike achronal t slices, with empty joint and no other
strata. Thus every original G-SS hypothesis is verified. The curvature
contraction above, in #90's convention, is independent of the action; the
metric is curved while its scalar and joint target are zero.

Causality bounds -5/3<=dr/dt<=1. Since all time spans are below T, distinct
r lifts cannot occur between the same physical endpoints, nor can an interval
double-project in r. The x circle is **not** unfolded with multiplicity.
For L>0 let S_L(p,q) be the infimum of
one-half the integral of (x-prime squared minus H(x)) over **all** circle
paths from p to q of duration L. Let X,Y denote the spacetime endpoints,
with circle coordinates x_X=p and x_Y=q. Integrating the causal inequality
in v, then at every intermediate (s,x), gives exactly

```math
\begin{aligned}
x_X&=p,\quad x_Y=q,\quad
 L=\Delta u,\quad e=\Delta v,\quad \tau=L/2+e,\\
X\preceq Y
 &\quad\Longleftrightarrow\quad e\ge S_L(p,q),\\
W_3(L,p,q,e)&=\int_0^L\int_{\mathbb R/\pi\mathbb Z}
        [e-S_s(p,x)-S_{L-s}(x,q)]_+\,dx\,ds,\\
P_3(\rho)&=20\int_0^{8T/3}\int_0^\pi\int_0^\pi
      \int_{S_L(p,q)}^{T-L/2}
       (T-L/2-e)K_3(\rho W_3)\,de\,dq\,dp\,dL.
\end{aligned}\tag{F3.2}
```

An upper limit below its lower limit means **empty**, not an oriented integral.
The source r integral gives 20; the integration of both endpoint times gives
T-tau, not a constant source weight. The (Delta t,Delta r) to (L,e) Jacobian
has absolute determinant one. Since H<=1/4, S_L>=-L/8, hence tau>=3L/8 and
the displayed finite L bound. The Delta-u=0 set is null for pair measure;
its entire nearly parallel neighborhood is retained in section 4.

F3.2 is the physical union: at each intermediate point the allowed v values
form one interval between the infimum past cost and supremum future clock.
Overlapping paths are not added. This is also the specialization of C3.2.
The complete action is a3*rho^(2/3)*20*pi*T minus beta3*rho^(5/3)*P3.
A fixed positive cutoff below pi/4 and S30's thresholds splits it by tau,
with equality long and the point once in short.

## 2. Actual minimizers and the dimension-three critical scaling

The variational functional defining S is identical to the x functional in
CG1–CG9; removing a decoupled flat coordinate changes none of its Euler,
Jacobi, folding or energy arguments. Their precise geometric payload is:

- In one potential cell, a minimizer has at most one turn (a zero index
  field between two interior turns gives a negative variation after rounding).
  Folding into the cell and the no-crossing exchange argument leave the
  unique favored branch except on q=-p, where the two reflected branches tie.
- Different-cell minimizers rotate without turning. Extra turns strictly
  increase the fixed-energy action; exactly the two complementary half-circle
  arcs tie at q=p+pi/2. Their terminal momenta differ.
- A minimizing conjugate endpoint cannot have a nonzero cubic variation.
  CG3's energy/flight-time calculation excludes such endpoints except the
  opposite turning endpoints at the first half period. The center has first
  conjugate length pi; the wall has none. There are no triple minima.
- With m=sin(2p)², the conjugate family has Lc=2K(m), qc=-p,
  Sc=((m-2)K(m)+2E(m))/4 and tau-c=Lc/2+Sc. Its quartic coefficient
  C=2K-prime(m)>0. The closing sources are p=plus/minus pT, where tau-c=T;
  tau-c has nonzero p derivative there. Both potential cells are included.

These are facts about the **same** circle ODE on the same finite L range,
not generic-singularity assumptions. Half lengths are below pi since
L<8T/3<2pi. Poincare bounds the half-action second variation from below;
the half actions and their local endpoint inverses are analytic. Their
middle composition has the same exact right normal form
P(u)=u⁴+A*u²+B*u plus an additive parameter function. CG5–CG6 derive the
two unfolding ranks and positive quartic coefficient. CO3's division/homotopy
construction therefore applies unchanged to this scalar function.

Writing a global minimum as a=sqrt(k)*r gives the exact parameter identities

```math
\begin{aligned}
A&=k-6a^2,&B&=8a^3-2ka,&-1/2\le r&\le1/2,\\
P(a+\sqrt k\,u)-P(a)&=k^2q_r(u),&q_r(u)&=u^2+4ru^3+u^4,\\
e-d(A,B,p)&=P(a)+k^2E,&
|dA\,dB\,de|&=2k^{7/2}\,dk\,dr\,dE,\\
W_3&=k^{5/2}f_{\sqrt k}(r,E,p),&
f_0(r,E,p)&=C(p)^{-1/4}\!\int_0^{L_c}\psi_p(s)ds
                     \int_{\mathbb R}[E-q_r(u)]_+du.
\end{aligned}\tag{F3.3}
```

The power 5/2 is **newly derived** from one screen displacement sqrt(k) and
one v interval k²; there is no extra flat screen integral. The pair exponent
7/2 is unchanged because the actual parameters are A,B,e. Thus the first
possible homogeneous cusp pole is 9/5, **above** the physical critical 5/3.
This power count alone does not prove cancellation: the E endpoints,
opening wells, physical overlaps, closing contacts and all complements still
need the bounds below. No sign from the 4D model certificate is relevant.

## 3. Uniform physical bounds through both wells and both tips

### Resolved short penalty, not a frozen optical model

Use the exact composition at a middle split l=L/2:
S_s(p,x)+S_(L-s)(x,q)=min_u(U(u)+D_s(x,u)), with D_s>=0.
Near a tip its **actual** penalty is
A_s(x,u)*(x-X_s(u))²/(2s), where X_s=p+s*V_s(u), A_s>c and V_s-prime>c.
These coefficients, after short-time rescaling, have bounded derivatives.
This follows from the unit-interval geodesic ODE and the positive half-action
endpoint inverse, not from the volume formula in 4D.

Put t=sqrt(k), alpha=sqrt(s/(s+k)), beta=sqrt(k/(s+k)) and
x=X_s(a)+t*sqrt(s*(s+k))*Z. Introducing the penalty derivative variable eta
turns the minimizing equations into
Z-alpha*V-bar(xi)=beta²*eta and
q-prime(xi)-A*alpha*V-bar-prime(xi)*eta+beta²*eta²*A_xi/2=0.
At a primary minimum their determinant is
A*alpha²*V-bar-prime(0)²+2*beta², uniformly positive including s=k=0
in the compact rescaled variables. The secondary minimum has the same
property with its uniformly positive local Hessian. This explicitly verifies
the uniform inverse used here; the unscaled long endpoint inverse is singular.

In F3.2 the resulting normalized tip volume element has factor
sqrt(s*(s+k)), **not** s*sqrt(s+k) as in 4D. It and all required local
Morse coefficients have a common integrable bound on the fixed s interval.
Away from the tips, the positive half inverses give the usual compact Morse
bounds. Reflection of a Morse coordinate eliminates odd sqrt(E) terms.
An individual open well therefore has volume
A_i(t,r)*E_i^(3/2)+B_i(t,r)*E_i^(5/2)+O(E_i^(7/2)), with A_i>c,
uniform bounded coefficients/remainders and E_i its positive excess.

### The union correction cannot be omitted

Near r=plus/minus 1/2 the second well opens at its exact depth d_r, with
absolute derivative four at the boundary. The two centers in Z are separated
by at least c*alpha, while widths are at most C*sqrt(E). They overlap only
for s<=C*k*E, at **both** tips. Integrating their possible double counting
in the exact positive-part interval, rather than summing tubes, gives

```math
\begin{aligned}
\left|W_3-\sum_{\mathrm{open\ wells}}W_{3,i}\right|
 &\le Ck^{5/2}E^{3/2}\int_0^{CkE}\sqrt{s(s+k)}\,ds
 \le Ck^{9/2}E^3.
\end{aligned}\tag{F3.4}
```

Only r in a band of width O(E) has a second open well. After the r integral,
the relative Mellin error of F3.4 is at most a constant times
k²*E^(5/2-3*Re(z)/2), with polynomial dependence on abs(z). This is strictly
better than the second-order head remainder used next. Thus even though the
union correction need not have a smooth single-fibre integer jet, it is
retained and controlled at the required **averaged** order.

For E bounded below, quartic coercivity confines the scaled states to a
bounded set after u=E^(1/4)*U. On a fixed central longitudinal interval the
nonnegative penalty realizes a contained sublens of volume at least
c*(k²E)^(5/4). The same composition and quadratic tip bounds give an upper
bound of that order. Consequently, on the entire retained physical germ,

```math
\begin{aligned}
f_t(r,E,p)&\asymp E^{5/4}\qquad(E\ge E_0).
\end{aligned}\tag{F3.5}
```

For the lower bound, take states in a fixed strict interior of the quartic
sublevel and use continuity of the positive half maps on a central s interval.
For the upper bound, the defect is nonnegative, so only this bounded quartic
sublevel participates. The short penalty restricts its image at a tip to
width C*(s*(k²E)^(1/4)+sqrt(s*k²E)); integrating its clock thickness C*k²E
on the tip layer s<=C*(k²E)^(1/2) is bounded by C*(k²E)^(9/4), hence smaller.
Outside that layer the half-map image width is bounded by C*(k²E)^(1/4).
This proves F3.5 for actual intervals, not just the principal profile.

### Closing fibres and the continued Mellin head

Before passing to minimum coordinates, straighten the **actual** closing
function F=T-L/2-e in (p,A,B,e-d) coordinates. At its focal zero set the
p derivative is nonzero, because tau-c-prime(pT) is nonzero; near p=0 the
closing function stays positive. A finite partition gives either a smooth
positive density or lambda-positive times a smooth density, with lambda a
fixed integration coordinate. The quartic polynomial and absolute energy
remain independent of the solved-for p. This retains sources just outside
the limiting closing range which enter at nonzero unfolding parameters.
It does not differentiate (T-tau-c)-positive after freezing the parameters.

For fixed k>0, let j_t be the resulting smooth density, including both
endpoint times, all coordinate Jacobians and pair cutoffs. The r-averaged
small-E Mellin integrand has the **derived** expansion

```math
\begin{aligned}
\int_{-1/2}^{1/2}j_t(r,E)f_t(r,E)^{-z}\,dr
 &=a_0(t,z)E^{-3z/2}+a_1(t,z)E^{1-3z/2}
       +O((1+|z|)^N E^{2-3\Re z/2}).
\end{aligned}\tag{F3.6}
```

The coefficients are obtained by multiplying the physical primary-well
jets and the actual density jets. The opening contribution to a1 is, at
each r-boundary, j_t(r_b,0)/4 times the integral from zero to one of
(A1+A2*(1-y)^(3/2))^(-z)-A1^(-z). This follows by the exact moving substitution
d_r=E*y. Smooth dependence of the Morse coefficients and the nonzero depth
derivative give the displayed remainder; the uniformly positive primary
term bounds the derivatives of the complex power. F3.4 contributes only a
smaller averaged remainder. No term is selected to enforce a desired zero.
The fixed lambda-positive source weight is integrated afterwards.

Subtract the two terms on 0<E<1 and restore their antiderivatives
1/(1-3z/2) and 1/(2-3z/2). F3.6 gives meromorphic continuation to Re(z)<2,
with only simple head poles at 2/3 and 4/3, and uniform polynomial vertical
bounds on closed substrips away from those poles.

## 4. The whole long integral, not only a cusp sector

Let Z-long(z) be the actual integral of W3 to power -z against F3.2's long
pair measure. C3.3 gives initial absolute convergence for 0<Re(z)<2/3.
In cusp charts the small-E radial integral after the two head subtractions
is bounded by a constant times

```math
\begin{aligned}
\int_0^{k_0} k^{7/2-5\Re z/2}\,dk&<\infty
       \quad\text{if }\Re z\lt9/5.
\end{aligned}\tag{F3.7}
```

For the **physical** E>=E0 part, use h=k²E before any model extension:
the measure is bounded by C*k^(3/2) dk dh, k<=C*sqrt(h), and F3.5 gives
W3 comparable to h^(5/4). Its h integral is bounded by the integral of
h^(5/4-5*Re(z)/4), with the same threshold 9/5. This is a genuine overlap
with the initial strip and the continued head. No spurious pole from extending
a homogeneous E tail to infinity is inserted. A fixed k annulus has just
the two regular head poles. Thus all focal pieces continue past the action's
critical line 5/3, without needing a value or sign for a residue at 9/5.

Here are the remaining pieces, which cannot be left as a remainder assertion:

1. **Unique nonconjugate tubes.** Compactness away from the classified focal
   neighborhoods bounds the endpoint inverses. Write the broken cost as its
   minimum plus X²*A_s/(s*(L-s)), with A_s smooth positive down to both tips
   in the short-time variables. Substitute X=sqrt(h*s*(L-s))*Y and use the
   one-dimensional Morse inverse. F3.2 then gives
   W3=h^(3/2)*(A+B*h+O(h²)), uniformly with all moving density factors.
   This establishes both tips, not a central-ray approximation.
2. **Ordinary two-route cuts.** The action difference is a genuine transverse
   coordinate by the distinct terminal momenta in CG1–CG2. The second tube
   opens only in an action-gap band of width O(v^(2/3)), for volume cap v.
   Rescale this gap and the causal excess by v^(2/3). The positive primary
   volume makes the inverse uniformly regular even when the second positive
   part opens. Its bounded first parameter derivative gives a v^(4/3)
   transition coefficient and O(v²) remainder after gap integration.
   The physical tip overlap is O(h³); dividing by the primary volume
   derivative O(h^(1/2)) and integrating the O(h) gap band gives a primitive
   correction O(h^(7/2)), smaller than v². Both source and target overlaps
   are retained.
3. **Ordinary closing and cutoff contacts.** On the internal seam tau has
   positive L derivative; at the two rotation closing points it has nonzero
   L derivative (CG8). These are tangent to the seam and straighten closing
   without destroying its action-difference coordinate. On a regular branch,
   the clock derivatives in (L,q) are (1/2-energy, terminal velocity); they
   cannot both vanish, since zero terminal velocity implies energy<=1/8.
   The small temporal cutoff meets no seam and has the same rank property.
   Retain the resulting fixed closing weight before taking jets.
4. **Nearly parallel Delta-u=0 collar.** For small L, the unique nearby lift
   has action (q-p)²/(2L)+L*A(L²,p,q), smooth by the unit-interval ODE; other
   lifts have a diverging kinetic gap. With s=L*t, multiply the broken cost
   by 2*L*t*(1-t); it has a uniformly positive Morse quadratic down to
   t=0,1. Put z0=L*(e-S_L). The same physical integration gives
   W3=z0^(3/2)*B(L,p,q,z0), with smooth positive B and
   B(0,p,p,0)=pi*sqrt(2)/6. In the original target clock the derivative of
   z0 at the long null arrival is tau+O(L), uniformly: differentiating the
   displayed action gives S_L+L*partial_L(S_L)=O(L). Since tau>=delta,
   choose the fixed collar small enough that this derivative is at least
   delta/2. Thus this entire collar has the same uniform inverse expansion.
5. **Everything outside the null cover.** Continuity, compactness and a
   finite partition give a positive actual volume floor, hence an entire
   Mellin transform on that piece and exponential signed response.

Items 1–4 produce the actual averaged volume primitive
b1*v^(2/3)+b2*v^(4/3)+O(v²). Its Stieltjes transform continues below Re(z)=2
with only the same two simple poles. All endpoint/source/pair partitions
sum to one before using the slab symmetry; no matching-label restriction is
introduced. Their finite sums preserve the bounds. Thus the **whole**
Z-long continues to Re(z)<9/5, with only simple poles at 2/3 and 4/3 before
that line, and polynomial vertical growth on compact strips away from poles.

## 5. Complete deterministic conclusion, then original expectation

Use the genuine C3.1 Mellin transform. Its zeros cancel **both** possible
regular poles. Mellin inversion on an initial line 0<c<2/3 and a contour
shift to Re(z)=7/4, with gamma decay and the bounds above, gives

```math
\begin{aligned}
P_{\mathrm{long},3}(\rho)
 &=\frac1{2\pi i}\int_{\Re z=c}\widehat K_3(z)\rho^{-z}
                              Z_{\mathrm{long}}(z)\,dz
   =O(\rho^{-7/4}),\\
L^\delta_3(\rho)&=O(\rho^{-1/12})\longrightarrow0,\\
\mathcal A_{\rho,3}(M,g)&\longrightarrow0
       =\tfrac12\int_M R_g\,d\mu_g+\int_J\coth\theta\,dA_g.
\end{aligned}\tag{F3.8}
```

These fixed-geometry, fixed-cutoff estimates are consequences of the proof,
not a claim of a general or shrinking-cutoff rate. C3 section 4 discharges
S30 here: the metric is smooth on a compact causal enclosure, faces are
spacelike compact slices, the joint is empty, and the cutoff is below the
finite locality/root/shell margins. S30's short action tends to zero; its
point cancels exactly once. No short piece can be discarded just because
the independent scalar is zero. F3.8 adds the entire long response, with
ordinary cuts, parallel directions, closures and positive-volume complement.

**Only now** use C3 section 5's actual Borel order, finite atomless volume,
contained exclusive intervals and finite Poisson-moment argument. The original
law's expectation equals this complete action for each positive density and
therefore tends to zero. This is not a sample-wise assertion. The 4D geometry
with the additional flat direction still has its unchanged complete-action
failure: the critical exponents are different.

## 6. What the continuation resolves, and the materially sharper blocker

The attempted cubic-primitive route genuinely fails here but convergence
still holds. In the primary wedge put h=k²E; then W3 is comparable to
h^(3/2)*k^(-1/2), so the phase scale is k^(5/3). The actual endpoint measure
is k^(3/2) dk dh. Formal inverse coefficients at primitive orders one, two,
three scale as k^(2-5i/3). With the endpoint measure their powers are
11/6, 1/6 and **-3/2**. The third is nonintegrable. It is not just a loose upper bound: at r=0 the
model profile is (4/3)*E^(3/2)-(2/5)*E^(5/2)+(1/2)*E^(7/2)+higher terms.
Writing U=(3/4)^(2/3)*f^(2/3), its inverse is
E=U+U²/5-4*U³/25+higher terms. The cubic coefficient is nonzero on an
open r neighborhood; the actual rescaled Morse coefficients converge to these
ones on that primary wedge. Smooth endpoint-density corrections carry extra
powers of k and cannot remove this absolute cubic divergence. But the required 3D
critical order is only 5/2: its power is **-2/3**, which is integrable.
The moving opening terms and overlap estimate above justify using this margin;
a fixed-r Taylor expansion by itself would not. This is why copying a 4D
cubic-jet requirement would falsely reject this admitted 3D success.

What remains for the **original arbitrary smooth curved-3D class** is now
precise. C3.2–C3.4 give the real union primitive, a uniform first-order strip
bound and the first coefficient without finite branch assumptions. To reach
the action scale one still needs the second subtraction and a signed or
summably dominated 5/2-order remainder **through all minimizing degeneracies
and their moving contacts**. This proof obtains it from this metric's actual
finite classification and analytic quartic normal form. G-SS alone supplies
neither that classification, a finite-type normal form, nor uniform bounds
for the second coefficient near arbitrary smooth caustics. Smoothness is not
analyticity; compactness bounds a fixed number of derivatives of the metric,
not inverses of a degenerating endpoint map. The a.e. regular-ray argument
cannot estimate those neighborhoods at order 5/2.

Substantive attempts here therefore separate three routes:

- Local curvature/normal-coordinate expansions do not control fixed-gap
  long intervals; C3.2 retains those intervals instead.
- Absolute cubic inverse-jet domination fails even on this explicit admitted
  metric. It is a proof-route failure, **not** a counterexample; F3.8 proves
  its complete normalized action actually succeeds.
- Matching with the true 3D exponents resolves this entire quartic test,
  including both route wells, overlaps and closing contacts. Extending its
  finite analytic classification to every smooth metric remains an unproved
  geometric implication, not merely an unperformed formal port.

This is the stopping boundary: the universal conclusion is still **UNKNOWN**,
not silently replaced by FCDC-3 or F3.1. **#177 owns all those missing original
quantifiers**, under #81. No new sub-issue is needed to hide them. A new failure
claim would need the entire matched canonical action of a fixed admitted
member, with independent target and all complements; no such 3D failure is
proved here. No no-caustics/genericity/finite-type condition is added to G-SS.

## 7. Evidence levels

The accompanying tests calculate actual focal intervals by the circle
boundary-value action, separately compare their first coefficient and
quarter-power scaling, test all wells of the **3D** polynomial profile,
normalization, moving opening and union overlap, and exact time/cutoff/ordered
partition restoration. The conformal diagnostics use independent interior
and endpoint domains and independently calculated curvature/joint targets.
These are finite numerical/symbolic checks, not a proof of the Mellin
continuation or a complete-action numerical validation of the focal slab.

No new Lean result or arithmetic sign certificate is claimed. The generic
bridge and earlier flat results retain their compiled scopes; neither checks
these new geometric arguments. Written proof, diagnostics, CI and independent
review are distinct. Attributable human mathematical/physical scrutiny,
provenance and justified formalization remain #94/#86.

Refs #177, #81, #24, #150, #94, #86.
