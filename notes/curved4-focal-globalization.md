# The physical source family and all minimizing contacts of the focal metric

This is a continuation of [CR4–CR19](curved4-focal-research.md), under
#151/#81. It preserves the original G-SS class, physical interval CR7,
complete pair measure CR8, canonical kernel and independent target zero.
It does **not** turn the [matched model certificate](curved4-focal-certificate.md)
into a physical-action coefficient.

The results here are a classification of this metric's minimizing contacts
and explicit physical source-family data. Section 5 isolates the uniform
subtracted transfer obligation, not an assumption added to G-SS. The
[complete-action sequel](curved4-complete-action-obstruction.md) proves its
source-integrated form, the regular complement and restoration. Classification
or a positive model certificate alone would not prove that conclusion.
These are written arguments, not Lean proofs or independent human acceptance.

## 1. Classify minima before summing any tubes

Write the mechanical energy as H-calligraphic to distinguish it from the
normal-form excess E. Along a stationary curve,

```math
\begin{aligned}
\mathcal H&=\tfrac12\dot x^2+\tfrac18\sin^2(2x),\qquad
 \ddot x=-\tfrac14\sin(4x),\\
P(\mathcal H)&=2K(8\mathcal H),\qquad
 F_{\mathcal H}(x)=\int_0^x\frac{dy}{\sqrt{2\mathcal H-H(y)}}.
\end{aligned}\tag{CG1}
```

Here K uses the elliptic **parameter** convention:
`K(m)=integral_0^(pi/2) (1-m*sin(theta)^2)^(-1/2) dtheta`.
P is the **half** period of an oscillating path, also the period of H along it.
Its first two energy derivatives are positive, by differentiating the
positive integral for K. The signed incomplete time F is used only when
the integration interval lies below the turning amplitude.

The two potential cells have endpoints at the maxima of H, with centers
0 and pi/2 on the x circle. For endpoints in one closed cell, folding any
path into that cell by reflections preserves its action. An interior
crossing of a cell wall would fold a nonzero velocity into a corner; rounding
that corner strictly lowers the action. Reaching the wall with zero velocity
would, by ODE uniqueness, give the constant wall path. Thus a nonconstant
minimizer with endpoints in one cell does not leave it.

A minimizer cannot have two interior turning points. Its time-translation
Jacobi field, namely its velocity, vanishes at consecutive turns. Restrict
this field between those turns and extend it by zero. Its index form is zero,
but its derivative has jumps at the two interior joins. If the full index
form were nonnegative, polarization would make this zero vector orthogonal
to every variation, contradicting those nonzero jumps. Thus the full path
would have a negative direction. The same argument excludes a turning point
at one endpoint and another in the interior. Constant paths are treated
separately.

For an upper-turn path of energy H-calligraphic, its time is
`P-F(p)-F(q)`. For a lower-turn path it is `P+F(p)+F(q)`. If p+q is
nonnegative, the signed sum F(p)+F(q) is a sum or difference reducing to
positive integrals with fixed endpoints. Its first energy derivative is
negative and its second positive. Consequently the upper-turn time is
strictly increasing in energy; the lower-turn time has strictly positive
second energy derivative. The statements reverse when p+q is negative.
A monotone path, when it exists, is unique, since its flight time strictly
decreases with energy.

After reflection and time reversal arrange `p>=abs(q)`. Put
`H0=H(p)/2` and `L0=F_H0(p)-F_H0(q)`. The monotone branch exists for
L at most L0, and the upper-turn branch for L above L0. A lower-turn path
has time at least P(H0), which is at least L0. Its branch with negative
energy derivative has already passed a conjugate point and is not a local
minimum. Strict convexity of its time map leaves at most one other local
minimum. Thus at most two global minima can occur; no finite branch bound
was assumed.

To decide the actual equality set, recall the no-crossing argument. Two
minimizers in a real cell cannot cross twice: exchanging their middle
pieces would produce corners unless their velocities agree, in which case
ODE uniqueness identifies them. If p+q is positive, compare a putative
lower-turn minimizer with its reflected time reverse. The latter is a
minimizer with both endpoints strictly lower. No crossing forces the first
path to have positive midpoint value. But the midpoint of a lower-turn path
is strictly negative: its phase displacement from the lower turn is half
the difference of the two incomplete endpoint times, of absolute value less
than one quarter of the full period. This is a contradiction. Therefore
the lower-turn branch cannot minimize: the unique monotone or upper-turn
branch remains. Reflection gives the other sign.

For q=-p the two turn branches are reflected time reverses and have equal
action. They exist precisely after the half period at turning amplitude
abs(p). Before it the monotone path is the unique minimum; at it the two
branches meet in one path. Existence of a global minimizer and the exclusions
above prove these are global statements, not just a stationary-path list.
For the exceptional center endpoints p=q=0, Poincare and `H(x)<=x*x`
make the constant path uniquely minimizing up to L=pi, including equality
by the strict quartic term. Beyond pi it has a negative second variation,
and the two reflected turn paths are the minima. The wall constant path is
treated below.

### Endpoints in different cells

Every such path crosses a maximum of H. A minimizing stationary path then
has energy strictly greater than 1/8 and never turns. For an oriented arc C,

```math
\begin{aligned}
S_L(C)&=\sup_{\mathcal H>1/8}
 \left\{\int_C\sqrt{2\mathcal H-H(x)}\,|dx|-\mathcal H L\right\}.
\end{aligned}\tag{CG2}
```

The stationary energy realizes the supremum: its flight time decreases
from infinity to zero. Extra complete turns of the circle strictly increase
the integral at every energy and cannot minimize. A potential period has
length pi/2. An arc shorter than that has strictly smaller integral than
one potential period; its complementary arc has strictly larger integral.
Hence the shorter arc is the unique minimum. The two arcs tie exactly when
`q=p+pi/2` modulo pi. Both are nonconjugate rotations. Cell-wall endpoints
follow by the same argument; a repeated wall endpoint has the unique
constant minimum with action -L/8.

These arguments retain every circle route in CR6 and establish the complete
minimizing-contact list:

- same-cell reflection seam `q=-p` (relative to the cell center), after its
  first half period;
- its conjugate edge, computed below;
- the antipodal rotation seam `q=p+pi/2`;
- a unique nonconjugate minimum everywhere else.

## 2. There are no additional minimizing conjugate folds

Let J be the endpoint Jacobi field normalized by `J(0)=0`, `J'(0)=1`.
If the path velocity never vanishes, reduction of order expresses J as a
positive factor times the integral of the reciprocal velocity squared;
there is no conjugate point. If its initial velocity is zero, the Wronskian
makes J a multiple of the path velocity. A first conjugate endpoint must
therefore be the opposite turn, after one half period. Time reversal also
handles a zero terminal velocity with nonzero initial velocity.

Suppose instead that both endpoint velocities are nonzero and there is
one interior turn. At a conjugate endpoint, differentiating the flight-time
identity gives

```math
\begin{aligned}
J(L)&=-\dot x(L)\dot x(0)\,L_{\mathcal H},\\
\partial_\nu^2x(L)&=-\dot x(L)\dot x(0)^2 L_{\mathcal H\mathcal H}
 \quad\text{when }L_{\mathcal H}=0,\\
D^3S[J,J,J]&=-J'(L)\,\partial_\nu^2x(L),
 \qquad\nu=\dot x(0).
\end{aligned}\tag{CG3}
```

The last identity follows by integrating the Wronskian of J and the second
initial-velocity variation; the potential is H/2. A favored turn has no
stationary flight time. A disfavored turn has strictly positive second
energy derivative, so CG3 is nonzero. Such a cubic stationary point cannot
minimize. Thus a minimizing conjugate point has both endpoint velocities
zero. Subsequent turns have an interior conjugate point and cannot minimize.
The equilibrium at a cell center has first conjugate time pi. At a cell
wall the Jacobi equation is hyperbolic and has no conjugate point.

## 3. Exact source-family data and the physical density

Let p now be the displacement of the source from its cell center, with
abs(p) less than pi/4, and put `m=sin(2*p)^2`. Denote the complete elliptic
integral of the second kind by E-calligraphic. The conjugate path and its
physical null time are

```math
\begin{aligned}
L_c(p)&=2K(m),\qquad q_c(p)=-p,\\
S_c(p)&=\frac{(m-2)K(m)+2\mathcal E(m)}4,\\
\tau_c(p)&=L_c(p)/2+S_c(p)
 =\frac{(m+2)K(m)+2\mathcal E(m)}4,\\
\frac{d\tau_c}{dm}&=(1-m/4)K'(m)>0,\qquad \tau_c(0)=\pi/2.
\end{aligned}\tag{CG4}
```

Integrating H over a half period gives `(K-E_calligraphic)/2`, proving the
action formula. There is a unique m-T with tau-c equal to T=7/4. It is less
than 1/2: `K'(m)>=pi/8` gives `tau_c(1/2)>=143*pi/256>7/4`. Put
`p_T=asin(sqrt(m_T))/2`. The causal source family consists of abs(p) less
than p-T in each of the two cells. Its boundary is the actual closing time
contact, not a discarded source neighborhood.

The normalized Jacobi mode and the quartic coefficient are

```math
\begin{aligned}
\psi_p(s)&=\frac{\mathrm{sn}(s,m)}{\mathrm{dn}(s,m)},\qquad
 \psi_p'(0)=1,\quad\psi_p'(L_c)=-1,\\
C(p)&=\tfrac18 P'(H(p)/2)=2K'(m)>0,\\
J(p)&=\int_0^{L_c(p)}\sqrt{\frac{2s(L_c(p)-s)}{L_c(p)}}\,\psi_p(s)\,ds,\\
\kappa(p)&=\tfrac43 J(p)C(p)^{-1/4}>0.
\end{aligned}\tag{CG5}
```

To obtain C without assuming a quartic jet, vary the initial velocity nu at
the turn. Energy changes by nu squared/2. Half-period antisymmetry gives
`x(L_c;nu)=-p+P'(H(p)/2)*nu^3/2+O(nu^4)`.
The endpoint linear term in the reduced action is `-nu*(q+p)`, since the
terminal derivative of the normalized Jacobi field is -1. Its stationary
equation therefore identifies the quartic coefficient as P-prime/8.
At p=0 this is pi/4, agreeing with CR10. At a middle split the state is
`nu*psi_p(L_c/2)+O(nu^2)`; the corresponding quartic coefficient in the
middle spatial coordinate is C divided by that Jacobi value to the fourth
power. The coefficient is positive throughout the entire causal source
family, not merely in the small interval supplied by CR12's implicit
function argument.

The mixed shooting derivative in L,nu is `psi_p'(L_c)=-1`, whereas the
L derivative itself is the zero terminal velocity. Together with the
reduced-action term `-nu*(q+p)`, this gives, after smooth state recentering,
the quadratic unfolding term `-(L-L_c)*nu^2/2`. A quadratic term proportional
to q+p does not change the parameter Jacobian. Normalize the quartic by
`u=C^(1/4)*nu`. The endpoint and volume normalizations at the contact are
consequently

```math
\begin{aligned}
\left|\frac{\partial(L,q)}{\partial(A,B)}\right|_{c}
 &=2C(p)^{3/4},\\
W&\sim\kappa(p)\int(E-u^4-Au^2-Bu)_+^{3/2}\,du,\\
D_0(p)&=400\,G(L_c(p),S_c(p))\,2C(p)^{3/4}.
\end{aligned}\tag{CG6}
```

The volume statement is the compact weighted-scaling limit, with the same
meaning and limitation as CR12, now along the explicit source family.
Both physical endpoint measures are still one. The factor 400 is their
r,z source integral; G is CR8's two-time and z-partner weight. No density
has been normalized away.

**Conditional only:** if a uniform subtracted transfer justifies replacing
the finite-part coefficient by its principal limit, its source-averaged
coefficient would be

```math
\begin{aligned}
C_*&=\frac49 I\sum_{\text{two cells}}
   \int_{-p_T}^{p_T}D_0(p)\,\kappa(p)^{-9/7}\,dp
 =\frac{12800}{9}I\int_0^{p_T}
 C(p)^{3/4}G(L_c(p),S_c(p))\kappa(p)^{-9/7}\,dp>0.
\end{aligned}\tag{CG7}
```

This derives a positive candidate density from the actual source geometry.
**CG7 alone does not identify C-star with C-phys.** That identification is
proved separately in CO13–CO14, using uniform subtracted matching and the
actual closing weights. Positivity of a candidate, even with a certified I,
would not justify the interchange by itself.

## 4. The other seams and their closing contacts

For an internal reflection seam, let m be defined by `L=2*K(m)`. It exists
for source displacement at most `asin(sqrt(m))/2`. Its action is CG4's
expression, independent of the starting phase p. Its null time increases
strictly with L, with derivative `1/2-m/8`. Thus it closes at the single
length `L_T=2*K(m_T)`. The two quartic endpoints of that seam meet the
closing face at p equal to plus or minus p-T. These intersections cannot
be removed in a physical matching argument.

For the rotation seam put `m=1/(8*H_calligraphic)`:

```math
\begin{aligned}
L&=2\sqrt m K(m),\qquad
 S_{\mathrm{rot}}=\frac{2\mathcal E(m)-K(m)}{4\sqrt m},\\
\tau_{\mathrm{rot}}&=L/2+S_{\mathrm{rot}},\qquad
 \frac{d\tau_{\mathrm{rot}}}{dL}=1/2-\mathcal H,\\
\min\tau_{\mathrm{rot}}&=\mathcal E(1/4)\lt\pi/2\lt T.
\end{aligned}\tag{CG8}
```

Its null time is strictly convex in L. At L tending to zero it diverges;
at `L=8*T/3` it exceeds T, since the action is strictly greater than -L/8.
It therefore has exactly two closing contacts, neither at its minimum.
At each ordinary seam the terminal momenta differ, so the equality of the
two smooth action branches is transverse. The seams are disjoint in the
retained finite-time region. There are no triple-minimum contacts.

All these contacts are strictly long for the **same** fixed delta below
S30's thresholds and pi/4: internal-seam times are at least pi/2, and the
rotation minimum is at least `sqrt(3)*pi/4`. At Delta-u=0, causality forces
constant x,z and the unique straight v generator; its screen tidal curvature
vanishes. Its full nearly-null neighborhood is retained, not discarded by
this pair-null statement. The quantitative regular/ordinary-cut and cutoff-
shell estimates are supplied in CO15. Contact classification alone is not
that estimate.

## 5. Exact composition and the transfer obligation

There is an exact reduction that avoids presuming a uniform long inverse.
Take the middle split l=L/2. In a small neighborhood of the source family,
l is uniformly less than pi, and each fixed-lift half action is strictly
convex: its second variation is bounded below by
`integral (variation'^2-variation^2)`. Near the retained half paths, winding
competitors have a fixed gap. Hence these half actions and their endpoint
maps are analytic. Put

```math
\begin{aligned}
U(a)&=S_l(p,a)+S_l(a,q),\\
D_s(x,a)&=S_s(p,x)+S_{l-s}(x,a)-S_l(p,a)\ge0,\\
S_s(p,x)+S_{L-s}(x,q)&=\min_a\{U(a)+D_s(x,a)\},\qquad 0\lt s\lt l.
\end{aligned}\tag{CG9}
```

This is the variational composition law, not a sum over selected rays.
For s bounded away from l, D-s has its unique zero at the point X-s(a)
of the minimizing first half path. At the source tip,
`X_s(a)=p+s*V(a)+O(s^2)` with nonzero derivative of V, and
`D_s=(x-X_s(a))^2*(1/s+O(1))/2`. The other tip is analogous.
The quartic middle germ admits local cusp coordinates; this identifies an
actual small-parameter envelope problem with a short-segment penalty, not
an arbitrary optical ansatz.

In minimum coordinates `a=sqrt(k)*r`, `A=k-6*a*a`, `B=8*a^3-2*k*a`,
and normal excess `h=k*k*E`, the physical volume can be written
`k^(7/2)*f_phys(k,r,E,p)`. The parameter measure is
`2*k^(7/2) dk dr dE`, times the actual smooth density, with the closing
weight still present. A Mellin variable z makes the required matching
particularly explicit. Let F-k(z,p) denote the E,r integral of the
physical volume to power -z, with its **own derived** first two E-endpoint
terms subtracted and their boundary terms restored. A sufficient estimate is

```math
\begin{aligned}
F_k(z,p)&=D_0(p)\kappa(p)^{-z}F_0(z)+O(k^\eta),\qquad \eta>0,\\
F_0(9/7)&=I,\qquad
\int_0^R2k^{(7/2)(1-z)}\,dk
 =\frac{4R^{(9-7z)/2}}{9-7z}.
\end{aligned}\tag{CG10}
```

The error must be uniform after source integration, through opening and
merging wells, with locally uniform complex-z bounds on both sides of 9/7
and adequate vertical growth control. It must include the physical weights,
cutoff and closing fibers. CG10 is **not inferred here** from the compact
CR12/CG6 limit or a positive sign certificate. CO13 proves the needed
source-integrated version after straightening the actual closing fibers;
it does not assume a pointwise fixed-p bound for the nonsmooth G weight.

The difficult corner is explicit: in CG9, s comparable to k is the
transition from the interior cusp profile to the endpoint penalty. At small
E the two spatial wells can overlap when s is of order kE; their physical
union cannot be replaced by their sum. Freezing the leading quadratic
penalty would only predict an overlap volume of order `k^6*E^4`, not prove
it. CO5–CO9 instead derive a uniformly invertible rescaled system for the
actual nonconstant D-s, and prove that bound with the subtracted remainder.
Closing at p-T introduces the weight
`(T-tau_c(p)+parameter corrections)_+^(3/2)`; CO11 straightens the closing
function before integrating b, rather than freezing or differentiating this
fractional-power weight at its zero.

CO14–CO16 carry out the corresponding Mellin continuation for the actual
whole pair measure. The kernel cancels the simple regular poles at 1/2 and
1, but not its derived 9/7 pole. This supplies the complete-action conclusion
that classification and CG7 alone could not provide. The distinction from
signed methods remains important: failure of absolute cubic averaging was
never itself a proof that the signed response fails to converge.

## 6. Complete-action and probability ledger

The actual full pair integral remains CR8, with all source p, every causal
partner, physical interval unions, both endpoint measures and the exact
closing weights. Split it with **one** positive fixed temporal cutoff as
in CR9. The physical point occurs once, in short. S30 supplies the short
limit and CP2 restores the target only after the complete long response is
controlled. That final control is the separate CO1–CO16 argument.

The unchanged finite-density Poisson bridge is applied in that sequel only
after the complete deterministic asymptotic is derived. No sample-wise
convergence or divergence is inferred from expectation alone.

`curved4_focal_globalization.py` provides floating diagnostics of this
classification, source data, closing weights and normalization. It is not a
certified full-action solver or a substitute for the written matching proof.
The original curved-4D scope is not narrowed, no universal positive theorem
is refuted merely by CG7, and independent scrutiny remains with #94/#86.

Refs #151, #81, #24, #94, #86.
