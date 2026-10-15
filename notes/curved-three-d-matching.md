# Curved 3D: signed averaging and a type-free conjugate-point estimate (#177)

**Continuation, not completion of the original arbitrary-metric theorem.**
This attacks the critical remainder rather than adding another spacetime
example. It preserves [C3.1–C3.9](curved-three-d-response.md), FCDC-3 and
[the complete quartic-focus result F3.1–F3.8](curved-three-d-focusing.md).
Their delivered source is pinned at
[`d75feaf`](https://github.com/q5m-ai/causal-set-emergence/tree/d75feafe5c7b1e01d8cf4584c5fedead73f9b0b2).
Shared inputs remain the actual G-SS contract, G1–G7, S1–S30 and measured-order
expectation bridge at `d2cbbc12dbfee6376140a2137013f3d409adfdbf`.

New outputs are: a weaker **averaged** criterion not requiring a pointwise
second coefficient; an explicit reconstruction of the quartic matching;
and a geometric one-screen minimum-jet/Jacobian identity with a weighted
angular estimate that does **not** count or classify singularities. The last
estimate controls the genuinely nonlinear near-conjugate layer wherever its
quartic coefficient is bounded below. The remaining uniform passage through
vanishing quartic coefficients and whole clusters of near-minimizers is not
proved. No additional complete G-SS class or FAILS row is claimed.

The integration base moved to `3895e7919fb25640c00f516d6ec8f17e35eeb7ce`
while this continuation was being written: #176 was finalized separately.
Its curved-2D theorem and #179's independent null/mixed work are not premises
here. Their files, claims and finalization receipts are not edited.

## 1. The observable and an averaging criterion without a second pointwise jet

Use C3's genuine 3D kernel and constants, the **actual** phase
w=(V/c3)^(2/3), and the cumulative pushforward N of the entire long pair
measure. All ordered source/target labels, both endpoint measures, physical
route unions and masks are inside N. For a signed field or finite pair
partition use the signed N, not an absolute-volume surrogate. Put

```math
\begin{aligned}
F(z)&=K_3(z^{3/2}),&t&=(c_3\rho)^{-2/3},\\
Q(w)&=\int_0^w N(s)\,ds
 =\int_{M\times M}\mathbf1_{\{x\preceq y,\ \ell\ge\delta\}}
       \chi(x)\phi(y)[w-(V(x,y)/c_3)^{2/3}]_+
                         \,d\mu_g(x)d\mu_g(y),\\
P_{\mathrm{long}}(\rho)&=t^{-1}\int_0^\infty Q(tz)F''(z)\,dz,\\
L^\delta(\rho)&=-\beta_3c_3^{-5/3}t^{-7/2}
                         \int_0^\infty Q(tz)F''(z)\,dz.
\end{aligned}\tag{M3.1}
```

These are finite-density identities, not a changed observable. Tonelli for
positive measures and signed Fubini prove the ramp formula. C3.3 gives
N=O(w), so Q=O(w²) at zero. N is continued constantly beyond its support,
and Q **linearly**, not by zero. Twice integrating by parts in G5 gives
M3.1; the origin and infinity terms vanish with these continuations.
F-double-prime is O(z^(-1/2)) at zero and exponentially decreasing times
powers at infinity. Its real signed moments are

```math
\begin{aligned}
\int_0^\infty z^2F''(z)\,dz&=0,&
\int_0^\infty z^3F''(z)\,dz&=0,\\
E_Q(w)&=\frac{Q(w)-b_1w^2/2-b_2w^3/3}{w^{7/2}},\\
L^\delta(\rho)&=-\beta_3c_3^{-5/3}
       \int_0^\infty z^{7/2}F''(z)E_Q(tz)\,dz.
\end{aligned}\tag{M3.2}
```

Indeed the two moments are twice the zeroth and six times the first
moment of F, respectively. These are exactly C3.1's two zeros, not 2D
logarithms or a third 4D zero. The critical moment is nonzero.

**Averaged sufficient criterion.** If, for some real b2, E-Q is bounded
near zero and tends to zero, the actual long contribution tends to zero.
The constant b1 can be the already derived C3.4 coefficient. Away from zero
E-Q is bounded by finite variation and the linear continuation of Q. The
integrable weight in M3.2 then proves the conclusion by dominated convergence.
This is an analytic implication to be discharged from geometry, **not** a
new field in G-SS or a proof that arbitrary curved metrics satisfy it.

It is strictly weaker than demanding N=b1*w+b2*w²+o(w^(5/2)). For example,
on a sufficiently small fixed interval take the **abstract** positive
primitive

```math
\begin{aligned}
N(w)&=w+w^2\sin(w^{-a}),\qquad \tfrac12\lt a\lt1,\\
N'(w)&=1+2w\sin(w^{-a})-a w^{1-a}\cos(w^{-a})>0,\\
\left|Q(w)-w^2/2\right|&\le\frac2a w^{3+a}=o(w^{7/2}).
\end{aligned}\tag{M3.3}
```

Continue N constantly past a sufficiently small endpoint. The last bound
follows by substituting u=w^(-a) in the remainder integral and integrating
once by parts; the decreasing amplitude bounds the remaining tail. Thus the
signed response vanishes although (N-w)/w² has no limit. This is a
counterexample to the **necessity of the pointwise-jet criterion**, not a
spacetime construction or a counterexample to #177. No realization of this
oscillation by a G-SS metric is claimed. It prevents making existence of a
classical second coefficient an unjustified prerequisite for every proof.

## 2. What actually repairs the quartic calculation

F3 does not assign a finite value to its divergent cubic inverse integral.
Here is the matching directly in the primitive variable. Retain F3's actual
r-averaged physical inverse, both wells, both endpoint overlaps, closing
weight and all smooth density factors. For fixed k let H-k(sigma) be the
cumulative integral of those factors over the normalized states with
f-sqrt(k)^(2/3) at most sigma. F3's uniform Morse construction gives

```math
\begin{aligned}
H_k(\sigma)&=A_k\sigma+B_k\sigma^2+O(\sigma^3)
                                  &&(0\le\sigma\le\sigma_0),\\
|H_k(\sigma)|&\le C\sigma^{6/5} &&(\sigma\ge\sigma_0),\\
N_{\mathrm{focal}}(w)&=
 \int_0^{k_0} k^{7/2}H_k(c_3^{2/3}w/k^{5/3})\,dk.
\end{aligned}\tag{M3.4}
```

Additional compact parameters are integrated or suppressed in H-k; all
bounds are uniform in them. The large-sigma estimate is the **physical**
F3.5 bound, with the real bounded energy domain, not an extended homogeneous
tail. The small-sigma assertion follows also directly: invert each open
well's positive E^(3/2) phase after taking its 2/3 power. Near opening,
substitute its exact depth equal to sigma times a bounded new coordinate;
the positive primary volume gives a uniformly positive inverse derivative.
The opening band has width O(sigma), producing a quadratic coefficient and
O(sigma³) error after averaging. F3.4's union-volume error changes the inverse
by O(k² sigma^(5/2)) only on that band, hence changes H-k by
O(k² sigma^(7/2)). It cannot be discarded pointwise but is smaller than the
required averaged error. F3's closing coordinate is straightened **before**
this operation. These facts, rather than a fixed-r Taylor series, give M3.4.

Constants absorb c3 in the following bounds. Split the k integral at a
constant multiple of w^(3/5), corresponding to fixed sigma-zero. This is an
estimate of one fixed physical primitive, **not a density-dependent temporal
cutoff or a change of domain**. The two coefficients are integrable, whereas
the unsplit cubic majorant is not:

```math
\begin{aligned}
b_1^{\mathrm{focal}}&=c_3^{2/3}\int_0^{k_0}k^{11/6}A_k\,dk,&
b_2^{\mathrm{focal}}&=c_3^{4/3}\int_0^{k_0}k^{1/6}B_k\,dk,\\
w^3\int_{w^{3/5}}^{k_0}k^{-3/2}\,dk&=O(w^{27/10}),\\
w^{6/5}\int_0^{w^{3/5}}k^{3/2}\,dk&=O(w^{27/10}),\\
w\int_0^{w^{3/5}}k^{11/6}\,dk+
 w^2\int_0^{w^{3/5}}k^{1/6}\,dk&=O(w^{27/10}).
\end{aligned}\tag{M3.5}
```

The last line restores the portions of **both** subtractions across the
matching boundary. Consequently this focal primitive has a quadratic
expansion with O(w^(27/10)) remainder, and its Q remainder is
O(w^(37/10)). This independently explains the margin above 5/2 and 7/2.
The signed zeros remove the two legitimate coefficients; endpoint abundance
and matching control what remains. The nonintegrable cubic coefficient is
never integrated to zero or identified with an action coefficient.
F3's already proved complete action and expectation, including its regular
and positive-volume complements, are preserved. This section is a mechanism
proof, not another special-geometry theorem.

## 3. A general smooth one-screen reduction near minimizing conjugacy

This step uses geometry, not analytic contact classification. Fix the compact
long null relation with arrival gap at least delta/2; C3.3 puts its excluded
small-arrival-gap complement above a positive volume floor. Use normalized
initial null directions and affine length on its compact geodesic-parameter
set. Affine and temporal lengths have uniform comparison on this fixed set,
by the geodesic ODE and compact causal control.

A proper subsegment of a minimizing null ray is unique and nonconjugate.
A second subsegment with a different tangent would concatenate to a broken
null curve and give chronological push-up; an interior conjugate point would
likewise contradict minimization beyond it. Equality of tangent gives the
same geodesic by ODE uniqueness. Thus a middle transverse section and both
proper endpoint pieces have smooth arrival graphs. Their inverse bounds
are uniform in smaller neighborhoods of the compact ray set. A finite cover
of **ray charts** follows; this is not a finite list of minimizing paths or
singularity types.

In one such chart, let a be the screen coordinate of the intersection of
the source cone with the middle section, and p=(p1,p2) the two labels of the
target timelike flow. Send that middle point along the second arrival graph
to the target flow. Its arrival clock U(a,p;x) is smooth, with source x as
an additional compact parameter. Actual first arrival is the minimum over
all admitted middle states in all relevant charts, not a sum of local
arrivals. At a state which realizes that global arrival, U(a+z,p)-U(a,p)
is nonnegative for all sufficiently small z.

In three dimensions the screen Jacobi equation is scalar. Its solution j,
normalized by j(0)=0 and j-prime(0)=1, has a simple first zero: simultaneous
j=j-prime=0 is excluded by uniqueness. Compactness bounds j-prime away from
zero on the minimizing conjugate set. The middle Hessian U-aa is a positive
smooth multiple of j at the terminal point, with nonzero proper-segment
Jacobi factors in the denominator. A terminal displacement along the ray
therefore crosses U-aa=0 simply. The transverse endpoint displacement changes
U-a with nonzero derivative by the nonconjugate second-half inverse.
At a minimizing conjugate point U-aa=U-aaa=0, so these two variations prove
that the following matrix is invertible:

```math
\begin{aligned}
M&=\begin{pmatrix}U_{ap_1}&U_{ap_2}\\
                  U_{aap_1}&U_{aap_2}\end{pmatrix},&
U_a(a,p(a,k))&=0,&U_{aa}(a,p(a,k))&=2k,\\
b(a,k)&=U_{aaa}/6,&c(a,k)&=U_{aaaa}/24,\\
p_a&=M^{-1}\binom{-2k}{-6b},&
p_k&=M^{-1}\binom{0}{2},&
\left|\det\frac{\partial p}{\partial(a,k)}\right|
 &=\frac{4k}{|\det M|},\\
\partial_a b&=4c+	frac16 U_{aaap}M^{-1}\binom{-2k}{-6b}
             =4c+O(k+|b|).
\end{aligned}\tag{M3.6}
```

Here the last derivative holds **k fixed**, and all derivatives of U on the
right are evaluated at (a,p(a,k)). The implicit function theorem gives these
coordinates on a smaller rectangle, uniformly in source parameters. This
requires only smoothness and the derived two-control rank. No quartic normal
form, nonzero fourth derivative, genericity or analyticity is used.

Let G-k be the measurable set of a in this rectangle for which that stationary
state realizes the **global** first arrival. It may have arbitrarily many
components; at k=0 it may contain a continuum. It need not be an interval.
For k>0 the actual pair measure in these coordinates has the form
J(x,a,k,h)*k dx da dk dh, where h is the advance of the target clock from
first arrival and J is smooth positive bounded above and below. This retains
the source volume density, target volume density and the determinant in M3.6.
Face and cutoff masks remain their actual indicators. Almost every arrival
label has a unique nonconjugate ray by C3.4; multiply covered tie labels have
zero label measure. Finite ray-chart weights count that ray once. None of
these statements removes any neighborhood of a tie or conjugacy.

## 4. Minimum positivity gives angular averaging without counting contacts

Taylor expansion at a global minimum on a fixed screen neighborhood gives

```math
\begin{aligned}
D(z)&=U(a+z,p)-U(a,p)
      =kz^2+bz^3+cz^4+O(|z|^5)\ge0,\\
|b|&\le C\sqrt{k}\quad\hbox{on }G_k,\\
\int_{G_k}\psi(a)c(a,k)_+^2\,da&\le C\sqrt{k}.
\end{aligned}\tag{M3.7}
```

The smooth nonnegative chart weight psi has compact support inside the state
rectangle. For the second line use the bounded fourth-order remainder and
put z opposite in sign to b, of magnitude proportional to abs(b).
Nonnegativity yields b²<=C*k. Shrinking the fixed chart guarantees this z
stays inside it. At k=0 this is the familiar vanishing cubic variation of a
minimum, now with an actual uniform near-minimum bound.

For the last line use M3.6: on G-k, c-positive squared is bounded by a
constant times b-a squared plus k. Put s=C*sqrt(k), and clip b to [-s,s].
Integration by parts, valid for this Lipschitz clipping function, gives

```math
\begin{aligned}
\int_{\{|b|\lt s\}}\psi(b_a)^2\,da
 &=-\int \mathrm{clip}_s(b)(\psi b_a)'\,da\\
 &\le s\int\bigl(|\psi' b_a|+\psi|b_{aa}|\bigr)\,da
 \le Cs.
\end{aligned}\tag{M3.8}
```

Enlarge s slightly if needed to include the non-strict band. Smoothness of
U and the bounded inverse of M bound b-a and b-aa uniformly, even at k=0.
This proves M3.7 after integrating over G-k, without integrating along its
boundary or assuming a finite number of zeroes. Source integration and
finite chart sums preserve the estimate. Thus for every fixed eta>0,
G-k intersect {c>=eta} has weighted size at most C*eta^(-2)*sqrt(k).

This is the general geometric counterpart of the sqrt(k) angular abundance
visible explicitly in the quartic model's a=sqrt(k)*r substitution. It also
shows why a fictitious independent positive-quartic degeneracy at every
angular label is not a valid replacement for the endpoint geometry: b=0,
c=1 on an open a interval at k=0 contradicts b-a=4c there.

## 5. What the geometric estimate actually controls

The same minimum inequality constructs a contained **physical** sublens.
On a fixed central longitudinal interval the broken-clock defect is bounded
above by C*(k*z²+sqrt(k)*abs(z)³+z⁴); the nearby middle charts are related by
bounded nonconjugate maps. Advancing the target clock by h opens a positive
clock width comparable to h. Choose screen width a sufficiently small
multiple of sqrt(h/(k+sqrt(h))). Its whole sublens lies in the actual interval,
so positive bounded metric density gives

```math
\begin{aligned}
V(x,y)&\ge c\frac{h^{3/2}}{\sqrt{k+\sqrt h}},\\
\mathcal B&=\{0\lt k\le\sqrt h\},\\
|\nu_{\mathcal B}|\{V\le v\}
 &\le C\int_0^{Cv^{4/5}}\int_0^{\sqrt h}k\,dk\,dh
  =O(v^{8/5}),\\
|\nu_{\mathcal B\cap\{c\ge\eta\}}|\{V\le v\}
 &\le C\eta^{-2}\int_0^{Cv^{4/5}}
                      \int_0^{\sqrt h}k^{3/2}\,dk\,dh
  =O(\eta^{-2}v^{9/5}).
\end{aligned}\tag{M3.9}
```

Every other path can only enlarge this sublens's volume; it is not counted
as a second interval. These are upper bounds for absolute pair measure, so
retaining a face/cutoff/closing indicator can only reduce them. They hold for
bounded endpoint fields, all finite ordered partitions and arbitrary admitted
contacts inside these sectors. They do **not** estimate phase derivatives or
justify a sum of separate route kernels. The geometric set B is fixed by the
pair data, not by density, and does not replace the fixed temporal split.

A phase sublevel bound O(v^s) bounds its polynomial-exponential kernel integral
absolutely by O(rho^(-s)), using dyadic volume bands or Stieltjes integration.
The positive-quartic part of B therefore has normalized response
O(eta^(-2)*rho^(-2/15)) and vanishes for each fixed eta. The rough B bound gives
only O(rho^(1/15)). **Neither is a conclusion about the complete action.**
The regular side of the matching, small-quartic sector and ordinary competing
routes are still present. No contribution has been deleted as measure zero.

### Closing contacts: a useful bound, but not the missing mixed estimate

There is also an unconditional first-order contact bound. For a source x,
intersect its first-arrival front with a compact smooth spacelike target
face, or with a sufficiently small timelike-flow translate of that face.
Each null ray meets that achronal face at most once; the timelike conormal
pairs uniformly nontrivially with a normalized null tangent. Its hitting time
and point map are smooth with bounded derivatives on the compact ray set,
regardless of endpoint conjugacy. The front intersection is contained in the
image of the compact one-dimensional direction set, so its length is bounded
by the integral of that map's speed, not by a branch count. Translated local
face patches use a finite cover and the same bounds.

The arrival graph is Lipschitz. At differentiability points its null conormal
is uniformly separated from the face's timelike conormal. Coarea and the
preceding length bound therefore give O(epsilon) measure for the labels whose
arrival-to-face gap lies in any width-epsilon band near zero. The same applies
to the temporal cutoff level. This permits continuously many minimizers and
arbitrary closing tangencies; the actual source and target masks are retained.
But it is **unweighted**. Combining it with M3.7 by taking the smaller of two
bounds does not produce their product or control the singular inverse-phase
weights. Simultaneous closing/weak-focusing matching still needs a proof.

## 6. Attempts to close the remaining gap, and why they do not yet do so

### A. Direct absolute domination is now quantitatively inadequate

The universal estimate in M3.9 misses the critical volume exponent 5/3 by
exactly 1/15. This is not a hidden proof of divergence. It says that bounded
smooth jets, a contained quartic-sized sublens and the Jacobian k alone do
not finish the argument. For a purely analytic negative control, consider

```math
\begin{aligned}
W(k,h)&=\int_{\mathbb R}[h-ku^2-u^4]_+\,du,\\
P_{\mathrm{panel}}(\rho)&=\int_0^1\int_0^1
                              kK_3(\rho W(k,h))\,dh\,dk,\\
I(8/5)&=-\frac{125}{126}(3/4)^{8/5}(6/5)^{7/5}\ne0,\\
P_{\mathrm{panel}}(\rho)&\sim
       \frac25\widehat K_3(8/5)I(8/5)\rho^{-8/5}.
\end{aligned}\tag{M3.10}
```

This is a complete **abstract pair integral**, not a metric, G-SS region or
canonical full action. It lacks the angular/minimum compatibility M3.6 and
must not appear in FAILS. It shows why an argument using only the rough
bounds cannot silently rely on the genuine 3D kernel to cancel the missing
power. There is no ambient target or Poisson claim for this surrogate.

For the displayed calculation put h=k²E and
f(E)=W(1,E). If E=r²+r⁴, then
f=(4/3)r³+(8/5)r⁵. The analytically continued integral of f(E)^(-s) is
(4/3)^(-s)*(5/6)^(1-3s/2) times
B(1-3s/2,5s/2-1)+(5/3)*B(2-3s/2,5s/2-2).
At s=8/5 this is the nonzero value above. To check matching rather than extend
a divergent model tail, change the **bounded** original domain to
k=r²t, h=r⁴(1+t). Its measure is 2*r⁷*t*(t+2) dr dt and
0<r<min(t^(-1/2),(1+t)^(-1/4)). Integrating r gives a pole at 8/5;
the large-t expansion has only the two earlier poles 2/3 and 4/3 before it.
The kernel zeros cancel those two, not 8/5. Subtracting that large-t head
and shifting just past 8/5 proves M3.10, including both bounded-domain edges.
The beta continuation is only an evaluation of this matched residue.

### B. Type-free averaging helps, but its small-quartic constants are not uniform

M3.7 replaces a finite quartic classification by a derived weighted estimate.
It does not bound the size of G-k where c is small. At a flat minimum an
entire interval of a can have b=c=0, consistently with M3.6. Dividing by c
would reintroduce precisely the unjustified inverse bound we are avoiding.

One can begin an adaptive estimate. Taylor's bounded fifth-order remainder,
nonnegativity, and a test displacement of size
min(sqrt(k/eta),k^(1/3)) give, wherever abs(c)<=eta,
abs(b)<=C*(sqrt(k*eta)+k^(2/3)). This suggests the effective scale
k²/(eta+k^(1/3)), not the quartic k². However the actual volume is the physical
union over **all** near-minimizing states, not the sublens of this selected
minimum. Other wells can open on that changing scale, possibly infinitely
many, and their tip images can overlap. A separate positive-quartic inverse
per well is not uniformly available. No bound on the averaged ramp remainder
of order 7/2 follows from the test-displacement inequality alone.

The new precise unfinished step is a **uniform physical-union matching
estimate on these adaptive small-quartic clusters**, including their actual
endpoint density and face/cutoff masks. It must either prove M3.2's averaged
remainder (or a still weaker adequate signed bound), or derive a surviving
complete response. Neither a second pointwise coefficient nor finite type
should be assumed. Continuously many minimizers are included in this step.

### C. Bounded variation of the arrival front does not justify summing cut jets

A distinct attempt uses Lipschitz/semiconcave arrivals and their finite
variation instead of a contact normal form. At a regular two-route seam,
changing to the action-gap coordinate divides by the difference of the two
terminal momenta. Finite variation controls the **jump**, not its reciprocal.
For the convex support envelope of N equally spaced unit directions, the
sum of gradient jumps is N*2*sin(pi/N), bounded, while the sum of their
reciprocals grows quadratically in N. These are elementary plane envelopes,
not G-SS counterexamples. They refute the proposed inference from bounded
variation alone to uniformly summable separate seam constants.

Physical union volume may compensate exactly for this loss when many routes
coalesce. Consequently the appropriate object is the whole cluster's ramp Q,
not the sum of its individual cut or tube expansions. This is compatible with
M3.1 and the geometric clipping estimate, but the required joint bound is not
proved here. The first-order closing bound above does not fix it by itself.

## 7. Complete accounting and original-acceptance crosswalk

The temporal cutoff delta is chosen once below C3 section 4's discharged
short-locality, derivative, root, joint and shell margins. Smoothness on the
compact causal enclosure gives those finite bounds; timelike face conormals
and transverse joint conormals give their positive denominators. S30 retains
both face fluxes and the compensating joint term, and gives the independent
short target. A=S+L exactly, with the physical point in short **once**.
All new ramp identities apply to the same L. Geometric/state subdivisions
only split that fixed pair integral and must be summed before any full limit
is asserted. No artificial boundary, cross-chart partner or closing fiber is
removed. Unit fields specialize the target to half curvature plus the induced
curve-length/normal-angle integral, defined independently of the action.

For any future general deterministic conclusion, the already discharged
C3 section 5 facts apply separately: standard Borel manifold, closed Borel
ambient order, finite atomless geometric volume, contained exclusive physical
intervals, Borel volume by Tonelli and finite Poisson second moments. The
actual layer factorials and the original finite Poisson law then identify
expectation at each positive density. This bridge **cannot** supply the missing
deterministic limit. No new universal expected or sample-wise theorem follows.

| Original #177 item | Source-backed continuation / exact boundary |
| --- | --- |
| Every original smooth curved 3D G-SS member; no new geometric restrictions | C3.2–C3.4 preserved; M3.1–M3.2 exact for the full physical primitive; M3.6–M3.9 derived locally near every minimizing conjugacy without finite-type assumptions. Full original conclusion remains UNKNOWN |
| Genuine 3D moments, critical response and actual remainder | M3.1–M3.3 prove the weaker averaged test; M3.4–M3.5 reconstruct actual quartic matching; M3.7–M3.9 derive angular averaging and its precise range, not the unresolved full remainder |
| Both measures, all paths/unions, changing/continuous multiplicity | Exact C3 clock/ramp union, actual k-weighted pair Jacobian and global minimum set. No separate-tube kernel sum; adaptive whole-cluster matching remains missing |
| Moving/closing/cutoff contacts and all ordered partitions | Actual masks retained in exact identities and absolute bounds; general first-order spacelike-contact abundance derived. The mixed weighted critical estimate remains open, not inferred from separate bounds |
| Complete deterministic target at compatible fixed cutoff, point once | FCDC-3 and F3 complete results preserved at their exact scopes. General S30 hypotheses discharged, but no new arbitrary-metric full limit is asserted |
| Independent target and original-law expectation afterward | Existing independent target and C3.9 unchanged; general finite-density identity remains valid, universal expected limit remains UNKNOWN with deterministic one |
| Adversarial evidence and failed approaches | Signed averaged criterion with no pointwise second coefficient; quartic matching exponents; minimum-coordinate Jacobian/clipping; impossible independent quartic panel and nonuniform cut-jet sum controls. Diagnostics are not a geometric remainder proof |
| Strongest justified result / retained ownership | No new complete-class WORKS row or G-SS FAILS row. #177 under #81 retains all original arbitrary-metric and contact quantifiers; #94/#86 retain independent scrutiny and justified formalization |

## 8. Verification and stopping boundary

This continuation establishes the preceding written analytic/geometric lemmas,
with finite symbolic/numerical regressions in `test_curved_three_d_matching.py`.
It does not certify a universal asymptotic remainder numerically, compile a
manifold proof, or obtain independent mathematical acceptance. Earlier tests,
proofs, certificates and dated PR receipts are preserved. The PR records the
new exact head, local checks, integration-tree checks, CI and newly authorized
single bounded feedback pass separately from the first delivery.

The stopping point is materially narrower than “arbitrary caustics lack an
analytic classification”: **the first angular weighted estimate now follows
from smooth geometric minimum coordinates and clipping; a fixed positive
quartic sector is controlled without classifying its contacts.** What is not
proved is its uniform signed physical-union extension when that quartic
coefficient vanishes, simultaneously with moving masks and competing-state
clusters. The averaged test shows that a pointwise second coefficient need
not be the only route. Neither the rough 8/5 bound nor M3.10's deliberately
non-geometric panel is a counterexample to the original G-SS action.

Thus #177/#81/#24 remain incomplete and open. No canonical definition or law,
physical cutoff convention, source scope, issue state or old proof is changed.
No agent, merge or deployment is authorized by this written continuation.

Refs #177, #180, #81, #24, #94, #86.
