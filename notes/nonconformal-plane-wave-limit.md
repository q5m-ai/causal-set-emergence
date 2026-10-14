# Non-conformal metric stability of the 4D correspondence (#81 / #167)

**Written theorem PW-4, not a formal certificate or independent acceptance.**
This continuation of [RPL-4](geometric-long-cancellation.md) proves complete
canonical deterministic and separately transferred expected limits for an
infinite-dimensional class of genuinely non-conformal ambient metric changes.
It solves the whole-diamond/two-tip problem in that class, including the
parallel-null collar and simultaneous spacelike-face/cutoff contacts. It does
**not** assert that RPL, absence of caustics, or correspondence is open in the
space of arbitrary Lorentzian metrics. #164's obstruction is unchanged.

## 1. Precise theorem and proof dependencies

Let G be any smooth symmetric positive-definite 2 by 2 matrix function on the
real line, with fixed global bounds `m I <= G(u) <= Lambda I`, where
`0<m<=Lambda<infinity`.
On the actual ambient manifold R4, with coordinates `(u,v,X)` and X in R2, put

```math
\begin{aligned}
g_G&=2\,du\,dv-dX^T G(u)dX, &
 d\mu_G&=\sqrt{\det G(u)}\,du\,dv\,d^2X,\\
 T&=(u+v)/\sqrt2, & Z&=(v-u)/\sqrt2.
\end{aligned}\tag{PW1}
```

These are Rosen plane-wave metrics; no field equation or energy condition is
imposed. Choose the future orientation by increasing T. Take **any** smooth
G-SS region M in this ambient spacetime, in the exact sense of the
[general contract](general-contract.md#3-a-precise-non-vacuous-general-core-candidate).
In particular ambient containment of every closed interval is required, not
inferred from intrinsic global hyperbolicity. There is no global graph or
joint-topology restriction on M beyond G-SS.

**Theorem PW-4.** For each such fixed G and M, the complete fixed-positive-gap
long response vanishes for every sufficiently small compatible cutoff. The
canonical minimal-layer action tends to the independently defined G-SS target.
The expectation under the **original** Poisson law of intensity `rho*mu_G|M`
tends to the same target, by a separate finite-density identity. The scalar
curvature of PW1 is zero; the target is therefore its actual induced
spacelike-joint integral, not a flat-area surrogate. Nonempty variable-angle
joints are included.

**Metric stability, precisely scoped.** One may replace G by *any* other smooth
matrix profile with these bounds, and choose any G-SS region for the new
metric. For `G_epsilon=G+epsilon H` with smooth bounded symmetric H, positivity
is preserved whenever `abs(epsilon)*sup(norm(H))<m`; all conclusions apply
provided the region satisfies G-SS for that metric. Section 6 supplies one
fixed nonempty-joint region for a whole genuinely non-conformal deformation.
Constants are locally uniform on profile families with a common eigenvalue
margin, bounded needed derivatives on the compact causal enclosure, and common
region/contact margins. This is stability **within the matrix-profile class**,
not openness under arbitrary metric perturbations or at loss of those margins.
No density/metric-parameter limit interchange is asserted.

Proof dependencies, in order:

1. PW2–PW7 below derive the actual order, whole interval, volume, both tips and
   a uniform phase from the metric, including changing eigendirections.
2. Section 4 derives the true endpoint-contact ranks and cubic density
   remainder; PW8 uses the unchanged three signed 4D moments.
3. [S30](general-metric-short-remainders.md#8-quantified-short-theorem-partition-cancellation-and-the-151-boundary)
   is the existing **written** general-metric short theorem, at the same fixed
   cutoff, with the physical point only in short. It restores the independently
   defined bulk and joint. We do not port or reprove S30 here.
4. The finite atomless measured-order Poisson bridge is applied only afterward.
   Existing generic checked bridge declarations are not new compiled PW limits.

## 2. Reconstructing the geometric obligation, without assuming it

RPL-4 requires more than a positive lens volume or one nonsingular Jacobi
matrix. Its hypotheses are actual endpoint-density/contact coordinates,
whole-interval maps with eight dominated rescaled derivatives and reference
reflection, geometric noncollapse outside singular wedges, and the strict
endpoint-abundance inequality GC2. Finite ordered pair covers must include
cross-chart partners, overlaps, cap complements and the entire physical union.

| Requirement | Already discharged before this continuation | PW-4 discharge / limitation |
| --- | --- | --- |
| Physical point multiplicity and interior weight | SW5–SW8 on the sphere slab; GC5 under faithful whole conformal diamonds | PW2–PW5 solve the full strictly convex path problem; no selected-ray sum or union approximation |
| Two tips and small-phase bounds | SW8's rescaled angular construction; the full boosted diamond in GC5 | PW6–PW7 integrate the exact slice maps **before** differentiating; both tips and the parallel-null collar have uniform divided-volume bounds |
| Both endpoint measures / moving contacts | SW7 closing fibres; GC6 spacelike face/shell ranks | Section 4 retains both PW1 factors and derives the same intrinsic contact ranks from the actual null relation |
| Focusing / singular abundance | Sphere exponents satisfy GC2; quartic exponents fail the sufficient bound, while CO1–CO16 separately prove divergence | Positive matrix path energy excludes competing minima in this class; no singular abundance test or treatment of a lost positive margin is claimed |
| General intrinsic metrics | Not supplied by the words no-caustics, convexity or global hyperbolicity | Still not supplied. Section 8 identifies the precise lost identity and the next uniform estimate needed |

There is an important distinction: the elementary PW slice map has bounded
rescaled derivatives through both tips when the u gap is bounded below, but
**does not establish RPL's uniform point-map clause as the u gap tends to
zero**. We do not silently add that premise. Instead PW7 gives a smooth exact
volume formula uniformly at that direction, sufficient to prove the same
signed cancellation directly. RPL is sufficient, not necessary. This direct
phase argument is a derived geometric producer, not an assumed volume jet.

## 3. The whole physical interval and its tip resolution

Write endpoints as `p=(u0,v0,X0)`, `q=(u1,v1,X1)`, and initially let
`L=u1-u0>0`. Set D=X1-X0 and define

```math
\begin{aligned}
 B(a,b)&=\int_a^b G(r)^{-1}\,dr, & B&=B(u_0,u_1),\\
 S_{a,b}(D)&=\tfrac12D^T B(a,b)^{-1}D, &
 e&=v_1-v_0-S_{u_0,u_1}(D),\\
 X_c(s)&=X_0+B(u_0,s)B^{-1}D. &&
\end{aligned}\tag{PW2}
```

A future causal path with increasing u obeys
`2*v' >= X'^T G X'`. Minimize the integral on the right with fixed transverse
endpoints. Completing the square about `X'=G^-1 B^-1 D` gives exactly
`D^T B^-1 D` plus the nonnegative integral of the deviation squared in G.
Strict positivity makes the minimizer unique. Thus the **actual ambient**
order for L>0 is `e>=0`, with chronological order `e>0`. Vertical u-constant
causal segments have constant X and increasing v; allowing these segments
only adds nonnegative v length and cannot lower the minimum. Conversely the
minimizer, with any nonnegative excess distributed in v, realizes the order.
This accounts for all causal paths, not just geodesics near a chosen branch.

For `u0<s<u1`, put B0=B(u0,s), B1=B(s,u1). The exact completion of squares is

```math
\begin{aligned}
 S_{u_0,s}(X-X_0)+S_{s,u_1}(X_1-X)-S_{u_0,u_1}(D)
  &=\tfrac12 (X-X_c)^T C^{-1}(X-X_c),\\
 C&=(B_0^{-1}+B_1^{-1})^{-1}
   =B_0-B_0B^{-1}B_0.
\end{aligned}\tag{PW3}
```

The second expression is symmetric even when the matrices do not commute.
It is a positive covariance, not a determinant of a selected geodesic branch.
Let z range over the **entire** unit disk and `0<r<1`. The following map is
one-to-one almost everywhere onto the whole chronological interval:

```math
\begin{aligned}
 u_*&=s, & X_*&=X_c(s)+\sqrt{2e}\,C^{1/2}z,\\
 v_*&=v_0+S_{u_0,s}(X_*-X_0)+r e(1-|z|^2),\\
 \Phi^*d\mu_G
  &=2e^2\sqrt{\det G(s)}\sqrt{\det C}\,(1-|z|^2)
        \,ds\,d^2z\,dr.
\end{aligned}\tag{PW4}
```

Indeed the lower v bound is the first cost and the upper bound is
`v1-S_s,u1(X1-X)`. PW3 gives exactly the remaining clock width. Both boundary
cones, their intersection and their moving closing disk are retained. At either
u endpoint the possible vertical boundary segment has zero four-volume, as do
the null cone boundaries; the entire interior and all neighborhoods of those
segments are integrated. PW4's Jacobian follows by the triangular order
`u, X, v`; derivatives of the moving center do not change it. Integrating r and
the disk, whose `integral(1-|z|^2)=pi/2`, gives

```math
\begin{aligned}
 V_G(p,q)&=\pi e^2\int_{u_0}^{u_1}
       \sqrt{\det G(s)}\sqrt{\det C(s)}\,ds.
\end{aligned}\tag{PW5}
```

### Two tips, noncommuting matrices, and the apparently singular direction

For `0<=t<=1`, write s=u0+tL. Define interval averages by their nonsingular
integral representation, **including zero length**:

```math
\begin{aligned}
 \overline B(a,\ell)&=\int_0^1 G(a+r\ell)^{-1}\,dr,\\
 A_0&=\overline B(u_0,tL), &
 A_1&=\overline B(u_0+tL,(1-t)L), &
 A&=\overline B(u_0,L),\\
 C&=L t(1-t)\,A_0 A^{-1} A_1, &
 \det C&=L^2t^2(1-t)^2\frac{\det A_0\det A_1}{\det A}.
\end{aligned}\tag{PW6}
```

The matrix identity follows from PW3 and `A=t*A0+(1-t)*A1`; it does **not**
reorder matrix factors. Its product is symmetric positive because it equals
C divided by the positive scalar. Eigenvalue comparison in
`C^-1=B0^-1+B1^-1` bounds that quotient above and below uniformly. All the
averages and determinant ratios are smooth at **both** t tips, and at L=0,
with bounds for every fixed derivative order on a compact u range. Thus the
only tip weight in the volume is the explicit integrable `t*(1-t)`.

For L bounded below, PW4 also has the required bounded derivatives in
`h=sqrt(e)`: X is affine and v quadratic in h. The apparently singular
quadratic coefficient is `C^(1/2) B0^-1 C^(1/2)`, bounded by I since
`C^-1>=B0^-1`. The cross coefficient is `D^T B^-1 C^(1/2)`, bounded through
both tips. Reflection is z to -z. These facts address the two longitudinal
ends, not just a central slice.

It would nevertheless be incorrect to assert uniformity of these h derivatives
as L tends to zero: e, `B^-1 D`, and the slice parametrization are then badly
scaled. Long pairs can have L arbitrarily small near the parallel generator
`partial_v`; a temporal cutoff does **not** exclude them. Instead introduce the
geometric endpoint phase Q below and cancel every L factor in PW5 exactly:

```math
\begin{aligned}
 Q&=2L(v_1-v_0)-D^T A^{-1}D=2Le,\\
 V_G(p,q)&=Q^2 H(u_0,L),\\
 H(u_0,L)&=\frac\pi4\int_0^1 t(1-t)\sqrt{\det G(u_0+tL)}
       \sqrt{\frac{\det A_0\det A_1}{\det A}}\,dt,\\
 H(u_0,0)&=\pi/24, &
 \frac{\pi m}{24\Lambda}&\le H\le\frac{\pi\Lambda}{24m}.
\end{aligned}\tag{PW7}
```

The constants and all needed derivatives are bounded on each compact endpoint
range, **uniformly down to L=0**. This follows by differentiating the averaged
matrices on the fixed t interval, using the positive eigenvalue margin; there
is no negative power of t, 1-t or L. Explicitly, `C/(L*t*(1-t))` has eigenvalues
between `1/Lambda` and `1/m`, while `sqrt(det G)` lies between m and Lambda;
integrating `t*(1-t)` gives the displayed positive bounds. The formula even
extends smoothly to small
negative L as a coefficient formula, not as a future-interval assertion.
At L=0 its determinant factor is exactly one, explaining the flat constant.
No logarithmic tip remainder is being ignored: the *exact whole volume*, not
an interior expansion, has been integrated before differentiation.

## 4. All directions, moving contacts and the critical signed bound

In `(T,Z,X)` coordinates PW1 is `dT^2-dZ^2-dX^T G X`. Causal speeds obey
`|d(Z,X)/dT|<=max(1,m^(-1/2))`. T is temporal; finite-T causal diamonds are
bounded and closed, and any inextendible causal curve has unbounded T in each
direction (a finite endpoint limit would extend it). Hence the ambient is
globally hyperbolic with T Cauchy. On the compact region all measures are finite
and smooth.

The actual long-null relation is smooth, including the apparently excluded
parallel generator. For L>0, `partial_(v1) Q=2L>0`. At L=0, future null pairs
have `D=0`, `v1-v0>0`, and `partial_L Q=2*(v1-v0)>0`. Conversely, on the
future branch `T(q)-T(p)>0`, `Q>=0` forces L>=0: L and the v gap cannot have
opposite signs, nor can both be negative. At L=0 it forces D=0. Thus **no extra
L-boundary** has to be appended to the phase collar. PW7 and
`w=sqrt(V)=Q*sqrt(H)` give a smooth phase coordinate with nonzero differential
on the entire fixed-positive-gap null relation. A finite cover and compactness
supply uniform inverses; the parallel-null collar, not just its measure-zero
axis, is included. Strictly timelike compact complements have a positive
physical phase floor.

### True face and shell intersections

A long-null source cannot lie on the future face or on a joint, and a long-null
target cannot lie on the past face or on a joint. A timelike face conormal is
strictly signed on future causal vectors. A causal curve in the closure would
therefore immediately leave the region at such a forbidden endpoint. Taking
limits of long curves in a compact causal enclosure proves positive clearance
from these forbidden faces. This excludes **no short joint collar**.

The only active true contacts are the source past face and target future face.
On the null relation their differentials are independent: target displacement
along its nonzero null generator changes the target face function strictly,
without changing the source face function. Source variation then handles the
source contact. This argument uses the actual order/null hypersurface just
proved, not a flat substitution.

Use the physical shell `T(q)-T(p)=delta`. At one-face shell contacts, in local
null coordinates `(p,r,n)` for small r, the face differential has a nonzero
source component whereas the shell has leading differential `dT(k) dr`.
At simultaneous two-face shell contacts, causal speed control makes the
endpoints close when delta is small. They must approach their common joint;
face pieces away from that joint are separated. The three leading differentials
are `alpha_- dp`, `alpha_+ dp+alpha_+(k) dr`, and `dT(k) dr`. Independent joint
conormals and `dT(k)>0` give rank three. Compactness and the small-r errors
preserve it for all sufficiently small **fixed** delta. Empty-joint members
have no such two-face shell contact for small delta. This is the intrinsic
GC6 argument with its hypotheses proved here, including simultaneous contacts.

Together with w, the active face/shell functions are therefore smooth local
coordinates. A finite compactly supported partition and this inverse change
of variables straighten the **moving** integration domains into fixed orthants.
Differentiate the entire pulled-back density, including
`sqrt(det G(u0))*sqrt(det G(u1))`, both endpoint partition fields, and every
contact Jacobian. Smoothness gives the actual long pushforward density

```math
\begin{aligned}
 b(w)&=b_0+b_1w+b_2w^2+O(w^3),\\
 K_4(z)&=(1-9z+8z^2-\tfrac43z^3)e^{-z},\\
 \int_0^\infty z^jK_4(z^2)\,dz&=0\qquad(j=0,1,2),\\
 \rho^{3/2}\int_{M\times M\,;\,p\prec q\,;\,\Delta T\ge\delta}
 K_4(\rho V_G(p,q))\,d\mu_G(p)d\mu_G(q)&=O(\rho^{-1/2}).
\end{aligned}\tag{PW8}
```

For the last line subtract the degree-two polynomial on the full positive
half-line using the three signed moments. Its beyond-cap tails and the
positive-volume complement are exponential. For the remainder set
`z=sqrt(rho)*w`; its bound is a constant times
`rho^(-1/2)*integral z^3*abs(K4(z^2)) dz`. This is the required **signed**
critical estimate. Absolute-value bounds on the un-subtracted polynomial would
fail. Constants may depend on the fixed cutoff; no shrinking-cutoff claim or
rate for the **complete** action is made.

Every original endpoint partition is restored by the full ordered double sum.
Artificial derivative terms cancel only in that sum, as in G4; restricting to
same-chart partners would be a different observable. No physical union is
replaced by adding branch volumes, no cutoff complement is discarded, and no
new subtraction enters the action.

## 5. Complete action, independent curvature and separate probability

Choose delta positive below both the contact threshold and S30's short
threshold for the fixed metric/region. S30 includes the physical point once;
PW8 supplies the complete long remainder with the original normalization.
The deterministic limit is therefore the **independently defined**
`integral R/2 + integral_J coth(theta) dA_G`. This is an application of the
existing short theorem, not a claim that PW8 alone computes a joint.

Direct Christoffel contraction for PW1 has Ricci tensor supported only in the
uu component; `g^(uu)=0`, so R=0 in either Riemann sign convention. In the
contract's convention that component is
`tr(G^-1 G'')/2 - tr(G^-1 G' G^-1 G')/4`.
The Weyl tensor need not vanish. The target is thus the actual G-joint term;
zero scalar curvature is not flatness, an omitted bulk, or a renormalization.

Only now construct the law: restrict PW1's smooth positive volume to M,
which is finite and atomless. The order is closed/measurable. Off-diagonal null
sets are hypersurfaces by Q above; the parallel generator and diagonal are
lower-dimensional, all of zero volume. Ambient containment identifies the
restricted interval parameter with PW5/PW7, including all partners. Mecke and
Poisson interval counts, with finite second moment controlling the finite signed
layer sum, give the original finite-density equality
`E A_disc(rho,4) = A(rho,4)`. Transfer the deterministic limit through that exact
identity. No law, coupling, sample-wise convergence, variance or new geometric
probability oracle is introduced.

## 6. A fixed region under genuine non-conformal deformations

This verifies that the stability assertion includes actual admissible regions,
not a matrix ansatz with unproved boundary hypotheses. Take `abs(epsilon)<epsilon0<1`
and `a(u)=1+epsilon*cos(u)`, `G=diag(a(u)^2,1)`. The metric bounds hold globally.
Its transverse tidal eigenvalues are `a''/a` and zero (up to the common
curvature-convention sign). Their nonzero trace-free part wherever
`epsilon*cos(u)!=0` gives nonzero Weyl tensor: for epsilon nonzero this is
**not** conformally related to the flat epsilon-zero member, even after a
coordinate change.

For spatial coordinates `Y=(x,y,Z)`, choose `s>0`, `eta>0` with
`eta+s<1-epsilon0`. Fix the same region for every epsilon:

```math
\begin{aligned}
 f(Y)&=\eta Z, & h(Y)&=s(1-|Y|^2),\\
 M&=\{\,|Y|\lt1,\ f-h/2\lt T\lt f+h/2\,\},\\
 J&=\{\,|Y|=1,\ T=\eta Z\,\}, &
 u_J&=(\eta-1)Z/\sqrt2.
\end{aligned}\tag{PW9}
```

The global envelopes `f +/- s*(1-|Y|^2)_+/2` have Euclidean Lipschitz constants
at most eta+s. The speed bound is at most `1/(1-epsilon0)`. Their strict causal
monotonicity proves ambient containment, past/future character and achronality.
The raw faces near the unit ball are smooth spacelike, meet only at the regular
sphere joint, and have independent conormals because s>0. Thus the entire G-SS
contract, not just a local slope test, holds simultaneously. All geometry and
epsilon are fixed before density varies.

Compute the target directly. On the unit sphere let
`A=1-eta^2`, `d=x^2/a_J^2+y^2+Z^2`, `a_J=a(u_J)`.
The face slopes are `eta*e_Z +/- s*Y`; inverse spatial metric is
`diag(a_J^(-2),1,1)`. Normal contraction and the determinant of the induced
joint metric give

```math
\begin{aligned}
 \coth\theta&=\frac{A+s^2d}{2s\sqrt{Ad+\eta^2Z^2}}, &
 dA_G&=a_J\sqrt{Ad+\eta^2Z^2}\,dS,\\
 \mathcal T_{\mathrm{SS}}
 &=\frac{\pi}{s}\int_{-1}^{1} a_J\left[
 A+s^2 Z^2+\frac{s^2}{2}(1-Z^2)(1+a_J^{-2})\right]dZ.
\end{aligned}\tag{PW10}
```

For the area identity restrict `diag(a_J^2,1,A)` to the Euclidean unit-sphere
tangent planes; its cofactor determinant is the displayed factor. Azimuthal
integration gives the second line. No phase coefficient or action fit enters
this calculation. At epsilon=0 it reduces to `2*pi*(A+s^2)/s`, agreeing with
GC8 at b=0. For nonzero epsilon the actual metric factor and normal angle vary;
replacing them by their flat values changes the target. This gives required
nonempty-joint coverage with a genuinely non-conformal changing causal order.
Scalar bulk is identically zero throughout this class, and is stated as such.

## 7. Adversarial estimate audit and verification boundary

The following are explicit challenges to the decisive proof, not claimed
independent review. They document limitations rather than silently repairing a
purported general perturbation theorem.

| Challenge / tempting invalid step | Resolution or retained limitation |
| --- | --- |
| Use the flat interval cost with a density evaluated at the source | PW2 minimizes the full matrix-weighted energy; PW4 has the interior density at s. Variable/noncommuting profiles change the phase. Diagnostics compare separate clock integration and the transformed volume. |
| Treat B0 and B1 as commuting | PW3 uses the symmetric parallel sum. PW6 preserves factor order; a rotating-eigenframe diagnostic is required, not only diagonal profiles. |
| Differentiate an interior expansion through a tip and drop the logarithm | PW5 is exact on the whole interval. The averaged-matrix formula yields the factored `t*(1-t)` before differentiation. No finite asymptotic truncation or unaccounted tip domain is used. |
| Assume fixed temporal gap implies L is bounded below | False. PW7 and the nonzero Q differential at L=0 retain the entire parallel-null collar. The PW4 point-map proof is **not** promoted to uniform RPL compliance there. |
| Infer arbitrary non-conformal openness from a positive determinant | Not done. Global strict quadratic minimization is the operative structure. Section 8 explains exactly what fails without it. |
| Freeze endpoint domains or delete simultaneous contacts | Section 4 proves the true face/shell ranks before differentiating the full pulled-back density. Null faces would invalidate that proof and are outside PW-4. |
| Infer the complete limit or target from three zero moments | PW8 is only long. S30, at one common fixed cutoff with point once, supplies short; PW10 computes the target independently. |
| Claim a failed bound establishes instability | No such inference. Outside this class no surviving contribution has been derived here. #164 alone retains its independently matched complete obstruction. |

`plane_wave_geometry.py` and its tests are floating/symbolic **diagnostics** of
these formulas, including negative controls. They are not a certified uniform
remainder, a proof by sampling or full-action numerical certification. This
written argument relies on the separately written S30; no new Lean proof,
regenerated #164 certificate or human mathematical approval is claimed.

## 8. Further generalization attempted: the precise remaining blocker

The matrix-profile theorem is not merely a constant-coefficient calibration:
G may rotate its eigendirections arbitrarily and have arbitrary smooth u
dependence, with no small-curvature assumption. Positivity controls every path
by a global quadratic energy and supplies the exact cancellation of all tip
and parallel-direction denominators in PW7. This explains a stable mechanism
under genuinely changing causal cones. It does not decide stability under
changes of the transverse dependence, lapse, shift or topology.

For a general null-geodesic tube, the natural next attempt is a Penrose-type
rescaling: keep the longitudinal coordinate, scale screen coordinates by h
and the conjugate null coordinate by h squared, and divide the metric by h
squared. On a fixed tube in null Fermi coordinates the candidate limiting
metric is a quadratic plane wave, not in general Minkowski. A positive
Dirichlet screen index form would make its limiting lens bounded, and the
present calculation describes that reference lens where a positive Rosen
frame exists. This improves the earlier purely central optical-index proposal.

It is **not yet a proof for perturbed intrinsic metrics**. One must show that
*every point of the actual interval* lies in a fixed rescaled tube before
using smooth dependence of its cones. A unique central ray or a nonzero Jacobi
determinant does not provide that parabolic containment. Excursions, competing
minimizers and a degenerating endpoint-direction chart must all be controlled;
then the two moving cone boundaries must admit a uniformly differentiable
whole-domain resolution through both tips and their mutual contact. PW2's
exact completion of squares supplies all of this for matrix profiles; it is
lost for a general transverse-dependent metric. An estimate for a selected ray
would simply reintroduce the unproved premise.

The next missing sufficient output can be stated sharply: derive from intrinsic
metric data a uniform whole-interval parabolic containment and a dominated
rescaled volume remainder of critical order, jointly in endpoint direction and
both tip variables, with the real minimum/union selection and true boundary
contacts. The old interior `integral ds/s` bound is neither that estimate nor a
physical logarithmic coefficient. This continuation resolves it **exactly for
matrix profiles**, not for arbitrary Hadamard optical metrics, conjugate/cut
contacts or generic metric perturbations. No actual new instability is claimed
without a complete-action calculation. This is a stopping blocker for broader
coverage, not an unexplained permanent draft or a new exhaustive-classification
requirement for #81.

## 9. Consolidated scope and original-acceptance crosswalk

Read the source-backed [full #81 crosswalk](geometric-long-cancellation.md#5-assessment-against-81s-original-acceptance-matrix)
and the [live original acceptance checklist](https://github.com/q5m-ai/causal-set-emergence/issues/81).
The delivery now has a coherent hierarchy:

- **Established in writing:** SW1–SW14 remove sphere-independence; RPL-4 derives
  a sufficient singular-lens criterion; FCDC-4 discharges its regular conformal
  whole-diamond case; PW-4 proves non-conformal matrix-profile stability by an
  exact weaker phase route, with arbitrary G-SS faces and nonempty joints.
- **Preserved:** #164's CO1–CO16 complete obstruction, model certificate and
  audit; #165/#166 and all integrated predecessors. #151 remains completed
  through its negative-resolution route, not reopened by this continuation.
- **Exploratory only:** the last section's general rescaling route, intrinsic
  whole-tube containment and simultaneous singular/true-joint resolution.
- **Still required under #81:** arbitrary curved 2D/3D; broader corrected
  metric/dimension coverage; focusing/cut/joint combinations outside these
  proved classes. PW-4 adds no all-dimensional or arbitrary-metric theorem.
- **Separately owned:** #154 → #155 → #156 and #169 null/mixed work. The worker's
  [#171](https://github.com/q5m-ai/causal-set-emergence/pull/171) has an unmerged
  dimensional cone-ending theorem and curved characteristic-contact blocker;
  it is coordination context, not an input to this proof. No G-SS contact
  argument is applied to a null face. [Continuation coordination](https://github.com/q5m-ai/causal-set-emergence/issues/156#issuecomment-6154817919).
- **Still required for acceptance:** independent mathematical/physical human
  review, provenance and intended-statement/formalization scrutiny #94/#86.

**#81/#24's original completion criteria remain unmet.** Readiness of #167
means a stable, validated, explicitly scoped contribution is available for
review, not acceptance of these written proofs or closure of the general
research task. No action, target, order, either measure, law, cutoff convention,
physical partner, union or issue scope is changed; no agent, merge, deployment
or closure is authorized by this note.
