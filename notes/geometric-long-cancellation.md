# Geometric sufficient cancellation and the remaining corrected theorem (#81)

**Written sufficient theorem, with two geometrically discharged branches; not
universal coverage, a necessary condition, or independent acceptance.** The
[sphere-dependent theorem](sphere-dependent-conformal-limit.md) is one branch.
The other, below, permits nonempty variable-angle joints and is not restricted
to a sphere-circle product or to time-dependent conformal factors. The
[non-conformal continuation PW-4](nonconformal-plane-wave-limit.md) subsequently
proves the same cancellation conclusion for arbitrary positive transverse-matrix
plane-wave profiles, by an exact phase construction rather than claiming every
RPL point-map bound. It includes both tips, the parallel-null collar and
simultaneous spacelike-face/cutoff contacts.

Source baseline: explicitly fetched `origin/issue-81-general-coverage` at
`41cf2c35378cf91c1c2d3651f8dd689370662bdf`, containing #164/#165/#166.
Read against [G-SS](general-contract.md), [#151's negative resolution](issue-151-resolution.md)
and the live [#81 acceptance matrix](https://github.com/q5m-ai/causal-set-emergence/issues/81).
No old theorem, independent target, order, measure, law, certificate or issue
scope is changed. Closed #151 is not reopened. #81 remains the owner of the
broader corrected curved theorem; assigning an owner does not prove a row.

## 1. What the sufficient condition says about geometry

The contrast between the sphere lens and the quartic lens is not “caustic
versus no caustic.” It is the interaction of **the shape of a physical thin
interval**, **the amount of endpoint pair space approaching that shape**, and
**the motion of the true endpoint contacts**. We give a sufficient condition
on those geometric objects, without prescribing a primitive jet, Mellin
coefficient, action limit or cancellation identity.

### Resolved physical lens condition (RPL), in dimension four

Fix a smooth G-SS region. Require the following geometric construction for
every sufficiently small **fixed positive** temporal cutoff. Its constants and
charts may depend on that cutoff; no uniform shrinking-cutoff estimate is
required or used. This permits choosing a common cutoff below the short
threshold after any fixed conformal change. All objects below are independent
of density. Work on a compact causal tube.
Require an exhaustive finite pair-chart cover near the long null relation,
with a smooth pair partition. A chart can contain a continuum of null paths;
this is **not** a finite-geodesic-branch hypothesis. Outside those charts,
compactness must give strictly timelike pairs with a positive physical volume
floor. All true boundaries, chart overlaps and phase-cap complements remain.

A regular chart has a geometric causal-excess coordinate e, vanishing on
null pairs, and compact remaining parameters zeta. A singular chart also has
a nonnegative geometric degeneration coordinate a. These coordinates come
from endpoint positions or a resolved null incidence relation, **not from
reparameterizing an unknown volume function**. On a singular chart require:

1. **Endpoint geometry.** The actual pair volume form, after straightening
   its moving contacts, is `a^nu*j(a,e,zeta) da de dLambda(zeta)`. Lambda is
   a fixed finite positive measure, allowed to contain a closing factor such
   as `(1-v²) dv`. After this contact straightening, the integration ranges in
   a, e and zeta are fixed boxes (with smooth chart cutoffs in the density),
   not moving omitted portions. The density is bounded on the full chart. On
   `0<=e<=eta*a^beta`, its derivatives through order three in `E=e/a^beta`
   are bounded uniformly and are continuous at E=0 for each a>0. The endpoint
   maps have the analogous bounds, so multiplication by any fixed smooth
   endpoint fields preserves this property. Actual corner/contact coordinates
   must give this form; a nonsmooth closing weight cannot be frozen.
2. **Whole-interval point maps.** For `e=a^beta*h²`, `|h|<=sqrt(eta)`, there
   is a map Phi from a fixed finite-measure reference domain D onto the
   **whole physical interval**, one-to-one almost everywhere for h>0, with
   physical volume form

   ```math
   \begin{aligned}
   \Phi_{a,h,\zeta}^*d\mu_g
    &=a^{2\beta-\sigma}h^4 J(a,h,\zeta,\xi)\,d\lambda(\xi).
   \end{aligned}\tag{GC1}
   ```

   In fixed smooth ambient coordinate patches, Phi has uniform h derivative
   bounds through order eight. J and its h derivatives through order eight
   have a common integrable dominator on D, uniform in the other parameters.
   J is nonnegative, its integral at h=0 is bounded below by a
   positive constant, and the maps obey a measure-preserving reflection
   `Phi(a,-h,zeta,xi)=Phi(a,h,zeta,R xi)`, with the same identity for J.
   This reflection is of reference coordinates, not a symmetry of the metric
   density. A finite disjoint reference partition is allowed. Multiplicity
   must be actual point multiplicity; overlapping geodesic tubes do not
   satisfy this clause by addition.
3. **Outer geometric noncollapse.** For `e>=eta*a^beta` in the retained small
   box, exhibit a subset of the actual interval by a one-to-one point map
   from a fixed positive-measure domain, whose volume Jacobian is bounded
   below by `c*e^(2*lambda/beta)`, where `lambda=beta-sigma/2>0`.
   All its image points must belong to the interval. This is a geometric
   inclusion/Jacobian test, not a desired sublevel estimate. Constants are
   uniform over zeta and the closing faces.
4. **Strict endpoint-abundance inequality.** The derived geometric exponents
   satisfy

   ```math
   \begin{aligned}
   &0\lt\beta\lt3\lambda,\qquad
   \lambda=\beta-\sigma/2,\\
   &\nu+\beta-3\lambda>-1.
   \end{aligned}\tag{GC2}
   ```

For regular charts omit a, use `e=h²`, pullback `e² J d lambda`, and smooth
contact density in e. Require the same reflection, positive integral and
bounded derivatives. A positive phase floor deals with the rest of the chart.
A point map need not be a spacetime coordinate chart at h=0: the interval
collapses there. Its **rescaled** bounds are what is required.

These are statements about endpoint incidence, maps of spacetime points,
physical volume forms, contained subsets and boundary transversality. They
can be checked without choosing the BDG kernel. In particular they are not
an assumed expansion of the volume pushforward. They are preserved under
smooth bounded coordinate changes. They are a sufficient geometric class,
not a new field in G-SS or a claim that every metric admits such a resolution.

### The theorem and proof

**Theorem RPL-4.** Every 4D G-SS member satisfying this geometric condition has
zero complete fixed-cutoff long response. Its canonical deterministic action
converges to its independently defined curvature-plus-joint target. The actual
Poisson expectation converges separately to the same target. The conclusions
also hold after any fixed smooth positive conformal rescaling on the compact
causal tube, with its **new** physical volume and independent target.

To prove it, integrate GC1, not a guessed phase model. The reflection makes
`integral J` smooth and even in h. Taylor's integral remainder, with the eight
h derivatives, gives a bounded C4 function H of `E=h²`, positive uniformly
on a smaller fixed wedge. Therefore the actual volume satisfies

```math
\begin{aligned}
V_g(a,e,\zeta)&=e^2a^{-\sigma}H(a,e/a^\beta,\zeta),\\
0\lt c&\le H\le C,&|\partial_E^jH|&\le C_j\quad(0\le j\le4).
\end{aligned}\tag{GC3}
```

This is a **derived** phase estimate. The outer contained subset gives
`V_g>=c*e^(2*lambda/beta)`. In particular every sufficiently small sublevel
`V_g<=w²`, with `w<=kappa*a^lambda`, is inside the regular wedge. There
`w/a^lambda=E*sqrt(H)` has a uniform inverse. If
`w>=kappa*a^lambda`, all sublevel points satisfy
`e<=C*w^(beta/lambda)`: inside the wedge this follows from its width, and
outside from the contained subset. There is no assumed global inverse.

Integrate the actual endpoint density up to that sublevel, and call this
one-fibre primitive f. Its coefficients are produced by inverse Taylor and
integration of j, as explicitly in RC10, not stipulated. Rescaling yields

```math
\begin{aligned}
|c_i(a,\zeta)|&\le C_i a^{\beta-i\lambda}\quad(i=1,2,3),\\
\left|a^\nu\frac{f-\sum_{i=1}^3 c_iw^i}{w^3}\right|
 &\le C a^{\nu+\beta-3\lambda},\\
N(w)&=n_1w+n_2w^2+n_3w^3+o(w^3).
\end{aligned}\tag{GC4}
```

On the wedge use the uniform inverse; off it use the sublevel width and
`beta/lambda<3`, including all subtracted terms. The quotient tends to zero
pointwise for a>0 and is summably dominated by GC2. Tonelli for the geometric
primitive and dominated convergence prove the last line. Regular charts
instead have a smooth density in w. Finite sums preserve these statements;
the physical union, not a sum of overlapping lens volumes, was used throughout.

The actual three 4D signed moments kill the three differentiated polynomial
terms. Stieltjes integration by parts controls the remainder with
`z^4*abs(K_4'(z²))`; above-cap pieces and polynomial tails are exponentially
small. Thus the complete long response vanishes. Combine with S30 at the
**same compatible fixed cutoff**, allocating the point only to short. The
independent bulk and joint are those of G-SS, not definitions by a limit.
Finally apply the finite-density measured-order bridge with the actual finite
atomless measure and contained ambient intervals. No sample-wise result follows.

For conformal stability, the point sets and maps remain the same, but GC1's
J is replaced by `Omega(Phi)^4*J` and the pair density by both endpoint
factors. Compact positive bounds preserve noncollapse, while the h derivative
bounds on Phi prove the new C8 bounds by the chain rule. The reflection acts
on Phi itself and therefore preserves evenness for **arbitrary** Omega.
Spacelike faces, their contact incidence and ambient containment remain;
curvature and induced joint area must be recalculated. This is a proof of
weighted stability, not an inference from conformal preservation of order.

## 2. Discharge at the focusing sphere, and comparison with the obstruction

For the sphere-circle slab, `a=pi-theta`, `e=u-theta`, and SW7 give
`(nu,beta,sigma)=(1,1,1/2)`. The point map is the actual flat diamond map
followed by SW5 and the bounded time/circle boost. SW8 proves its rescaled
bounds, including the longitudinal tips; `sqrt(a)*Q_theta` supplies J's
bounds and positive integral. Reflection is `(B2,B3)->(-B2,-B3)`.
The closing weight is factored explicitly in SW7, before differentiating.

The noncollapse requirement can be checked by actual inclusions, not just
by quoting a phase bound. In the regular wedge use a fixed central reference
subdiamond where J has positive mass. For `eta*a<=e<=4*a`, monotonicity in
boosted time contains the regular lens at excess `eta*a/2`, of volume at
least `c*a^(3/2)`, comparable to `e^(3/2)` on this range. For `e>=4*a`, the
endpoint triangle inequality contains the antipodal diamond with excess
`e-2*a>=e/2`. In its central meridian band, a circle interval of width
`c*sqrt(e)` and clock thickness `c*e` is a contained coordinate box, uniformly
in azimuth. Its Jacobian gives `c*e^(3/2)`. The bounded boost transports the
subsets into the actual interval; moving sources and closing fibres stay in
a compact tube. Positive conformal factors preserve the lower bound. This
verifies clause 3 with `2*lambda/beta=3/2`.

The resulting majorant is `a^(-1/4)`, integrable. Thus RPL-4 is independently
discharged for all SW1 factors, not offered as an extra unproved assumption
in that theorem. It explains why angular density variation changes the phase
coefficients but not the strict summability margin.

For #164's **actual** quartic primary wedge, the derived geometry instead
gives `(nu,beta,sigma)=(3/2,2,1/2)`: the candidate cubic majorant is
`a^(-7/4)`. This fails the sufficient inequality. Failure is **not** the
negative proof. CO5–CO16 separately match both wells, their overlap and moving
opening/closing layers, and the model certificate supplies its own bounded
sign evidence. The actual matched pole is 9/7, with nonzero kernel multiplier
22/343, giving the preserved complete action
`-D*rho^(3/14)+O(rho^(1/6))`. No certificate or coefficient is regenerated or
modified here. A pure transition scaling without that matching would not
establish its sign or even its survival.

The borderline equality in GC2 remains undecided by this method. Logarithmic
terms or signed cancellation between matched pieces can matter there. RPL-4
is neither necessary nor a classification of all caustics.

## 3. Beyond the product: faithful conformal diamond covers

Here is a separate geometric condition whose **regular** RPL clauses can be
proved, rather than assumed from the words “no caustics.”

**Faithful conformal diamond cover (FCDC).** At each sufficiently small fixed
positive temporal cutoff, a compact neighborhood of the long-null endpoint
relation admits finitely many endpoint neighborhoods such
that each neighborhood's entire ambient intervals lie in an open spacetime
patch U with a smooth conformal Minkowski chart. The chart maps each whole
interval bijectively onto the corresponding entire flat diamond, with its
actual endpoints. Shrink the endpoint neighborhoods so the intervals and
coordinate extensions needed for differentiation stay in compact subpatches
and the conformal factors have positive bounds there.

This is a condition on actual geometry and interval containment. A local
conformal chart at the source or target alone does not satisfy it. Neither
global hyperbolicity nor a nonsingular endpoint exponential map supplies it.
It permits different interval patches for different ordered pairs, including
pairs whose original source/target atlas labels differ.

**Corollary FCDC-4.** Every smooth 4D G-SS region with FCDC has the canonical
complete deterministic and separate expected curvature-plus-joint limits,
for arbitrary fixed smooth positive conformal factors. Nonempty joints and
all finite ordered endpoint partitions are included.

### Derive the actual phase, not just a causal-coordinate reduction

On such a patch write `g=Omega² eta`. Let x be the source, r>0 the spatial
separation, n its direction, `q=tau²-r²`, and use the full boosted diamond D0.
With B_parallel and B_perp relative to n, the actual map is

```math
\begin{aligned}
t_*&=t_x+\tau(1/2+A)+rB_{\parallel},\\
\mathbf x_*&=\mathbf x+r(1/2+A)n+\tau B_{\parallel}n
                        +\sqrt q\,B_{\perp},\\
V_g(x,y)&=q^2\int_{D_0}\Omega(t_*,\mathbf x_*)^4\,dA\,dB.
\end{aligned}\tag{GC5}
```

Faithfulness is needed for the last equality. Long-null compactness keeps
r bounded below on each retained patch. Reflecting B_perp makes the integral
even in sqrt(q). It is smooth in q, with bounded derivatives of any fixed
order and a positive leading value. The actual inverse of `w=q*sqrt(H)`
is therefore smooth; it is not the flat inverse with a frozen density.
The map and Jacobian directly satisfy the regular RPL clauses.

### True contacts, joints and the fixed temporal shell

It remains to verify endpoint-domain regularity; a smooth phase alone is
not enough. On the compact long-null relation a source can meet only its
past face and a target only its future face, not a joint. Indeed a future
causal vector at a spacelike future face points strictly out of the region;
a past causal vector at a past face does likewise. At a joint both apply.
If a sequence of interior long causal pairs approached such a forbidden
endpoint, compact causal control gives a limiting causal curve in the closure
with nonzero temporal duration, contradicting that local strict exclusion.
Consequently the forbidden faces and joint have positive clearance on each
fixed long-null compact set. This does **not** discard the short joint collar.

The remaining two possible face constraints are independent on the null
pair manifold: vary the target along the null generator to change its future
face defining function (a timelike conormal has nonzero pairing with every
nonzero null vector), while leaving the source constraint fixed. With the
source face alone, source time is transverse. Compactness gives uniform lower
bounds for these local coordinate inverses.

At the cutoff shell there is an additional constraint `t(y)-t(x)=delta`.
With at most one face, its null-generator derivative and the face conormal
are independent for small delta. If both true faces are active there, G3's
whole-curve bound makes their endpoints close. For small delta they must
lie near the joint: the compact face pieces away from the joint are separated.
In null coordinates `(x,r,n)`, at the limiting joint with r=0 the differentials
of the two face functions and the temporal gap have leading forms

```math
\begin{aligned}
&\alpha_-\,dx,\\
&\alpha_+\,dx+\alpha_+(k)\,dr,\\
&dt(k)\,dr,\qquad k=(1,n).
\end{aligned}\tag{GC6}
```

The two joint conormals are linearly independent and `dt(k)>0`; the rank is
three. Compactness and the O(r) error preserve the rank at every sufficiently
small fixed cutoff. With empty joint there is no two-face shell contact for
such a cutoff. This verifies, not assumes, the relevant global-partition case.

Now use the actual phase w together with the active face/cutoff functions as
coordinates. Their rank at w=0 persists on a common small collar. Smooth
compactly supported pair partitions and the implicit function theorem turn
the domains into fixed orthants. Differentiate the full pulled-back density,
including both endpoint volumes and every moving-boundary Jacobian. It is C3
in w with uniform bounds. Hence the actual off-diagonal long density is
`b0+b1*w+b2*w²+O(w³)`. The entire ordered pair cover, not just its diagonal
labels, has the signed zero response proved above. Positive-volume complements
are retained by compactness. No nonempty-joint contribution has been assigned
to long: S30 retains its actual short joint and compensating face flux.

This completes the FCDC corollary with a compatible fixed temporal cutoff.
Any original source/target partitions restore exactly by G4; their derivative
sums vanish only after the full ordered double sum. Probability uses the
actual geometric measure and order exactly as after SW13, not a new law.

### Nonvacuity, topology and an independently computed variable-angle joint

Every G-SS region in Minkowski space, with **arbitrary smooth positive**
spacetime-dependent conformal factor on its compact causal enclosure, satisfies
FCDC. This is not a global graph or combined-budget restriction on the region.
A conformal chart whose image is causally convex also suffices. The explicit
unique-whole-interval lift argument for a thin flat torus `2*T<L` supplies
FCDC across its coordinate seams for arbitrary smooth positive factors there.
This is a new written weighted consequence, not a duplicate or recertification
of #166's compiled constant-factor theorem. Thicker quotient intervals with
multiple projected routes are not automatically faithful charts.

For a concrete nonempty-joint member, choose `b>0`, `0<s<1`, and
`0<epsilon<1-s`. In Minkowski coordinates put

```math
\begin{aligned}
f(\mathbf x)&=\epsilon x_1,&h(\mathbf x)&=s(1-|\mathbf x|^2),\\
M&=\{ |\mathbf x|\lt1,\ f-h/2\lt t\lt f+h/2\},&
\Omega&=1+b|\mathbf x|^2. 
\end{aligned}\tag{GC7}
```

The separate global causal envelopes `f ± s*(1-|x|²)_+/2` are strictly
Lipschitz with bound epsilon+s<1; their epigraph/hypograph intersection proves
ambient containment. Raw faces are smooth, their joint is the sphere at
`t=epsilon*x_1`, and the joint conormals are independent since s>0. The metric
has spatially varying curvature. Write `A=1-epsilon²`. Direct normal/Gram
calculation on the joint, with dS ordinary unit-sphere area, gives

```math
\begin{aligned}
\coth\theta&=\frac{A+s^2}{2s\sqrt{A+\epsilon^2 x_1^2}},&
dA_{\eta}&=\sqrt{A+\epsilon^2x_1^2}\,dS,\\
\mathcal J_g&=\frac{2\pi}{s}(A+s^2)(1+b)^2,\\
\frac12\int_M R_g\,d\mu_g
 &=-144\pi b s\left(\frac1{15}+\frac b{35}\right),\\
\mathcal A_{\rho,4},\ \mathbb E A^{\mathrm{disc}}_{\rho,4}
 &\longrightarrow
 \frac{2\pi}{s}(A+s^2)(1+b)^2
 -144\pi b s\left(\frac1{15}+\frac b{35}\right).
\end{aligned}\tag{GC8}
```

The angle varies with x1 when epsilon is nonzero. For the bulk use
`Box_eta Omega=-6b`, `R_g dmu_g/2=3*Omega*Box_eta(Omega) d^4x`, and the
actual time thickness `s*(1-r²)`; the radial integral gives the displayed
negative term. Conformal rescaling multiplies joint area by Omega² and leaves
the normal angle unchanged. None of these target calculations uses an action
fit or a primitive coefficient. The FCDC proof supplies the complete action,
then the original-law expectation separately.

## 4. Genuinely different routes tried, and the sharper remaining blocker

The positive results above do not end the general investigation merely because
a new note can be published. The following comparisons identify what is and
is not controlled by several plausible geometric proposals.

| Proposal / method | What can actually be derived | What is still missing, or why it is insufficient |
| --- | --- | --- |
| Conformal order comparison alone | Same interval sets and positive upper/lower volume comparisons | It does not identify weighted coefficients or their derivatives. SW5/SW8 and GC5 supply the missing **point maps** in the proved classes. Freezing the source density fails even finite interval checks. |
| Pointwise caustic scaling alone | SW10's positive fractional interval coefficient; CO4's quartic scaling | Pair abundance, opening layers and closing/overlap matching decide the normalized signed response. F19's isolated sector and a failed GC2 bound are not counterexamples. |
| Null exponential/Jacobi inverse away from conjugacy | A nonzero screen determinant gives a local inverse on that branch; compact subsets separated from its zero set have bounded inverses | It neither identifies the full physical interval nor bounds the inverse as the branch reaches a minimizing cut/conjugate contact. Endpoint-tip uniformity and all competing branches still require proof. No blanket no-caustics theorem is inferred. |
| Nonpositive-curvature ultrastatic optical metric | The index form along a unique minimizing spatial geodesic controls the transverse quadratic defect; in a Hadamard space distance has no cut locus | Expanding on an interior longitudinal segment does not give uniform high derivatives at the two tips. In distance Hessians the natural bounds contain inverse powers of distance to an endpoint. A complete fixed-domain point map or matched tip estimates for an arbitrary variable-curvature optical metric have **not** been derived here. This route is blocked analytically, not refuted. |
| Finitely many minimizing branches | A finite local list, if actually proved, limits combinatorics | #164 already has at most two relevant minimizers and nevertheless diverges. Physical overlaps, opening gaps and quartic stiffness are not controlled by the count. |
| Ordinary folds / “generic” contacts | A specified nondegenerate local projection normal form controls that projection | It does not by itself give the minimum selection, physical lens union, endpoint measure exponent or boundary-contact rank. Those must be derived; excluding higher contacts from the old core would be a scope change. |
| Convexity | Ambient causal convexity identifies the physical interval parameter and order; faithful conformal diamond containment yields GC5 | Convexity as interval containment alone supplies no rescaled derivative or abundance bound. The admitted compact-Cauchy counterexample slab is causally convex. No conjectural convexity slogan repairs its long response. |
| Einstein equation or energy inequalities | Ricci contraction enters Raychaudhuri's trace focusing equation, and scalar curvature fixes the local bulk term | Trace control is not control of the full screen map, minimum selection, Weyl contribution or endpoint contacts. No sufficient implication to RPL/FCDC has been proved here; no counterexample satisfying an unstated energy condition is claimed. |

The optical-index route has a quantitative endpoint problem, not merely a
missing citation. On an interior segment of length L, a transverse displacement
Y at longitudinal distance s has quadratic broken-distance defect bounded
below by a positive multiple of `L*abs(Y)^2/(s*(L-s))`. This follows from the
nonnegative-curvature-term sign in the Hadamard index form and the elementary
Dirichlet energy minimum. Put `Y=sqrt(e*s*(L-s)/L)*Z`. In spatial dimension
three the two transverse coordinates and clock thickness then give a volume
factor comparable to `e²*s*(L-s)/L`. But the endpoint expansion parameter is
`abs(Y)/s`, of size `sqrt(e/s)`, not uniformly small. Termwise absolute bounds
on the second e derivative of the divided interior integrand can therefore
cost `s*(1/s)^2`: its integral down to s=e is `log(1/e)`. The endpoint domain
`s=O(e)` has physical coordinates of size e and volume of order e to the
fourth, precisely the order at which this derivative needs matching.
This is a failure of that **domination argument**, not a derived nonzero log
coefficient. The exact flat diamond has the same pessimistic bound and no
log at all. Matching both tip domains before differentiation, or constructing
a uniform point map, is necessary before this route can be promoted to a
new geometric theorem.

The material new obstruction to a broader **positive proof**, after the angular
extension, is thus specific: **derive a uniformly controlled resolution of the
whole causal diamond, including both longitudinal tips and simultaneous
minimizing/closing contacts, from intrinsic metric data beyond the verified
conformal/round-lens classes.** A bound for a Jacobi determinant on a selected
ray, a smooth central lens, or a volume comparison is not that resolution.
RPL isolates exactly which geometric maps, densities and contained subsets
would discharge it and explains the strict codimension/scaling margin; it
does not claim those maps exist for arbitrary G-SS metrics.

This is a sharper blocker, not a new exhaustive-classification gate. The
[subsequent PW-4 construction](nonconformal-plane-wave-limit.md#3-the-whole-physical-interval-and-its-tip-resolution)
resolves it for genuinely non-conformal matrix-profile plane waves: exact
quadratic path minimization produces the entire physical lens and a smooth
phase through both tips and the parallel-null direction. It does not establish
RPL's uniform point-map clause at that direction; the weaker direct-phase proof
suffices. No openness under arbitrary ambient metric perturbations is inferred.

The still-unproved broader step is now [whole-interval parabolic containment
and dominated tip/contact resolution](nonconformal-plane-wave-limit.md#8-further-generalization-attempted-the-precise-remaining-blocker)
from intrinsic metric data when that exact quadratic path identity is lost.
Variable-curvature Hadamard optical metrics and matched signed estimates outside
RPL remain different possible routes, not proved branches. No unrelated pilot
issue or unapproved scope decision is created here.

## 5. Assessment against #81's original acceptance matrix

The live issue and its original unchecked obligations are controlling. This
source crosswalk records actual delivery; named ownership is **not discharge**.

| Required row | Source-backed status after this work | Residual obligation / owner |
| --- | --- | --- |
| Flat G-SS 2D–4D | CFT1–CFT4 written universal positive results, preserved; the selected flat 2D/3D/4D and thin-torus compiled results retain their exact scope | No duplicate flat analytic task; intended formalization and scrutiny #86/#94 |
| Arbitrary curved 2D | No universal full theorem or refutation here; G5–G7 and S30 are inputs, not assembly | Dimension-specific full physical interval/contact response and independent target/expectation: **#81** |
| Arbitrary curved 3D | Likewise unresolved; neither flat SmoothPilot3 nor cubic 4D cancellation decides it | Separate critical-order geometry and complete assembly: **#81** |
| General curved 4D | Unconditional claim refuted by unchanged CO1–CO16; SW1–SW14 prove arbitrary sphere-dependent factors; RPL-4 is sufficient; FCDC-4 adds nonempty joints; [PW-4](nonconformal-plane-wave-limit.md) adds genuinely non-conformal matrix-profile stability with both tips, parallel-null collar and spacelike contacts | Derive broader intrinsic metric coverage when exact quadratic path minimization is lost; simultaneous singular/true-joint contacts and arbitrary perturbations remain **#81** |
| Dimensions at least five | CFT's admitted flat counterexample in each dimension; earlier all-dimensional positive subclasses and the separate 7D obstruction preserved | Corrected required geometric/dimensional theorem, not revival of the false universal assertion or classification of every member: **#81** |
| All causal partners / interval regime | SW3/SW4/SW7; GC1's actual point multiplicity; GC5 faithful diamonds; PW2–PW7's actual global path minimum and interval; both endpoint densities, ordered partitions and G2 shell signs | FCDC/Rosen geometry is not automatic for general atlases; unrestricted whole-interval resolution remains **#81** |
| Bulk plus independent joint | SW1/SW2; S30 at a compatible fixed cutoff; GC8's variable-angle nonzero-bulk example; PW9–PW10's fixed nonempty-joint region under non-conformal changes, independent zero scalar bulk and varying induced angle/area | General singular contact/joint combinations beyond the derived rank/resolution cases: **#81** |
| Null/mixed / creases / tips | Not solved by G-SS arguments; #83/#84 and #134 preserved; parallel unmerged #168/#170/#171 supply TT-A/TT-B and dimensional cone results with a curved-null blocker, not inputs here | **#154 → #155 → #156**, including #169's curved single-cone task, retains wider required coverage; no duplication or null singular-limit interchange |
| Mandatory compact nonlocal tests | #166 thin-torus checked result and #139→#152→#153 sphere assembly retained; SW extends the latter with all smooth factors | Neither a successful compact example nor child closure proves general metric/dimension coverage |
| Verification / human acceptance | New analysis is conventional writing with finite diagnostic checks; generic bridge already checked; #164 proof and model certificate unchanged | New concrete asymptotics/weighted geometric specializations are not Lean proofs. Independent human mathematical/physical scrutiny, source provenance and justified formalization remain **#94/#86** |

The original #81 criteria for full required dimension/metric/null/mixed
coverage and #24's corrected-general-theorem completion remain **unmet**.
This work supplies a non-vacuous explanatory sufficient condition and two
proved geometric applications, followed by PW-4's direct non-conformal geometric
producer, rather than the tautology “the long term vanishes.” It does not settle the remaining curved 2D/3D rows or claim the
verified sufficient classes exhaust the required corrected scope.

Shared-interface coordination was posted to the
[#154 worker's issue](https://github.com/q5m-ai/causal-set-emergence/issues/154#issuecomment-6153309865)
before edits. No TT-A/TT-B or dimension/short/Poisson production definitions
are changed. The selected null/mixed branch is not duplicated. All phase
formulas here explicitly use `w=sqrt(V)` in 4D; G5's normalization is unchanged.

## 6. Verification boundary

The proof is the written construction and estimates, not the tests.
`test_sphere_weighted_lenses.py` compares independent physical interval
representations and tests negative controls. `test_geometric_cancellation.py`
checks the conformal diamond measure, independent variable-angle target,
contact ranks, exponent arithmetic and unchanged scaling.
`test_plane_wave_geometry.py` adds whole-clock/point-map comparisons, noncommuting
profiles, both tips, the parallel-null collar, signed moments and independent
joint geometry. These finite checks are neither an interval certificate nor a
full-action numerical solution.
No #164 file or certificate is edited, no Lean input changes, and no new full
Lean audit or independent human review is claimed. PR-local validation and
one bounded stable-head feedback snapshot are recorded on the delivery PR.
No agent launch, merge, deployment, issue closure, or #81/#24 scope edit occurs.

Refs #81, #24, #164, #165, #166, #154, #155, #156, #94, #86.
