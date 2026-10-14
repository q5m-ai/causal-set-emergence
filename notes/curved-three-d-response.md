# Curved 3D: physical response, regular theorem, and remaining coverage (#177)

**Partial written delivery, not the universal curved-3D theorem.** We derive
an unconditional physical-domain reduction and first subtraction for every
original smooth G-SS member; prove a complete deterministic and then expected
limit under an explicit additional whole-interval cover condition; and continue
through a genuinely curved conjugate/cut example in the
[focal sequel](curved-three-d-focusing.md). Neither a local conformal chart nor
flat `SmoothPilot3` implies the theorem. All remaining original curved-3D
quantifiers remain **#177 under #81**. No new FAILS row is asserted.

Integration pin: **`d2cbbc12dbfee6376140a2137013f3d409adfdbf`**. Actual inputs
inspected at that pin are [G-SS and its independent target](general-contract.md),
[dimensional kernels](dimension-kernels.md), [G1–G7](full-partner-globalization.md),
[the short geometry](general-metric-short.md), [S1–S30](general-metric-short-remainders.md),
and [the finite-measure expectation proof](../formal/BoundaryDraft/DimensionMeasureExpectation.lean).
The 4D physical-clock and focal **geometric** arguments are identified where
reused below; their kernels and asymptotic conclusions are not inputs.
#175's unmerged 2D source at `9422627a1815e487aec262b53492a5c442e3fead` was
read for coordination only, not consumed. Shared definitions are unchanged.

## 1. Genuine dimension-three normalization

For the original closed ambient order restricted to M and actual exclusive
interval volume V, the existing recurrence gives

```math
\begin{aligned}
c_3&=\pi/12,&a_3=\beta_3&=2c_3^{2/3}/\Gamma(5/3),\\
K_3(z)&=(1-27z/8+9z^2/8)e^{-z},&
\widehat K_3(s)&=\Gamma(s)(1-3s/2)(1-3s/4),\\
\mathcal A_{\rho,3}&=a_3\rho^{2/3}\mu_g(M)
 -\beta_3\rho^{5/3}\int_{x\preceq y\in M}K_3(\rho V(x,y))\,d\mu_g(x)d\mu_g(y),\\
\int_0^\infty w^jK_3(c_3\rho w^{3/2})\,dw
 &=(c_3\rho)^{-2(j+1)/3}\frac23\Gamma(2(j+1)/3)
       (1-(j+1))(1-(j+1)/2).
\end{aligned}\tag{C3.1}
```

The density moments j=0,1 vanish; j=3/2 **does not**. The sufficient density
remainder is little-o of w to power 3/2, not just little-o of w. In cumulative
form it is little-o of w to power 5/2 after subtracting b1*w+b2*w².
Here w=(V/c3) to power 2/3 is a volume phase, not a geodesic distance.
The layer weights are (1,-27/8,9/4); the last polynomial coefficient is
9/8 because the exclusive count has a factorial. No 4D moment is used.

Fix one smooth Cauchy temporal function tau and a positive sufficiently small
cutoff delta. Strict short receives the **one** physical point; equality
belongs to long. For arbitrary fixed smooth fields chi,phi use G1's weighted
S and L, with the same coefficients and both endpoint measures.

## 2. Unconditional physical clock, through every cut and route union

The geometric clock construction CP3–CP6 in
[curved4-physical-response](curved4-physical-response.md) is dimension independent
up to its final volume exponent. Here is its 3D specialization with that
exponent rederived. Flow a timelike field with d tau=1 through a Cauchy surface
Y, writing q(t,z) and volume j(t,z) dt d sigma(z), with j smooth positive.
Each flow line meets M in an open interval (m-minus,m-plus), or not at all,
by ambient causal convexity. There is no Euclidean graph assumption.

For a source x let a_x(z) be its first causal arrival on that flow line;
for a target y let b_y(z) be its last causal departure. Empty sections contribute
zero. Closedness of the globally hyperbolic order and the timelike flow imply
that these causal sections are closed rays, and their thresholds are Borel.
Thus the **whole physical union**, even with continuously many rays, is

```math
\begin{aligned}
V(x,y)&=\int_Y\mathbf1_{a_x(z)\lt b_y(z)}
       \int_{a_x(z)}^{b_y(z)}j(t,z)\,dt\,d\sigma(z),\\
N^\delta_{\chi,\phi}(w)&=
 \int_M\chi(x)\,d\mu_g(x)
 \int_{\ell\lt m_+}\int_\ell^{\max(\ell,T_{x,z}(c_3w^{3/2}))}
          \phi(q(t,z))j(t,z)\,dt\,d\sigma(z),\\
\ell&=\max(a_x(z),m_-(z),\tau(x)+\delta).
\end{aligned}\tag{C3.2}
```

T is the inverse of actual ambient interval volume along the target clock,
clipped at m-plus, starting at a. It exists: the volume is continuous by
dominated convergence on the compact causal enclosure (cone boundaries are
achronal and volume-null), and strictly increases after arrival by timelike
push-up and a contained open diamond. If the lower clock already exceeds
the volume threshold the inner integral is zero. Closing fibres have their
actual zero length, not a deleted neighborhood. A signed target field stays
inside the integral; its antiderivative is not replaced by a positive part.
Containment makes this ambient volume the restricted volume on actual pairs.

Compact causal control bounds auxiliary spatial speed by a constant times
d tau. If the arrival gap is less than delta/2, a long pair's clock advance
is at least delta/2, giving a uniform positive volume floor. Otherwise take
the last fixed short null segment of an arriving generator. Its local squared
separation from the advanced target has positive clock derivative, uniformly
on compact normalized null directions. S8, specialized to d=3 on this
**local** segment, gives a contained volume at least c*h to power 3/2, where
h is the clock advance. For larger h use monotonicity. Therefore

```math
\begin{aligned}
|\nu^\delta_{\chi,\phi}|([0,w])&\le Cw,\\
L^\delta_{\chi,\phi}(\rho)
 &=\frac32\beta_3c_3^{-5/3}\int_0^\infty z^3K'_3(z^{3/2})
       E((c_3\rho)^{-2/3}z)\,dz,\\
E(w)&=\frac{N^\delta_{\chi,\phi}(w)-b_1w-b_2w^2}{w^{5/2}}.
\end{aligned}\tag{C3.3}
```

The last identity is Stieltjes integration by parts and the two actual zero
moments. N continues **constantly** beyond its support; the subtracted
polynomial is integrated on the whole half-line. Hence no upper boundary
term is lost. Finite variation and the integrable kernel derivative justify
Fubini at every positive density. The first bound alone gives O(rho), not
vanishing. Positive-volume complements have an exponentially small normalized
response. Small volume is not short displacement.

### A derived first subtraction, not a critical estimate

For almost every target flow label with finite arrival, that arrival has a
unique nonconjugate generator. Indeed the arrival graph is locally Lipschitz;
at a differentiability point all supporting last-segment cones have the same
terminal direction, hence the same backwards geodesic. Conjugate arrivals
are critical values of the smooth map from one initial screen angle and
affine length to the two-dimensional flow surface; Sard applies in countably
many charts. This is an almost-everywhere statement, **not** a bound on their
normalized neighborhoods or an assumption of finitely many singularities.

On a regular ray use affine null Fermi coordinates (s,v,Z), with one screen
coordinate Z. If eta is the positive pairing of the target clock with the
terminal tangent, the broken screen index has positive coefficient D(s).
Integrating its quadratic lens, including the two tips, gives

```math
\begin{aligned}
A_3(x,z)&=\frac{4\sqrt2}{3}\eta^{3/2}
                    \int_0^L D(s)^{-1/2}\,ds,\\
V(x,q(a_x(z)+h,z))&=A_3(x,z)h^{3/2}+o(h^{3/2}),\\
b_1&=\int_M\chi(x)\,d\mu_g(x)
 \int_{\mathcal R_\delta(x)}\phi(q(a_x(z),z))j(a_x(z),z)
                       (c_3/A_3(x,z))^{2/3}\,d\sigma(z),\\
N^\delta_{\chi,\phi}(w)&=b_1w+o(w),\qquad
L^\delta_{\chi,\phi}(\rho)=o(\rho).
\end{aligned}\tag{C3.4}
```

Here R-delta has arrival strictly between the two physical faces and strictly
above the cutoff. The index coefficient behaves as 1/s at the first tip
and 1/(L-s) at the other. A tip interval of longitudinal length epsilon has
volume bounded by C*h^(3/2)*epsilon^(3/2)+C*h³. On the central segment,
rescale Z by sqrt(h), v by h and apply dominated convergence. Compact causal
control confines the whole interval to the unique ray's tube; positivity
of the index bounds the rescaled central screen. Taking h to zero and then
epsilon to zero proves the coefficient, without a uniform inverse near a
caustic. In flat null coordinates D=L/(s*(L-s)); the integral recovers exactly
c3*(2*L*eta)^(3/2), a normalization check independent of the 4D coefficient.

The pointwise strip bound used in C3.3 dominates the divided clock strips.
Regular null graphs meet each spacelike face and temporal level transversely;
the equality masks are null in the remaining variables. Dominated convergence
therefore proves C3.4 on the actual domain, with both fields and all contacts.
Subtract b1*w in the Stieltjes formula to obtain the last conclusion. This
improves the unconditional bound, but supplies neither b2 nor the 5/2 remainder.

## 3. A complete restricted theorem: faithful whole conformal diamonds

**Theorem FCDC-3.** Suppose a 3D G-SS member also has the following geometric
property for every sufficiently small fixed positive temporal cutoff: a compact
neighborhood of its long null relation has a finite endpoint cover such that
each entire physical interval lies faithfully in a conformal Minkowski patch,
with its entire flat diamond as image. The intervals and the coordinate
extensions used for differentiation stay in compact subpatches with smooth
positive bounded conformal factor. Then the complete canonical deterministic
action tends to the independent curvature-plus-joint target. Its original-law
expectation tends to that target separately.

This is the **additional** whole-interval condition, not local conformal
flatness or a field added to G-SS. It includes every G-SS region in a globally
conformal Minkowski spacetime, and smooth conformal factors on thin flat-torus
slabs of duration less than half the shortest period: their whole intervals
have unique faithful lifts. Arbitrary thick quotients are not included.

### Actual phase and both measures

Let d=t_y-t_x, r be the spatial separation, n its direction, sigma=d²-r².
On the unit-duration rest diamond D0 in three dimensions, use coordinates
(A,B-parallel,B-perpendicular). The exact boosted map and volume are

```math
\begin{aligned}
t_*&=t_x+d(1/2+A)+rB_\parallel,\\
X_*&=X_x+r(1/2+A)n+dB_\parallel n+\sqrt\sigma B_\perp n^\perp,\\
V(x,y)&=\sigma^{3/2}\int_{D_0}\Omega(t_*,X_*)^3\,dA\,dB
      =c_3\sigma^{3/2}H(x,r,n,\sigma),\\
d\mu_g(x)d\mu_g(y)&=\Omega(x)^3\Omega(y)^3
                   \frac{r}{2\sqrt{r^2+\sigma}}\,dx\,d\sigma\,dr\,dn.
\end{aligned}\tag{C3.5}
```

The boost has determinant one and the rest dilation has determinant
sigma to power 3/2. Long-null compactness keeps r away from zero in each
patch. Reflection of B-perpendicular makes the whole integral smooth and
even in sqrt(sigma), hence smooth in sigma to every required finite order.
This is not reflection symmetry of Omega. H is positive with a compact lower
bound. The **actual** phase w=sigma*H^(2/3) has a smooth positive inverse near
zero. No endpoint density or varying phase is frozen.

### Moving boundaries and cutoff contacts

A long null source cannot lie on the future face, a target on the past face,
or either endpoint on the joint. A limiting causal curve in the closure would
immediately leave the local spacelike boundary on its forbidden side. Compact
causal control and the positive time gap consequently give clearance of these
forbidden contacts. The short joint collar is still present.

The allowed past-source and future-target constraints are independent on the
null pair manifold: variation along the target generator changes only the
latter, with nonzero derivative against its timelike conormal. A single source
constraint is transverse to source time. With the temporal shell and at most
one face the same triangular rank calculation applies. If both faces meet the
shell at a sufficiently small cutoff, temporal-speed control puts both near
one joint point. The leading three differentials there are
alpha-minus*dx, alpha-plus*dx+alpha-plus(k)*dr, and d tau(k)*dr.
Their rank is three because the two joint conormals are independent and
k is a nonzero future null vector. Compactness preserves this rank at one
fixed sufficiently small delta. With empty joint no such double-face shell
contact exists at small delta.

Use w and these active defining functions as coordinates. A finite smooth
pair partition rectifies the actual domains to fixed orthants; all moving
Jacobian derivatives, endpoint factors and chart weights remain. Integrating
the compact smooth density gives

```math
\begin{aligned}
B^\delta_{\chi,\phi}(w)&=b_0+b_1w+O(w^2),\\
L^\delta_{\chi,\phi}(\rho)&\longrightarrow0.
\end{aligned}\tag{C3.6}
```

The last line uses C3.1, not a 4D cancellation. Subtract the two polynomial
terms globally; the small-phase error has normalized bound O(rho^(-1/3)),
and fixed-phase tails are exponential. Finite sums retain every ordered
source/target label, not just matching charts. The complement of the endpoint
cover has a positive volume floor by continuity and compactness; it was not
omitted. Physical unions inside each faithful chart are counted once by its
point map. C3.6 is **not** asserted for multi-route charts lacking faithfulness.

## 4. Consume the actual short result and identify the target

The following discharges S30's hypotheses for FCDC-3, the focal sequel and
also the exact reduction for every original smooth G-SS member:

| Consumed hypothesis/input | Actual discharge, not a conclusion-valued condition |
| --- | --- |
| Smooth metric, compact auxiliary domains and finite derivative bounds | Smooth G-SS and a finite normal/face/joint atlas on a compact causal enclosure; for d=3 the finitely many S10 mixed derivatives exist and are bounded |
| Whole short-interval locality | The minimum of d tau on the compact future causal auxiliary-unit bundle is positive; choose delta below the finite source-support distance margins as in G2 |
| Uniform null-edge phase/inverse | S1–S8 apply to those genuinely local intervals; their positive ratio is derived there, not inferred for a long conjugate interval |
| Full/face/corner root and diagonal estimates | Compact timelike face conormals give the S21 depth-root denominator; transverse joint conormals give S26's height root; shrink the same fixed delta below these and the S17 shell bounds |
| Endpoint fields, physical masks and measures | Smooth fields on the compact auxiliary tubes, actual exponential target density and source density, exactly G10's full-minus-face-plus-corner indicator identity |
| Induced curve length and angle | Minus the restricted metric is positive on TJ; its one-dimensional Gram density and both future unit normals give G12. Compact transversality bounds the angle weight; no action defines this measure |
| Complete partition/point restoration | Source and target partitions independently sum to one near their physical/auxiliary domains. Sum all ordered pairs; their diagonal products sum to one, not the number of charts |

In d=3 the particular S14 diagonal value vanishes because the polar factor
has one zero at the diagonal. S11's **other** contact terms and the S13
odd-dimensional O(w²*(1+abs(log w))) remainder are still needed, and are
consumed, not set to zero. Both bulk Green-identity face fluxes remain until
summation. In particular the compensating joint flux T from G13 is generally
nonzero even for unit fields. S25 and S29 restore it, not the assertion that
all face terms vanish.

At a common fixed delta below **all** short and long thresholds, S30 and C3.6
give the complete weighted conclusion, followed by its unit-field specialization:

```math
\begin{aligned}
\lim_{\rho\to\infty}A_{\chi,\phi}
 &=\int_M\chi(\Box_g\phi+R_g\phi/2)\,d\mu_g
 +\int_{\Sigma_+}(\phi n_+\chi-\chi n_+\phi)\,d\Sigma_g
 +\int_J\chi\phi\coth\theta\,dA_g,\\
\lim_{\rho\to\infty}\mathcal A_{\rho,3}
 &=\tfrac12\int_M R_g\,d\mu_g+\int_J\coth\theta\,dA_g.
\end{aligned}\tag{C3.7}
```

At finite density A=S+L exactly. An alternate cutoff has the exact signed
indicator-difference allocation of G2, with opposite signs in short and long;
no arbitrary shell is declared negligible. Derivatives of partitions cancel
only in the complete ordered sum. The point occurs once. This completes the
deterministic theorem **only for the stated restricted class**.

### Independent variable-curvature and variable-angle calculation

In spatial R² set f=epsilon*x1, h=s*(1-r²), and let M lie between f-h/2 and
f+h/2 over r<1, with 0<s and 0<epsilon, s+epsilon<1. Take Omega=1+b*r²,
b>0. The separate globally strict Lipschitz extensions using (1-r²)-positive
prove ambient containment. Faces are smooth compact achronal disks, with
transverse circle joint, so this is an actual FCDC-3 member. This example is
not the definition of the theorem's class.

With A=1-epsilon² and joint parameter theta, the direct normal Gram and
conformal curvature computations in #90's sign give

```math
\begin{aligned}
R_g&=-16b\Omega^{-3}+8b^2r^2\Omega^{-4},\\
dA_g&=(1+b)\sqrt{A+\epsilon^2\cos^2\theta}\,d\theta,&
\coth\vartheta&=\frac{A+s^2}{2s\sqrt{A+\epsilon^2\cos^2\theta}},\\
\mathcal J_g&=\frac\pi s(A+s^2)(1+b),\\
\mathcal B_g&=2\pi s\int_0^1r(1-r^2)
             \left(-8b+\frac{4b^2r^2}{1+br^2}\right)dr\\
 &=4\pi s\left(1-\frac b2-\frac{1+b}{b}\log(1+b)\right).
\end{aligned}\tag{C3.8}
```

Here theta is the circle coordinate, vartheta the positive normal rapidity.
The curvature formula follows from
R=Omega^(-2)*(4*Box(log Omega)+2*g-flat-inverse(d log Omega,d log Omega));
it is not fixed by an action coefficient. The induced length is calculated
from the tangent of t=epsilon*cos(theta), and the angle from the two future
normals. Both terms are nonzero and the angle varies. C3.7 gives their sum,
not merely a flat angle with an unchanged area measure.

## 5. Separate original-law expectation

Only after the deterministic theorem, apply the generic measured-order bridge.
A smooth second-countable manifold is standard Borel. Global hyperbolicity
makes the ambient order closed and antisymmetric; its triple interval indicator
is Borel. Compact closure and smooth positive chart densities give finite
atomless volume. Tonelli gives Borel actual V. Ambient containment identifies
the restricted interval; endpoints are atoms of zero mass. Null partners are
volume-null by the achronal-flow-box argument, without deleting their neighborhoods.
The polynomial-exponential kernel is bounded at each fixed positive density;
layer counts are bounded by squared Poisson cardinality. Thus the one-point
and distinct ordered two-point Mecke identities apply to the original law:

```math
\begin{aligned}
\mathbb E L_k&=\rho^2\int_{x\preceq y\in M}
 e^{-\rho V(x,y)}\frac{(\rho V(x,y))^k}{k!}\,d\mu_g(x)d\mu_g(y),\\
\mathbb E A^{\mathrm{disc}}_{\rho,3}&=\mathcal A_{\rho,3}.
\end{aligned}\tag{C3.9}
```

These are exactly the hypotheses/conclusion of
`dimensionFiniteMeasureAction_expectation`, not a new probability law or a
new compiled manifold instance. C3.7 then transfers for FCDC-3; the sequel
transfers its own complete deterministic result by the same discharged facts.
For arbitrary G-SS, the finite-density identity is valid but no full expected
limit follows from C3.4. No sample-wise conclusion is made.

## 6. Continuation, status and the remaining quantified task

Do not stop the research at FCDC-3: it excludes conjugate and multi-route
long intervals. The [sequel](curved-three-d-focusing.md) derives the actual
3D volume and pair measure for the compact quartic-focus slab, retains both
wells and their endpoint overlaps, and proves its **complete** zero limit.
It also identifies the critical estimate still missing in the original class.
This is a scoped positive theorem, not a claim that all 3D caustics are benign.

- **WORKS:** FCDC-3 with its explicitly added whole-interval condition, and
  the sequel's one specified curved focal slab. Existing flat results survive.
- **FAILS:** no new 3D complete-action failure is proved. The integrated 4D
  and higher-dimensional counterexamples remain unchanged in their own dimensions.
- **UNKNOWN:** the original arbitrary smooth curved-3D G-SS conclusion,
  including uncontrolled minimizing multiplicity/degeneracy and interactions
  with moving face/closing contacts. C3.2–C3.4 remain valid there; they do not
  establish the C3.3 critical remainder. **#177 retains the whole missing row.**

Written geometric/analytic arguments, finite diagnostics and existing compiled
foundations are separate. No new Lean declaration, formal audit, model-sign
certificate, independent AI proof audit or human acceptance is claimed.
#94/#86 retain final intended-statement, mathematical/physical, provenance
and justified-formalization scrutiny. The validation receipt belongs to the PR.

Refs #177, #81, #24, #90, #150, #77, #94, #86.
