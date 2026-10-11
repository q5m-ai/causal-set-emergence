# General curved 4D: physical clock pushforward and the unresolved signed estimate

**Status: written partial analysis and a precise mathematical blocker, not a
complete-action theorem or counterexample.** This continues CFT5–CFT6 of the
[corrected FLAT theorem](corrected-flat-theorem.md) from integration commit
`76a8dd1c2330ea2207169a203fe3b7f5eaa2c36d`. All integrated positive and negative
results are retained. No restriction of G-SS, change of action/target/law,
new Lean result, or independent human mathematical review is claimed.

The new general geometric output is an **actual clock-fibre formula** for
interval volume and its long pushforward, valid through arbitrary cut and
conjugate contacts, and a uniform small-sublevel bound. It is not a sum of
geodesic volumes. The bound is insufficient at the signed critical order.
A dilation-increment estimate below is a genuinely weaker alternative to a
cubic primitive jet; it is **not yet discharged for arbitrary G-SS geometry**.
Section 7 identifies exactly the remaining geometric calculation. In
particular, this note does not answer the universal 4D question affirmatively
or negatively merely because its partial results can be committed.

## 1. Audit of CFT5–CFT6 and actual consumption of S30

Fix a smooth 4D G-SS member, with the selected ambient order restricted to M.
Use the canonical constants, not the negative d'Alembertian coefficient:

```math
\begin{aligned}
a_4&=\beta_4=4/\sqrt6,\qquad c_4=\pi/24,\\
K_4(s)&=(1-9s+8s^2-\tfrac43s^3)e^{-s},\\
\mathcal A_{\rho,4}
 &=a_4\sqrt\rho\,\mu_g(M)
   -\beta_4\rho^{3/2}\int_{x\prec y}K_4(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y).
\end{aligned}\tag{CP1}
```

**Notation correction:** CFT1 previously printed alpha in its point term;
the [shared interface](dimension-producer-interface.md) calls that positive
coefficient a. In the kernel convention a equals minus alpha. CFT1 is corrected
to a, preserving the canonical action used in its proof and all integrated
results. Neither CFT5 nor CFT6 needs a sign or numerical-factor correction.

Here is the hypothesis discharge needed before using
[S30](general-metric-short-remainders.md#8-quantified-short-theorem-partition-cancellation-and-the-151-boundary):

- G-SS supplies the smooth metric, compact closure, ambient causal convexity,
  two compact smooth spacelike faces, transverse joint and absence of additional
  boundary strata. Empty joint and disconnected faces are allowed. Scalar
  curvature uses the fixed sign in the general contract.
- Choose a smooth Cauchy temporal function tau. Enclose the compact source,
  face and joint tubes in a compact causal enclosure. The positive minimum
  of d tau on future causal auxiliary-unit vectors gives **whole-interval**
  locality, including for the auxiliary sources used by S30.
- Take a finite normal/face/joint atlas and decrease one positive delta below
  all S30 locality, null-rescaling, local phase, face-root, height-root and
  temporal-shell thresholds. Smoothness on these compact tubes supplies the
  finite derivative bounds required there. This is the local inverse of S30,
  not a uniform inverse through a long cut or conjugate contact.
- The unit endpoint fields extend smoothly to every auxiliary tube. For an
  endpoint partition, retain the complete ordered double sum before taking
  a limit. Its derivative terms sum to zero; only **then** are the physical
  fields constant. Both geometric endpoint measures remain.

Thus S30 applies for every fixed sufficiently small delta to the **actual
strict temporal-short action**. The unit-field normal derivative flux is
zero; its compensating face/joint terms have already been combined by S30.
The point term is present exactly once. At this same cutoff,

```math
\begin{aligned}
T_g&=\tfrac12\int_M R_g\,d\mu_g+\int_J\coth\theta\,dA_g,\\
\mathcal A_{\rho,4}-T_g
 &=L_g^\delta(\rho)+r_g^\delta(\rho),\qquad
 r_g^\delta(\rho)\longrightarrow0.
\end{aligned}\tag{CP2}
```

This is a complete-action reduction, not a claim about its limit. In
particular a proved finite nonzero long limit would shift the complete
limit by that value; a proved divergent long term could not be canceled by
this short remainder. No such general long conclusion is available below.
All assertions here consume the conventional written S30 proof, not a newly
compiled manifold theorem or a review certificate for it.

## 2. Physical intervals without selecting geodesics

Use the temporal flow of the smooth timelike vector field with d tau equal
to one, obtaining a Cauchy splitting Q as R times a Cauchy manifold Y.
The flow exists through every finite temporal level: a maximal flow line
ending at a finite level without a spacetime endpoint would be an inextendible
timelike curve missing a Cauchy level. A spacetime endpoint would instead
extend the smooth ODE. Thus this is a global splitting, not a global Euclidean
graph hypothesis on M. Fix any smooth positive density d sigma on Y and write

```math
\begin{aligned}
q(t,z)&\in Q,\qquad \tau(q(t,z))=t,\\
d\mu_g(q(t,z))&=j(t,z)\,dt\,d\sigma(z),\qquad j>0,\\
a_x(z)&=\inf\{t:x\preceq q(t,z)\},\\
b_y(z)&=\sup\{t:q(t,z)\preceq y\}.
\end{aligned}\tag{CP3}
```

An empty future section has a equal to positive infinity; an empty past
section has b equal to negative infinity. Every nonempty future section is
exactly a closed upper ray, and every nonempty past section a closed lower
ray: the flow is timelike, transitivity and push-up give the ray property,
and closedness of the globally hyperbolic causal order includes the finite
endpoint. Such endpoints are bounded by the time of x or y, respectively.
The threshold functions are Borel; for example the strict upper sublevel of
a is a countable union of causal tests at rational clock values.

The physical interval is the intersection of these rays on **each physical
flow line**. Consequently, for actual endpoints in M,

```math
\begin{aligned}
V_M(x,y)
 &=\int_Y \mathbf1_{\{a_x(z)\lt b_y(z)\}}
       \int_{a_x(z)}^{b_y(z)} j(r,z)\,dr\,d\sigma(z).
\end{aligned}\tag{CP4}
```

An empty section contributes zero, not an integral with infinite endpoints.
Global hyperbolicity confines the support to the projection of a compact
causal enclosure. Ambient causal convexity of M identifies this ambient
interval with the restricted one. Removing the two endpoints changes no
volume. This is Tonelli applied to the actual three-point causal indicator.
It counts the **union** of every causal route exactly once, including
continuously many minimizing null geodesics. It uses no branch count,
exponential-map injectivity, or assertion that a cut neighborhood is small.

In an ultrastatic spacetime this reduces to the familiar physical expression
with inner length equal to the positive part of time gap minus the two
spatial distances. In a general metric neither distance substitution nor a
sum of route-indexed kernels is valid; CP3–CP4 are the replacement.

### Continuity and the clock inverse actually available

The actual interval volume is continuous in both endpoints on a compact
endpoint set. To prove this, dominate its indicators on a common compact
causal enclosure. Except on the achronal boundaries of the two cones,
chronological membership is stable under endpoint perturbation and
nonmembership is stable by closedness of the causal order. Each boundary
has volume zero: in a timelike flow box it meets each vertical line at most
once. Dominated convergence proves continuity. This argument does not bound
any normalized neighborhood of those boundaries.

For fixed x and z with finite a, the function
V(x,q(t,z)) is zero at t=a, continuous and strictly increasing for t>a.
Indeed, for a at most t1 less than t2, the positive-volume chronological
interval from q(t1,z) to q(t2,z) lies in the larger x interval and outside
the smaller one, up to null endpoints. The clock inverse therefore exists
on its actual range and is continuous. **No differentiability, uniform
inverse derivative, or absolutely continuous pushed density follows from
this argument.** The primitive formulation below does not require them.

## 3. The whole long pushforward, including every closing contact

Along a timelike flow line, ambient causal convexity makes M either empty
or a single open interval. Denote its endpoints by m-minus and m-plus and
its projection by D. These are Borel data of the given open set, not imposed
smooth graph functions. D has compact closure in Y. Spacelike face charts
provide their local smooth descriptions where needed, but the following
formula also retains their closing fibres at the joint.

For x in M, put s=tau(x). Consider z in D with a_x(z) below m-plus(z).
Let T_x,z(v) be the inverse of the ambient volume V(x,q(t,z)) at v,
**clipped at m-plus(z)**, and starting at a_x(z) when v=0. Using ambient
volume defines this auxiliary inverse also at a face endpoint; on the
retained open fibres it equals the physical restricted volume. Let ell be the maximum of a_x(z),
m-minus(z) and s+delta. Discard only empty fibres with ell at least m-plus.
For the other fibres define

```math
\begin{aligned}
U_{x,z}(v)&=\max\{\ell_{x,z},T_{x,z}(v)\},\\
N_{\chi,\phi}^{\delta,V}(v)
 &=\int_M\chi(x)\,d\mu_g(x)
   \int_{\{z\in D:\ell_{x,z}\lt m_+(z)\}}
     \int_{\ell_{x,z}}^{U_{x,z}(v)}
       \phi(q(t,z))j(t,z)\,dt\,d\sigma(z),\\
N_{\chi,\phi}^{\delta}(w)&=
 N_{\chi,\phi}^{\delta,V}(c_4w^2).
\end{aligned}\tag{CP5}
```

Since T is clipped, U is at most m-plus on these fibres. If the volume at
ell already exceeds v, U equals ell and the contribution is zero. If the
volume threshold passes the future face, the whole fibre is included. At a
closing fibre its contribution is zero by its actual integration length,
not by deleting a collar. For signed phi one integrates its signed density;
one must **not** take a positive part of its antiderivative difference.

CP5 follows by monotone substitution of an indicator, not by differentiating
the inverse. All quantities are measurable; equivalently the sublevel tests
for T are tests on the continuous actual V. Both measures, the physical
partner domain, the moving null arrival, lower and upper faces and the
fixed temporal cutoff are present. No chart-label matching or component
exclusion has been inserted. Restoring an arbitrary finite endpoint atlas
at finite density recovers this same formula, including off-diagonal labels.

For two fixed cutoffs their signed difference is exactly the portion of
CP5 between the two lower clocks. Its negative pair prefactor belongs to
short and its opposite to long, as in G2 of the globalization note. This
formula includes macroscopic shells; it does not declare them negligible.
Only the sufficiently small local shell conversions actually proved in
S30 may be consumed as vanishing responses.

## 4. A general quantitative estimate, and why it stops too early

**Lemma (small physical long sublevels).** For every fixed 4D G-SS member
and positive temporal cutoff there are positive constants v0 and C such that

```math
\begin{aligned}
N_{1,1}^{\delta,V}(v)&\le C\sqrt v\quad(0\lt v\le v_0),\\
|\nu_{\chi,\phi}^{\delta}|([0,w])&\le C_{\chi,\phi}w
 \quad(0\lt c_4w^2\le v_0).
\end{aligned}\tag{CP6}
```

Here nu is the actual signed phase measure, and the second line bounds its
total variation by the positive pair measure with absolute endpoint weights.
The constants are geometry/cutoff dependent. They are not a family-uniform
or density-dependent geometry assertion.

**Proof.** Work in the compact flow tube of target spatial projections and
all endpoint times, and its compact causal enclosure. Write a=a_x(z) and
t=a+h for a retained causal target. If a-s is less than delta/2, the long
condition forces h at least delta/2. The interval contains a fixed small
clock-timelike diamond starting at q(a,z). Uniform compact local metric
bounds give a positive volume lower bound. Such pairs are excluded by
choosing v0 smaller than that bound.

Otherwise a-s is at least delta/2. Choose a causal null geodesic from x to
y0=q(a,z), which exists by global hyperbolicity; a chronological curve would
contradict the definition of a. Take its last fixed small temporal segment,
from p to y0, shorter than delta/4 and all compact normal-locality margins.
All of this segment and its small clock-advanced target diamonds lie in a
normal neighborhood. The *long* geodesic can have a cut/conjugate endpoint;
only this uniformly short final segment is used.

Let sigma(p,q(a+h,z)) be the local squared geodesic separation. At h=0 it is
zero. First variation pairs a nonzero future null tangent with the timelike
clock vector; its derivative is strictly positive. The segment's fixed
temporal length and compact normal charts give a uniform positive lower
bound for this derivative. Taylor and a common small h0 give sigma at least
c h for h at most h0. The actual local interval formula S8, with its derived
positive bounded ratio, then gives a lower volume bound c-prime times h
squared. This local diamond is contained in the original physical interval
because x precedes p. No chosen geodesic is counted as an additional volume.

For h at least h0 use monotonicity and the same positive lower bound at h0;
decrease v0 again. Every remaining small-volume long fibre therefore has
h at most C sqrt(v). The choice of a null geodesic need not be measurable:
it proves a uniform pointwise bound for each fibre, whereas the primitive
being integrated is the measurable CP5. Bounded j on the target flow tube,
finite sigma-volume of the compact spatial projection and finite source
volume now prove CP6. Bounded endpoint fields prove its variation version.

This is genuine control through **all** contacts, but only at first primitive
order. By Stieltjes integration and the absolute derivative of the kernel it
gives an absolute long-action bound of order rho, not a vanishing action.
It supplies no second or third signed coefficient. The examples in section 6
show why promoting it to critical cancellation would be invalid.

The complementary positive-volume part is nevertheless completely controlled.
Put B=mu_g(M). Boundedness of the actual kernel polynomial gives, for fixed
v0>0 and unit fields,

```math
\begin{aligned}
|L_{\{V_M\ge v_0\}}(\rho)|
 &\le C\beta_4 B^2\rho^{3/2}(1+(\rho B)^3)e^{-\rho v_0}
 \longrightarrow0.
\end{aligned}\tag{CP6a}
```

Bounded fields only change the constant. The rest of CP5, including its
regular nearly-null complement, remains in CP7; it is not removed by this
tail estimate. In particular temporal long is not the same as positive volume
bounded away from zero.

## 5. A signed alternative to a cubic jet

Set h=(c4 rho) to power minus one-half. For arbitrary real b1 and b2 define
F(w)=(N(w)-b1 w-b2 w squared)/w cubed, where N is the **complete physical**
CP5 primitive. CFT6 with b3=0 and its remaining critical moment give

```math
\begin{aligned}
H(z)&=2\beta_4c_4^{-3/2}z^4K_4'(z^2),\qquad
 \int_0^\infty H(z)\,dz=0,\\
L_g^\delta(\rho)
 &=\int_0^\infty H(z)\{F(hz)-F(h)\}\,dz.
\end{aligned}\tag{CP7}
```

The identity is valid at every positive density, even for unbounded F with
no jet. The finite total phase measure is continued constantly past its
support, not by zero. Near zero the unsubtracted integrand is a constant
times z N(hz) plus polynomial terms, hence integrable. At infinity the
kernel dominates the constant primitive and the subtraction polynomial.
Subtracting the single finite number F(h) is permitted because the displayed
moment is exactly zero. Integration by parts has the positive long sign
in CFT6, since the original pair prefactor is negative.

**Analytic sufficient estimate, not a geometric theorem.** If, for each z>0,
F(hz)-F(h) tends to zero and its absolute value has a common H-integrable
majorant, CP7 tends to zero. One usable majorant is
C times (1+absolute log z) to any fixed finite power. In particular it is
enough that F be locally absolutely continuous in log w and

```math
\begin{aligned}
\sup_{w>0}|wF'(w)|&\lt\infty,\qquad
 \lim_{w\downarrow0}wF'(w)=0.
\end{aligned}\tag{CP8}
```

The derivative conditions may hold almost everywhere with the corresponding
essential bounds. Integrate the logarithmic derivative between h and hz:
the difference is bounded by C absolute log z and tends to zero on each
fixed log interval. Near zero H is O(z to the fourth power); at infinity it
is a polynomial times a Gaussian. This proves the required domination.
A cubic Peano jet is thus **not necessary**. Nor is CP8 necessary: direct
signed estimates in CP7 can be weaker still. No CP8 derivative is claimed
for the geometric inverse in CP5.

More generally, if those dilation increments tend to kappa log z with the
same domination, the complete-action limit, by CP2, would be

```math
\begin{aligned}
\lim_{\rho\to\infty}L_g^\delta(\rho)
 &=\frac{48}{\pi}\kappa,\\
\lim_{\rho\to\infty}\mathcal A_{\rho,4}
 &=T_g+\frac{48}{\pi}\kappa.
\end{aligned}\tag{CP9}
```

This is a conditional response calculation, **not** an admissible example
with nonzero kappa. The constant is fixed by

```math
\begin{aligned}
\int_0^\infty z^jK_4(z^2)\,dz
 &=-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2),\qquad j>-1,\\
\int_0^\infty z^4K_4'(z^2)\log z\,dz&=\sqrt\pi/8,\\
2\beta_4c_4^{-3/2}(\sqrt\pi/8)&=48/\pi.
\end{aligned}\tag{CP10}
```

The first identity follows from the actual polynomial coefficients and
convergent gamma integrals. Differentiating at j=2 and integrating by parts
proves the second. All logarithmic integrals converge absolutely. This also
checks the normalization of a potential critical logarithm independently of
any caustic model.

## 6. Diagnostics that distinguish the estimates from the desired theorem

The following are **scalar phase-measure controls, not G-SS geometries**.
They show both the gain of CP7 and the insufficiency of CP6. Fix w0=1/4;
continue each primitive constantly above w0.

1. For w below w0 take N(w)=w+w cubed times
   log(1+log(w0/w)). It is positive and increasing, has finite mass and is
   O(w), but has **no cubic Peano jet**. Indeed its cubic quotient diverges.
   Its logarithmic derivative is -1/(1+log(w0/w)), so CP8 and the ordinary
   derivative on the capped tail prove a zero signed response. This is an
   explicit alternative to demanding a cubic jet.
2. Take N(w)=w+w cubed times log(w0/w). It has the same positivity,
   finite-mass and O(w) properties. Its dilation increments tend to minus
   log z, so its normalized signed response tends to **-48/pi**, not zero.
   This proves that the general bound CP6 and monotone inverse continuity
   do not logically imply the desired limit. It is not an action counterexample.
3. A positive fractional addition w to power 5/2 also respects those bounds.
   Its signed response grows as rho to power 1/4 with the exact coefficient
   from G7; no constant cubic subtraction removes it.

For the first two controls monotonicity follows by differentiating: the
negative part of the cubic correction's derivative is at most w squared,
so N-prime is at least 1-w0 squared. Their logarithmic quotients on the
constant tail are continuous and have bounded logarithmic derivative.
No unproved geometric realization is used in these negative controls.

### A degenerate-contact route that is not yet an obstruction

A tempting local model for a degenerate optical minimum is

```math
\begin{aligned}
\mathcal V(E,A,B)
 &=\int_{\mathbb R}(E-u^4-Au^2-Bu)_+^{3/2}\,du,\\
\mathcal V(\lambda E,\lambda^{1/2}A,\lambda^{3/4}B)
 &=\lambda^{7/4}\mathcal V(E,A,B),\qquad \lambda>0,\\
dE\,dA\,dB&\longmapsto\lambda^{9/4}dE\,dA\,dB.
\end{aligned}\tag{CP11}
```

These identities are just substitution u=lambda to power one-quarter times
v in a finite positive-part integral. A weighted homogeneous sector whose angular volume profile is bounded above
and bounded strictly away from zero would have volume-phase primitive power
9/7, whose normalized response could scale
as rho to power 3/14. That **does not prove a physical coefficient**. A real
metric derivation would have to produce this optical family from the actual
interval, integrate its longitudinal and regular transverse measures,
include the competing-minimum side, subtract the regular-side terms and
control the matched remainder. An endpoint-sector power count establishes
none of those requirements. In particular no nonzero matched coefficient,
admissible complete-action obstruction, or rejection of the integrated
sphere-circle result follows from CP11. This route remains unresolved,
rather than being promoted to a counterexample from its suggestive exponent.

## 7. Precise stopping blocker and separate expectation

The unresolved object is now the explicit inverse-strip integral CP5 of
**CP4's actual physical interval volume**. CP6 controls its mass, not the
signed critical response. The missing general geometric statement is either:

- derive sufficient dilation-increment control in CP7 (or another direct
  signed estimate) from those actual arrival/departure functions, with all
  competing minima, changing contacts and closing fibres included; or
- derive and match a nonvanishing response for an admissible fixed G-SS
  member, retaining the regular complement and cutoff shells, then use CP2
  to prove its complete-action behavior.

Even existence of suitable first two coefficients b1,b2 for the CP8 route
has not been proved here. Declaring them to exist, differentiating the
continuous clock inverse, summing finitely many conjectured branches, or
using CP6 to discard a cut collar would assume the missing producer.
The scalar controls prove a concrete logical insufficiency of the estimates
obtained; they do not prove that G-SS admits those scalar primitives.
The degenerate model likewise lacks geometric realization and full matching.
This is a **mathematical blocker**, not a request to narrow the class or to
obtain interim human review. A conditional CP8 theorem cannot complete #151.

For clarity, the expectation bridge itself is not blocked. Its hypotheses
are separately discharged on the actual geometry:

- the smooth manifold is standard Borel and the ambient globally hyperbolic
  causal order is a closed Borel partial order;
- the triple interval indicator is Borel, restricted geometric volume is
  finite and atomless, and ambient causal convexity gives physical interval
  containment, including all null paths;
- achronal-boundary Fubini makes the null-pair relation product-null, without
  deleting a neighborhood; chronological intervals have positive volume;
- the exclusive ordered layer counts are bounded by squared cardinality,
  whose moment under the original finite Poisson law is finite.

The existing generic measured-order Mecke/count theorem therefore gives,
conventionally on this manifold, for every positive density,

```math
\begin{aligned}
\mathbb E_{\mathrm{Poisson}(\rho\mu_g|_M)}A^{\mathrm{disc}}_{\rho,4}
 &=\mathcal A_{\rho,4},\\
\mathbb E A^{\mathrm{disc}}_{\rho,4}-T_g
 &=L_g^\delta(\rho)+r_g^\delta(\rho).
\end{aligned}\tag{CP12}
```

This uses the actual selected order and volume, not an optical model or an
auxiliary law. It is a written geometric application of the existing compiled
generic bridge; there is no new compiled universal manifold instance. Without
settling the deterministic long term, it supplies **no expectation limit**.
There is no variance, sample-wise, shrinking-cutoff or rate assertion.

## 8. Validation and scope ledger

`curved4_physical_response.py` and `test_curved4_physical_response.py` are
finite diagnostics, not a general spacetime solver. They check the clipped
clock primitive against original endpoint integrations with both nonconstant
coordinate densities, signed endpoint fields, moving/closing contacts and
short/long restoration. The accepted sphere-circle physical-volume routines
check clock inversion on both sides of the secondary transition and retain
nonzero circle separation; no new standalone sphere theorem is introduced.
They also check the signed normalization, constant-tail Stieltjes identity,
non-jet vanishing control, nonvanishing scalar controls and CP11's limited
homogeneity claim. These checks cannot certify the geometric proofs or the
missing estimate.

The result is **not a corrected general curved-4D theorem**. General curved
4D complete-action behavior remains #151/#81's research obligation. The sharp
written FLAT theorem, selected curved successes, higher-dimensional complete
action obstructions and all previously integrated foundations remain intact.
No issue body or state is changed; a 4D result would still not replace the
broader dimension/null/mixed contracts of #81/#24. Human expert scrutiny and
justified formalization remain #94/#86 final-acceptance obligations.

No Lean/checker/dependency/build input changes. No fresh Lean audit, new
compiled asymptotics, agent launch, merge or deployment is claimed. The PR
records actual local, CI and GitHub browser-rendering checks separately.

Refs #151, #81, #24, #86, #94.
