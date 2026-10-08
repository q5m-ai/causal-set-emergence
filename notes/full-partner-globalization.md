# Full-partner globalization: foundations and a focusing obstruction (#151)

**The universal producer remains unproved; #151 is not administratively
completed.** This note proves the finite-density manifold/atlas foundation
and an actual all-dimensional, weighted long producer for **thin flat-torus
slabs**. It consumes, without strengthening, the accepted 4D sphere–circle
cut-neighborhood result. The continuation now derives a
[written 7D complete-action obstruction](seven-dimensional-focusing-obstruction.md)
to the all-dimensional finite G-SS target, including the matched cut remainder,
actual short point cancellation and complete complement. It is not a universal
classification of nearly-null responses, a Lean theorem or independent human
review. No desired averaged estimate is an admissibility input. #151/#81/#24
remain open, and PR #159 remains draft for review/contract coordination.

Base: `b86f5dadddaeb6a11299557ff28781e9b33ed743` on
`origin/issue-81-general-coverage`, including #137 / PR #146 and #139 / PR #147.
The statements below are conventional arguments, not new Lean declarations
or independent human review. Historical verification claims are unchanged.

## 1. Shared sign, order and cutoff

Use exactly [G-SS](general-contract.md#3-a-precise-non-vacuous-general-core-candidate)
and [its independent action](general-contract.md#2-independent-action-order-and-geometric-target),
in each integer physical dimension d at least two. The ambient manifold is
smooth, time-oriented and globally hyperbolic; M is the fixed precompact open,
ambient-causally-convex two-spacelike-face region. The selected order is the
**ambient order restricted to M**. Both measures are Lorentzian volume;
the exclusive interval removes exactly its two endpoints, not null relations.

Freeze a smooth Cauchy temporal function t on the ambient spacetime. The
shared separation is its **temporal gap**; it is not small interval volume.
With bounded real endpoint fields chi, phi, set

```math
\begin{aligned}
\ell(x,y)&=t(y)-t(x),\\
V_M(x,y)&=\mu_g\bigl(M\cap(J^+(x)\cap J^-(y)\setminus\{x,y\})\bigr),\\
P^{\lt\delta}_{\chi,\phi}(\rho)
 &=\int_{M\times M}\mathbf1_{\{x\preceq y,\ \ell(x,y)\lt\delta\}}
       \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
P^{\ge\delta}_{\chi,\phi}(\rho)
 &=\int_{M\times M}\mathbf1_{\{x\preceq y,\ \ell(x,y)\ge\delta\}}
       \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
S^\delta_{\chi,\phi}
 &=a_d\rho^{2/d}\int_M\chi\phi\,d\mu_g
       -\beta_d\rho^{1+2/d}P^{\lt\delta}_{\chi,\phi},\\
L^\delta_{\chi,\phi}&=-\beta_d\rho^{1+2/d}P^{\ge\delta}_{\chi,\phi},
\qquad A_{\chi,\phi}=S^\delta_{\chi,\phi}+L^\delta_{\chi,\phi}.
\end{aligned}\tag{G1}
```

Here K, a, beta and the auxiliary normalization constant c are the existing
dimension-indexed quantities, not new coefficients. The long output is
**signed**, with a minus sign. The point belongs exactly once to strict short;
equality belongs to long even when a diagnostic assigns mass to that level.
No vanishing of L is assumed.

[Initial coordination](https://github.com/q5m-ai/causal-set-emergence/issues/151#issuecomment-6049625050)
proposed time plus auxiliary spatial distance. After reading #150's concurrent
proposal, [the follow-up](https://github.com/q5m-ai/causal-set-emergence/issues/151#issuecomment-6049652763)
**superseded** that candidate with the temporal gap above and notified #149/#150.
This does not change any old radial-null-cutoff theorem or claim peer approval.
#149 owns dimension coefficients/flat producers; #150 owns local metric
responses; #151 owns the nonlocal producer and globalization. No shared
production definition is edited here. The inspected
[#149 interface at its published implementation pin](https://github.com/q5m-ai/causal-set-emergence/blob/dc6233e/notes/dimension-producer-interface.md)
uses the same coefficients, volume phase and signed pieces. Its Minkowski
producer keeps the radial-null cutoff; G2, not an identification of masks,
is the compatibility rule.

For any two Borel short masks s and s-prime, including two different cutoff
conventions, their exact overlap correction is

```math
\begin{aligned}
D_{s,s'}(\rho)&=-\beta_d\rho^{1+2/d}
 \int_{M\times M}\mathbf1_{\{x\preceq y\}}(s-s')(x,y)
 \chi(x)\phi(y)K_d(\rho V_M(x,y))\,d\mu_g(x)d\mu_g(y),\\
S_s-S_{s'}&=D_{s,s'},\\
L_s-L_{s'}&=-D_{s,s'}.
\end{aligned}\tag{G2}
```

This restores every overlap at finite density, with its actual sign. It does
not assert that the shell has a zero limit. Time gap and unnormalized radial
null distance `v = delta_t + r` are different masks even in Minkowski space.

## 2. General geometric foundation, without an analytic estimate

We use the standard smooth Cauchy temporal-function theorem of
[Bernal–Sánchez](https://arxiv.org/abs/gr-qc/0401112), not an assumed bound on
interval-volume derivatives. The following compact argument also explains
precisely where global hyperbolicity and ambient containment enter.

### Compact causal control and Borel order

Let K be the compact closure of M and choose any smooth complete auxiliary
Riemannian metric h. Cover K by finitely many sets of the form
`I+(p_i) intersect I-(q_i)`. Every causal curve with endpoints in K lies in
one of the finitely many compact ambient diamonds `J+(p_i) intersect J-(q_j)`.
Their union D is compact, by global hyperbolicity. On the bundle of future
causal h-unit vectors over D, the continuous function dt is strictly positive.
The bundle is compact, so its minimum m is positive. Consequently every such
causal curve obeys

```math
\begin{aligned}
\mathrm{length}_h(\gamma)&\le m^{-1}\bigl(t(y)-t(x)\bigr),\\
 d_h(x,z)&\le m^{-1}\bigl(t(y)-t(x)\bigr)
 \quad\text{for every }z\in J^+(x)\cap J^-(y),\\
 &\hspace{35mm}x,y\in K,\quad x\preceq y.
\end{aligned}\tag{G3}
```

The second inequality uses a causal curve through z, concatenating the two
relations. It bounds the **whole interval**, including all alternative paths,
not just one chosen geodesic.

For completeness, closedness of the causal relation follows from the same
compact control and the causal limit-curve argument. For convergent endpoints,
place their neighborhoods in finitely many such diamonds. Parameterize their
causal curves by t and extend constantly over the small endpoint discrepancies.
G3 gives a common Lipschitz bound and compact range. A uniformly convergent
subsequence is causal by closedness of the cones in local coordinates. If the
limiting temporal gap is zero, G3 forces coincident endpoints; otherwise it
connects the limiting endpoints causally. Thus J-plus is closed, hence Borel.
No smoothness of its boundary or uniqueness of geodesics is needed.

The joint exclusive-interval indicator on triples is Borel: it is the product
of the indicators of `x <= z`, `z <= y`, membership in M, and the two endpoint
inequalities. Tonelli therefore makes V_M a Borel function of both endpoints.
It lies between zero and the finite volume of M. A finite chart cover of K
proves that finiteness: in each relatively compact chart the positive smooth
volume density `sqrt(abs(det(g)))` is bounded. The same chart expression
proves atomlessness. These are geometric measures, not supplied target masses.

**Containment is a separate hypothesis of G-SS.** If x,y are in M, every point
in their closed ambient interval lies on a concatenated ambient causal curve
between them, so ambient causal convexity puts it in M. Endpoint removal is
volume-null. Hence the restricted volume equals the actual ambient interval
volume. The same curves prove that intrinsic and restricted orders agree.
None of these conclusions follows merely from intrinsic global hyperbolicity.

Null intervals also have zero volume without deleting cut loci. If x precedes
y but not chronologically, the push-up property puts their whole interval in
the achronal boundary of J-plus(x). In a timelike flow box an achronal Borel set
meets each vertical timelike line at most once; Fubini gives zero volume.
Thus, for each x, its null-related partners are volume-null. Joint Borel
measurability and Tonelli give zero product measure for the null relation and
diagonal. Chronological endpoints have an open positive-volume subinterval.
These facts prove that the small-volume pushforward in section 4 has no atom
at zero. They do **not** bound normalized neighborhoods of that atomless set.

### Finite normal atlas and genuine short locality

Cover K by finitely many smaller neighborhoods with closures in convex normal
neighborhoods U_i, and choose smooth nonnegative source weights chi_i supported
compactly in U_i, summing to one near K. Such weights are constructed by taking
finitely many bumps positive on the smaller cover, dividing by their positive
sum near K, and using one cutoff equal to one near K to extend by zero.
Choose target weights phi_j independently in the same manner. There is no
requirement that the two atlases or their labels agree.

The h-distance of each compact source support to the complement of its U_i
is positive. Choose delta less than m times the minimum of these finitely
many distances. G3 proves: if chi_i(x) is nonzero and a causal pair is strict
short, **its entire ambient interval lies in U_i**, regardless of target label.
This is the uniform locality lemma needed before #150 uses local interval
calculations. It makes no inference from small V_M. Long intervals can cross
any number of charts and encounter cut/conjugate loci.

Near the compact smooth spacelike joint, local tangent Gram matrices are
positive definite. Their smooth positive area densities and finitely many
charts give finite induced area, including counting measure in dimension two.
The two future unit normals are smooth; transversality makes their inner
product strictly greater than one. Compactness bounds the positive angle
weight. Smooth scalar curvature is bounded on K. Thus the independent bulk
and joint target integrals are absolutely finite. On overlaps these are the
same metric densities by the ordinary determinant change-of-variables rule,
not chartwise target choices. No action coefficient is used to define them.

### Canonical expectation specialization in writing

The manifold is standard Borel; the constructed ambient causal relation is a
Borel partial order; restricted volume is finite and atomless. These discharge
the hypotheses of the existing dimension-indexed measured-order Mecke/count
argument, with intensity rho times restricted volume. Counts use distinct
ordered pairs and the actual exclusive interval. Every layer count is bounded
by squared cardinality, so finite Poisson second moments justify the finite
signed sum. The one-point mean and two-point mean carry respectively one and
two intensity factors. This proves in writing the unchanged finite-density
expectation equality with G1 at unit fields, independently of any limit.

This is a general **written** geometric instantiation, not a new compiled
Lorentzian-manifold instance. [#137's checked package](../formal/COMPACT_MEASURED_ORDER.md)
implements the selected torus and sphere–circle instances only. The universal
formal encoding remains a verification obligation under #86; an upstream
compiled example is not evidence that this general instantiation was compiled.

## 3. Exact finite atlas globalization and its quantitative boundary

At each positive density all pair integrals are absolutely finite: K_d is a
polynomial times an exponential, hence bounded on nonnegative arguments, and
both endpoint measures and fields are finite/bounded. In chart coordinates
use **both** volume densities and the actual V_M of section 2, even when the
interval exits both endpoint charts. Finite summation and change of variables
give

```math
\begin{aligned}
\sum_{i,j}\chi_i(x)\phi_j(y)&=1,\\
\sum_{i,j}\int_M\chi_i(x)\phi_j(x)\,d\mu_g(x)&=\mu_g(M),\\
\sum_{i,j}P^{\ge\delta}_{\chi_i,\phi_j}&=P^{\ge\delta}_{1,1},
\qquad \sum_{i,j}S^\delta_{\chi_i,\phi_j}=S^\delta_{1,1},\\
\sum_{i,j}L^\delta_{\chi_i,\phi_j}&=L^\delta_{1,1}.
\end{aligned}\tag{G4}
```

The complete **ordered double sum** is indispensable. No same-chart test
belongs in the integration domain. Coordinate seams do not create physical
boundaries. Any auxiliary pair partition theta_a summing to one obeys the
same identity, and mask differences are restored by G2. For nonnegative
partitions the sum of the absolute weights is exactly one. For any fixed
finite signed refinement it is bounded by the product of the two sums of
supremum norms. These give genuine finite-density absolute domination and
finite total variation of the corresponding phase measures.

If local integrations by parts produce weight derivatives, their cancellation
uses the full identities `sum d(chi_i)=0`, `sum d(phi_j)=0`, and their higher
derivatives near K. True face/joint fluxes are not artificial weight derivatives
and cannot be discarded this way. An asymptotic remainder sum is justified
only after each required estimate, or an estimate of the aggregate, is proved.
The elementary bound just given grows with physical normalization; it is
**not** the missing density-uniform remainder dominator.

All connected-component labels remain in G4. For distinct connected components
of M itself, a causal pair is in fact impossible under G-SS: its connected
causal curve would lie wholly in M by ambient containment and join the two
components. This is a consequence of that hypothesis, not an assumption of
componentwise action additivity. Different face components, chart labels or
auxiliary pieces of the same M can still pair, and are not excluded. Without
ambient containment even the former zero statement is unavailable.

## 4. Actual pushforward and the exact unresolved residual

Put q=d/2 and let w be `(V_M/c_d)^(1/q)`. This is an auxiliary scalar phase;
it is **not** a claim that curved intervals obey the flat proper-time law.
Push the actual signed, weighted long pair measure forward by w, calling it
nu. By sections 2–3 it is a finite signed Borel measure of bounded support,
with no atom at zero. Define its cumulative primitive N. Exactly, without an
assumed density or jet,

```math
\begin{aligned}
N_{\chi,\phi}^\delta(w)
 &=\int_{M\times M}\mathbf1_{\{x\preceq y,\ \ell\ge\delta,
                           V_M\le c_dw^q\}}
       \chi(x)\phi(y)\,d\mu_g(x)d\mu_g(y),\\
P^{\ge\delta}_{\chi,\phi}(\rho)
 &=\int_{[0,\infty)}K_d(c_d\rho w^q)\,dN_{\chi,\phi}^\delta(w)\\
 &=-c_d\rho q\int_0^\infty N_{\chi,\phi}^\delta(w)
                       w^{q-1}K_d'(c_d\rho w^q)\,dw.
\end{aligned}\tag{G5}
```

To prove the last equality, express the kernel as minus the integral of its
derivative from w to infinity and apply signed Fubini. Absolute integrability
follows from finite total variation and the integrable absolute derivative
of the polynomial/exponential kernel. N is continued **constantly**, not by
zero, beyond its phase support. There is no discarded endpoint term.

For any real constants b_j, j=1,...,n+1, with n=floor(d/2), subtract their
primitive polynomial and define E by exact division. The existing signed
moments annihilate its derivative polynomial. Rescaling gives the identity

```math
\begin{aligned}
E(w)&=\frac{N(w)-\sum_{j=1}^{n+1}b_jw^j}{w^{q+1}},\\
L^\delta_{\chi,\phi}(\rho)
 &=\beta_dq\,c_d^{-1-1/q}
   \int_0^\infty z^{2q}K_d'(z^q)
             E\bigl((c_d\rho)^{-1/q}z\bigr)\,dz.
\end{aligned}\tag{G6}
```

G6 is an identity for the **actual** cumulative measure, not a conditional
completion theorem. It remains true when E is unbounded or does not tend to
zero. Finite-density integrability follows from G5 and the subtracted
polynomial. Choosing coefficients for which E has a useful averaged bound,
or deriving the nonzero response when it does not, is the general analytic
obligation. The [7D continuation, O9–O16](seven-dimensional-focusing-obstruction.md),
now derives an actual long primitive mode proportional to `w^(7/2)` that no
integer polynomial subtraction removes. Its G6 residual has a nonzero `1/w`
leading term, and its signed response survives in the complete action after
short point cancellation. Smoothness of g, compactness, atomlessness, finite
partitions and G3 do not imply a vanishing or bounded critical residual.

For comparison, a primitive mode `N(w)=w^r` near zero contributes, up to
exponentially small fixed-phase truncation terms,

```math
\begin{aligned}
L_r(\rho)&=-\beta_d r\,c_d^{-r/q}
             \rho^{1+(1-r)/q}M_d(r-1),\\
M_d(j)&=\frac2d\Gamma\left(\frac{2(j+1)}d\right)
          \prod_{k=1}^{n+1}\left(1-\frac{j+1}{k}\right),
\qquad r>0.
\end{aligned}\tag{G7}
```

These are actual convergent signed moments from the existing recurrence.
Logarithmic primitive modes are derivatives of G7 in r, justified by absolute
log-moment integrability. At critical r=q+1 a pure mode survives in odd
dimensions. In even dimensions its pure response is zero but a logarithmic
mode has a nonzero response. Neither sign nor vanishing can be assigned before
the actual geometric primitive is known. The tests compare G7 and its
logarithmic derivative with direct kernel integrals; they do not fit a general
geometric expansion.

## 5. An actual full-partner long producer: thin torus in every dimension

**Theorem (bounded atlas regression).** Let d be any integer at least two,
`X = R^(d-1)/(L Z)^(d-1)`, with its Euclidean quotient metric and induced volume,
and let `M=(-T/2,T/2) x X` with `0<T<L/2`, metric `dt^2-h_flat`.
For every fixed positive temporal cutoff delta and every pair of smooth real
fields near the closed slab, G1's actual signed long contribution tends to
zero. The fields may be signed and may cross any coordinate seam. This is
not a graph-presentation hypothesis and not a theorem for thicker slabs.

**Actual intervals.** A causal path has spatial length at most its time gap,
which is less than T. Two causal lifts of the same endpoints would differ by
a nonzero lattice vector of length at least L, whereas their distances from
the source lift sum to less than 2T. Hence the causal lift is unique. Every
intermediate point lifts into that same flat diamond; projection of the
diamond is injective, since two same-time points in it cannot differ by a
lattice vector of length L. Conversely the diamond projects into the ambient
interval. Monotonicity of time keeps it inside M. Thus its actual volume is
`c_d*(tau^2-r^2)^(d/2)`, with multiplicity one. This proof holds in all these
dimensions, including the two directions in dimension two.

If delta is at least T, the long domain is empty. Otherwise fix
`0<delta<T`. With `q=d/2`, set

```math
\begin{aligned}
H_{\chi,\phi}(\tau,r,\omega)
 &=\int_X\int_{-T/2}^{T/2-\tau}
       \chi(t,p)\phi(t+\tau,p+r\omega)\,dt\,d\mathrm{vol}_X(p),\\
P^{\ge\delta}_{\chi,\phi}(\rho)
 &=\int_\delta^T\int_{S^{d-2}}\int_0^\tau
     r^{d-2}H_{\chi,\phi}(\tau,r,\omega)
       K_d\bigl(c_d\rho(\tau^2-r^2)^q\bigr)\,dr\,d\omega\,d\tau,\\
B^\delta_{\chi,\phi}(w)
 &=\frac12\int_{\max(\delta,\sqrt w)}^T\int_{S^{d-2}}
       (\tau^2-w)^{(d-3)/2}
       H_{\chi,\phi}(\tau,\sqrt{\tau^2-w},\omega)\,d\omega\,d\tau,\\
P^{\ge\delta}_{\chi,\phi}(\rho)
 &=\int_0^{T^2}K_d(c_d\rho w^q)B^\delta_{\chi,\phi}(w)\,dw.
\end{aligned}\tag{G8}
```

Here `p+r*omega` is addition **on the torus**, not chartwise clipping. The
ordinary sphere measure has mass two in dimension two. The displayed B is
used only for `0<w<T^2`, and is zero beyond T squared. The substitution is
`w=tau^2-r^2`; its factor is one-half, including the integrable radial endpoint
singularity when d=2. Absolute Fubini follows either from the original compact
pair integral or its identical absolute-weight version. No endpoint measure,
closing time contact or cross-chart pair has been omitted.

**Derived regularity.** For `0<=w<delta^2/2` the lower bound in the near-zero
formula is just delta. This fixed-lower-bound expression extends smoothly to
`|w|<delta^2/2`, with every square root bounded below by delta divided by the
square root of two. Negative w is used only for this Taylor extension, not to
add acausal pairs to the observable. Express the time integral in H by
`t=-T/2+(T-tau)*s`, `0<=s<=1`. Its Jacobian is exactly `T-tau`; the closing
face contact at tau=T is retained, without a moving-domain differentiation.
The remaining domains are fixed compact sets: `[delta,T]`, `[0,1]`, the torus
and the sphere. Smooth periodic fields, translation on the torus, and the
positive square-root margin imply bounded derivatives in w of every fixed
finite order. Differentiation under these integrals is therefore justified.

In particular, with n=floor(d/2), Taylor's theorem applied to the **actual G8**
produces coefficients and a bound

```math
\begin{aligned}
B^\delta_{\chi,\phi}(w)
 &=\sum_{j=0}^{n}b_jw^j+R(w),\\
b_j&=\frac1{j!}\left.\frac{d^j}{dw^j}B^\delta_{\chi,\phi}(w)\right|_{w=0},
\qquad |R(w)|\le Cw^{n+1},\\
\frac{R(w)}{w^{d/2}}&\longrightarrow0.
\end{aligned}\tag{G9}
```

The constant is finite because the preceding differentiated integrands are
bounded on their fixed domains. For even d, `n+1>d/2`; for odd d it exceeds
`d/2` by one-half. Only `n+1` bounded derivatives of the endpoint fields on
that compact domain are used; the geometry itself is flat and smooth. No
historical C3 hypothesis is asserted in arbitrary dimension.

The whole-half-line signed moments M_d(0),...,M_d(n) vanish. Subtract G9's
polynomial using those moments, rescale by `(c_d*rho)^(-2/d)`, and use the
integrable absolute envelope `z^(d/2)*abs(K_d(z^(d/2)))` for the near-zero
remainder. G9 supplies both the bound and the limit needed for dominated
convergence. The actual finite pair measure above a fixed positive w and the
subtracted polynomial tails give exponentially small normalized terms.
This proves L tends to zero, with its sign in G1, for the stated geometry.
G4 then applies to any finite endpoint atlas with the same cutoff. Unlike G6,
the needed estimate here has been **derived**, not assumed.

This is a new weighted long-sector proof for the stated family, not a claim
that the already written 4D thin-torus full-action corollary is new. It does
not supply the all-dimensional short coefficient or a full-action theorem.
It is a mandatory topology/seam regression of the general interface; its
unique-lift argument does not cover cut loci or arbitrary flat G-SS regions.

## 6. Retaining the successful focusing producer and its complement

The accepted [sphere–circle proof](sphere-circle-focusing.md) uses precisely
the time cutoff in G1. Its F14–F18 construct the actual **aggregate** primitive
for a fixed antipodal neighborhood, including both sphere sheets, the second
arc transition, transverse endpoints, both time contacts and circle partners.
The integrable remainder majorant in F16 is proportional to `a^(-1/4)` in
the transverse distance a to the antipode. It is not the assertion that the
cut set can be discarded because it has zero endpoint measure.

Its phase is `w_F=sqrt(V)`, whereas G5 uses `w=sqrt(V/c_4)`. Consequently the
primitive comparison is `N_G(w)=N_F(sqrt(c_4)*w)`. The cubic primitive jet and
its derived domination survive this constant change of variables. F18 then
gives the **signed G1 contribution** tending to zero, multiplying its pair
limit by minus beta_4. There is no sign or normalization change to the action.
Choose its fixed `a0<pi-delta` as in that proof, so the whole cut neighborhood
lies in temporal long. All minimizing branches and the secondary logarithm
remain in that producer.

A general endpoint partition need not respect the rotational symmetry used
there. We do **not** assert F16 separately for each such cell. Instead G4,
restricted to this same cut neighborhood, restores the entire double sum
**at every density**, and only then F18 applies to the aggregate. This is a
valid way to globalize that estimate; it supplies neither individual cell
limits nor a missing uniform weighted dominator. Chartwise limiting before
restoring the sum would require a stronger theorem.

F20's complement is unchanged: short, off-cut long and positive-excess terms
are all retained. In particular the regime of small reduced sphere/time
coordinates with nonzero circle separation can still be temporally long.
Only the fixed positive-excess part has an immediate exponential bound.
#152 owns the selected short/off-cut/complement proof, and #153 its later
complete deterministic/expected assembly. No whole-slab conclusion follows
from the cut-neighborhood theorem or this partition identity.

## 7. Exact acceptance boundary and residual owners

| #151 obligation | Result here | Unproved remainder / native owner |
| --- | --- | --- |
| Actual general long pushforward with all partners | G5, Borel geometry and finite signed measure; no density postulated | Critical-order estimate or surviving responses for arbitrary G-SS: **#151**, not discharged by G6 |
| Every-dimensional signed normalization | G1, G6–G7 use the existing recurrence; G8–G9 prove an actual thin-torus producer | General geometry and nonzero boundary/partition flux responses: **#151**, coordinated with #149/#150 |
| Full source/target atlas | Constructed finite smooth weights; G3 short locality; G4 and G2 exact restoration, genuine finite-density domination | General density-uniform remainder summability: **#151**; local remainders: #150 |
| Order, volume, interval and expectation hypotheses | Derived conventionally in section 2 without replacing containment by GH | Universal manifold formal encoding/audit: #86; #137 supplies only its checked explicit instances |
| Thin-torus and focusing stress tests | Actual weighted all-dimensional thin-torus long theorem; accepted focusing theorem instantiated after complete partition restoration | Thin-torus formal full limit #138; selected focusing complement #152 and assembly #153; arbitrary caustics still **#151** |
| General producer or complete-action obstruction | **Written 7D complete-action obstruction**, [O3/O9/O15](seven-dimensional-focusing-obstruction.md); no universal producer | **#151** retains general caustic-response classification; #81/#86 own corrected assembly and independent review; issues remain open |

The remaining universal statement is not an admissibility field: starting
from actual G5 for every G-SS metric/region, classify its critical-order signed
responses with all cut/conjugate neighborhoods and moving contacts retained,
then match #150's actual short output. A finite bulk-plus-joint target cannot
be its conclusion unchanged: the continuation's complete 7D action diverges.
The corrected statement there is its explicit complete-action asymptotic,
not a no-caustics replacement of G-SS or an assumed universal counterterm.

The attempted routes and exact failure are now more specific:

1. G3 and finite-density domination do not bound G6 uniformly in density;
   atomlessness supplies no normalized cut-neighborhood estimate.
2. #139's aggregate cubic domination is valid in 4D, not a cellwise jet and
   not dimension-independent. In 7D the next Taylor endpoint power is
   `a^(-10/7)`, which is not integrable.
3. Rather than discard that region, O9–O13 rescale and subtract the three
   actual integrable primitive terms. The resulting integrable remainder
   has a positive, rationally certified nonzero coefficient. O14–O16 retain
   the complement and physical point, turning this into a complete-action
   obstruction rather than an isolated sector diagnostic.

The smallest decisive next step is independent checking of that matched
coefficient and full point cancellation, followed by #81/#86's corrected
coverage statement. Arbitrary Lorentzian caustic classification remains
native #151 work; general short boundary fluxes remain #150 work. No new
catch-all issue, silent core restriction, noncompact extension, shrinking
cutoff, degenerating-angle uniformity or sample-wise claim is introduced.

## 8. Verification boundary

`full_partner_globalization.py` and `test_full_partner_globalization.py` check
the actual thin-torus long density against original causal radial integration,
its nonconstant periodic endpoint correlations, signed/off-diagonal partition
terms, temporal-versus-radial cutoff restoration, the equality convention,
2D angular normalization, high-dimensional critical moments, the exact Stieltjes
identity on a signed atomic phase measure without a density/jet, and the
accepted focusing phase/sign conversion. These are finite diagnostics, not a proof of
the universal estimate or of the standard manifold theorems used above.

```sh
.venv/bin/python -m unittest -v test_full_partner_globalization
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

No Lean, checker, dependency or build input is changed. No fresh Lean audit is
claimed; the existing integrated audit does not verify these written arguments.
The PR records observed checks and browser mathematics separately. Independent
human mathematical review remains under #94/#86. The PR targets the integration
branch with `Refs #151`, not automatic closure language, and remains draft
for review and general-contract coordination. The separate 7D note records its
new written obstruction, exact sign arithmetic and finite diagnostics; it does
not change the verification status of these general foundations.
