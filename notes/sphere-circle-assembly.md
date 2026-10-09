# Complete 4D sphere-circle action and expectation (#153)

**The complete deterministic action tends to the independently defined bulk
`320*pi`; the genuine Poisson expectation has the same limit.** This is a
conventional written theorem for the fixed geometry below, consuming actual
integrated producers, not a conditional theorem with sector conclusions in
admissibility. The finite-density measured-order bridge is already Lean-checked;
this assembly and its analytic predecessors are **not** compiled asymptotic
proofs or independent human mathematical review. #81/#24 remain open.

## 1. Inputs and fixed theorem scope

Starting integration revision: `97cd77e10cf0a45c338906080c5d24c598235fdd` on
`issue-81-general-coverage`. All three native prerequisites are ancestors:

| Input | Integrated source used, not administrative issue status |
| --- | --- |
| #139 / PR #147 | Merge `0bfc8bb3d6dce188c39414fedef5e0a3bd646dd5`; [actual interval, full pair reduction, cut primitive and F20](sphere-circle-focusing.md), especially F1–F4 and F11–F18 |
| #152 / PR #160 | Merge `b3b3670ec2d19403459fb53372dd3f278fa580f1`; [actual matched complements](sphere-circle-complements.md), SC1–SC15 and section 6 |
| #137 / PR #146 | Merge `b86f5dadddaeb6a11299557ff28781e9b33ed743`; [checked selected measured order and original-law bridge](../formal/COMPACT_MEASURED_ORDER.md) |

Fix physical dimension four, sphere radius one, circle **circumference** 20,
and slab width four. Time orientation is increasing t. In the normalization
of [#90, section 2](general-contract.md#2-independent-action-order-and-geometric-target),
the observable is the unsmeared minimal-layer action, namely the physical
`l_p^2*S/hbar`. No metric, region, action, target or law varies with density.
The selected order is the ambient causal order restricted to the slab, not
an auxiliary order obtained by deleting the cut locus:

```math
\begin{aligned}
X&=S^2_1\times(\mathbb R/20\mathbb Z),\
g&=dt^2-h_{S^2_1}-db^2,\
M&=(-2,2)\times X,\
D(p,q)&=\sqrt{\theta(p,q)^2+\mathrm{dist}_{S^1_{20}}(p_b,q_b)^2},\
(t,p)\preceq(s,q)&\quad\Longleftrightarrow\quad D(p,q)\le s-t.
\end{aligned}\tag{SA1}
```

Here theta is round great-circle distance, not chord distance. The circle
uses its shortest quotient distance; the product uses the Euclidean
square-root-of-squares distance, not a maximum. The theorem has no
no-conjugate-points, unique-sphere-geodesic, small-curvature, chart-disjointness,
or assumed overlap-jet hypothesis.

### Geometric admissibility in the exact G-SS contract

The product is a smooth time-oriented Lorentzian manifold. X is compact and
complete. Along any future causal curve parameterized by time, spatial speed
is at most one. Conversely a minimizing spatial geodesic traversed at speed
at most one realizes every relation in SA1. Completeness supplies such a
geodesic even at antipodes; uniqueness is unnecessary. Thus SA1 is the actual
ambient causal relation, not merely a sufficient coordinate test.

The temporal coordinate gives strong causality. A closed causal diamond lies
in a compact closed time interval times X and is closed by continuity of D,
so it is compact. Equivalently, an inextendible causal curve cannot have a
finite time endpoint: its spatial component is then Cauchy and has a limit,
from which the curve extends. Each constant-time slice is Cauchy. The ambient
product is globally hyperbolic, and the same argument on the open time interval
gives intrinsic global hyperbolicity of M.

**Ambient containment is proved separately.** If x,y belong to M and
x precedes z precedes y, time monotonicity puts z's time between their times,
strictly inside (-2,2). There is no spatial restriction to check. Hence every
closed ambient interval with endpoints in M is contained in M, including
null intervals. Every ambient causal curve between these endpoints stays in
M, so the intrinsic and restricted ambient orders agree. This is stronger
than merely asserting intrinsic global hyperbolicity.

M is nonempty, open and precompact with closure `[-2,2] x X`. Its entire
frontier consists of the two compact embedded smooth hypersurfaces
`Sigma_-={-2} x X` and `Sigma_+={2} x X`. Each is achronal and spacelike,
with induced positive metric h. They are respectively past and future faces,
have empty boundaries, and have empty common joint J. There is no lateral
wall, null boundary, tip, crease or additional corner. Sphere polar coordinates
and the circle fundamental-domain seam introduce no physical stratum. The
transverse-normal condition at J is vacuous: **no value of coth at zero angle
is evaluated**. These facts verify every geometric clause of #90's G-SS core;
no analytic sector conclusion was used.

The example retains interior null focusing: the events at times minus/plus
pi/2 with north/south sphere positions and equal circle position are inside
M, null-related and joined by all minimizing meridians. This is not the
null-boundary branch of #134. Nor is it a conformal-pilot instance: the
independent product contraction gives nonzero Weyl square `4/3`.

## 2. Independent target, measures and canonical deterministic action

In a regular sphere chart the metric is
`diag(1,-1,-sin(theta)^2,-1)`. Its nonzero connection coefficients are
`Gamma^theta_phi,phi=-sin(theta)*cos(theta)` and
`Gamma^phi_theta,phi=Gamma^phi_phi,theta=cot(theta)`.
Using exactly #90's Riemann sign convention, the sphere Ricci components are
`-1,-sin(theta)^2`, and time/circle components vanish. Contracting with the
inverse Lorentzian metric gives scalar curvature two. Smoothness extends this
scalar through the coordinate poles. This computation (also SC15 and
`general_metric_gate.product_curvature`) is independent of interval-volume
jets, action coefficients and the limit being proved. Therefore

```math
\begin{aligned}
d\mu_g&=dt\,dA_{S^2}\,db,\
\mu_g(M)&=4\,(4\pi)\,20=320\pi,\
\mathcal T(M,g)&=\frac12\int_M R_g\,d\mu_g
                   +\int_{\varnothing}\coth\theta\,dA_g=320\pi.
\end{aligned}\tag{SA2}
```

The spatial volume is area times **length**, not probability-normalized Haar
measure. Let mu denote its spacetime restriction to M. Define the exclusive
interval by removing exactly the selected endpoints from the closed order
interval. Endpoint atomlessness and the containment just proved identify its
mu-volume with the full ambient interval volume V. Time Fubini then gives
F1: at intermediate spatial point z the allowable time length is
`(tau-D(p,z)-D(z,q))_+`. In particular this is the actual interval, not the
flat proper-time formula or a sum of overlapping geodesic diamonds.

With both endpoint measures retained, the unchanged deterministic action is

```math
\begin{aligned}
K(z)&=(1-9z+8z^2-\tfrac43z^3)e^{-z},\
P(\rho)&=\int_M\int_{M\cap J^+(x)}K(\rho V(x,y))\,d\mu_g(y)d\mu_g(x),\
\mathcal A_\rho&=\frac4{\sqrt6}\sqrt\rho\,[320\pi-\rho P(\rho)],
\qquad \rho>0.
\end{aligned}\tag{SA3}
```

V is jointly measurable by the exclusive interval indicator and parameter
integration; it lies between zero and mu(M). At fixed positive density the
continuous kernel is bounded on that compact phase interval. Finite product
measure therefore gives absolute integrability before any signed Fubini or
finite partition. The closed causal mask is retained. Its null boundary has
zero pair measure: for a fixed source and target spatial position its arrival
time is the singleton `t+D(p,q)`. Time Fubini works also at antipodes. This
nullity justifies integral endpoint conventions, **not** deleting null-related
elements from finite-order interval counts.

## 3. One fixed cutoff and exact finite-density restoration

Choose a sufficiently small positive delta in the actual analytic radius
constructed in SC3–SC11, also below 1/4. Then choose a0,e0 in the **proved**
F11–F13 ranges, shrinking them if needed, with the following inequalities.
Choose the fixed phase cap v0 in SC5–SC10 also below F14's cap after conversion:

```math
\begin{aligned}
0&\lt\delta\lt\tfrac14,\qquad
0\lt a_0\lt\pi-\delta,\qquad d=\pi-a_0>\delta,\qquad
0\lt e_0\lt4-\pi,\
c&=\frac\pi{24},\qquad C=160\pi^2,\qquad
v=\sqrt{W/c},\qquad w=\sqrt W=\sqrt c\,v,\qquad
z=\sqrt{c\rho}\,v=\sqrt\rho\,w.
\end{aligned}\tag{SA4}
```

The displayed inequalities alone are not a substitute for the producers'
smallness ranges. All choices are made **once before density varies**. There
is no limit in delta, a0, e0 or v0 and no uniformity as they shrink.

For a causal pair let tau be original time separation and b shortest signed
circle separation. Since `|b|<=tau<4<10`, the interval has the unique circle
lift used in F1; no sphere lift is asserted. Its actual volume is
`W(u,theta)` with `u=sqrt(tau^2-b^2)`. Integrating the source spatial volume,
target sphere azimuth, both endpoint times and circle separation gives F2–F3:

```math
\begin{aligned}
G(u)&=2u\,[4\,\mathrm{arcosh}(4/u)-\sqrt{16-u^2}],\
G_s(u)&=\mathbf1_{\{u\lt\delta\}}\,2u
 [4\,\mathrm{arcosh}(\delta/u)-\sqrt{\delta^2-u^2}],\
G_o(u)&=G(u)-G_s(u),\
I(H;D_*)&=C\int\!\!\int_{D_*}\sin\theta\,H(u)
 K(\rho W(u,\theta))\,du\,d\theta.
\end{aligned}\tag{SA5}
```

G_s uses the displayed expression only on `0<u<delta` and is zero otherwise;
endpoint values are understood by continuous extension where appropriate.
The factor **4** is the original slab width, not delta. Short is `tau<delta`,
and equality belongs to long, even when theta and u tend to zero. In the
original pair space, allocate long first by `theta<d` or `theta>=d`, then the
latter by `u<theta+e0` or `u>=theta+e0`. These are disjoint and exhaustive.
Since `theta>=d>delta` forces `tau>delta`, their reduced weighted integrals are
exactly the F20 pieces:

```math
\begin{aligned}
P_s&=I(G_s;\ 0\le\theta\le\pi,\ \theta\le u\le4),\
P_o&=I(G_o;\ 0\le\theta\le d,\ \theta\le u\le4),\
P_c&=I(G;\ d\le\theta\le\pi,\ \theta\le u\le\theta+e_0),\
P_e&=I(G;\ d\le\theta\le\pi,\ \theta+e_0\le u\le4),\
P&=P_s+P_o+P_c+P_e.
\end{aligned}\tag{SA6}
```

The duplicated equality boundaries in the integral notation are null. This
is an equality at **every positive density**, not an asymptotic identification.
G_s and G_o can both be nonzero at the same reduced coordinates because they
integrate different original b/time partners. Consequently their overlapping
reduced supports do not double-count a pair.

Allocate the entire physical point term exactly once to short:

```math
\begin{aligned}
S_\delta&=\frac4{\sqrt6}[320\pi\sqrt\rho-\rho^{3/2}P_s],\
L_j&=-\frac4{\sqrt6}\rho^{3/2}P_j\quad(j=o,c,e),\
\mathcal A_\rho&=S_\delta+L_o+L_c+L_e.
\end{aligned}\tag{SA7}
```

There is no local point allocation to each of the four sectors. Likewise,
if finite endpoint partitions chi_i,psi_j are introduced, insert the entire
ordered double sum `sum_i,j chi_i(x)*psi_j(y)=1` into P and
`sum_i,j chi_i(x)*psi_j(x)=1` into the point integral. Bounded weights and
finite measure justify those identities. Restore that sum **before** product
symmetry or F18; #139 does not prove an arbitrary weighted-cell cut jet.
Keeping only matching chart labels is a different observable.

### Boundary and partner ledger

| Boundary / partner set | Finite-density retention and actual analytic treatment |
| --- | --- |
| Diagonal and physical point | Pair diagonal is product-null, but SA7 retains the physical point once; SC12–SC14 retain both logarithms giving its cancellation and the finite term |
| Original `tau=delta`, reduced `u=delta` contact | Strict-short/equality-long allocation; same moving Rdelta in SC6/SC9, SC7 root derivatives, exact upper root in SC10; no frozen boundary |
| Long circle partners with `theta,u -> 0` | G_o remains present; equivalently SC6 keeps m near either circle-axis direction and r at least delta/2 |
| Closing `tau=4` and reduced `u=4` | The original `4-tau` weight, G and moving R4 remain; SC7 retains derivatives even where the boundary integrand vanishes |
| Artificial `theta=d` | Off-cut Rd and its moving upper-time intersection m_* in SC6–SC7; the unchanged lower edge of the aggregate cut integral |
| Artificial cut cap `u=theta+e0` | F14's actual capped primitive plus the entire P_e of SA6, with its positive actual phase minimum |
| Secondary transition `u=2*pi-theta` and antipodal meridians | F4's full two-sheet spatial measure and F13–F16's summable primitive on both sides, not a differentiable density assumed through the transition |
| `theta=0,pi`, circle seam, null `u=theta` | Full geometric measures and causal partners; null coordinate boundaries do not justify discarding normalized neighborhoods |
| Fixed phase caps v0,w0 | Boundary term in cut integration by parts, all subtracted polynomial/log tails and actual above-cap domains retained until positive-phase estimates |
| Artificial endpoint partitions | All ordered source/target cells, including off-diagonal labels, restored before any aggregate cut cancellation |

Thus no physical face, contact strip or artificial boundary is dropped on the
basis of its zero measure alone. The producers estimate its neighboring
integrals and moving-root derivatives. In particular neither an isolated
transition-sector response (F19) nor a local curvature coefficient replaces
the full P_c or P_s.

## 4. Complete deterministic conclusion

The inputs are actual integral theorems, with the following remainder receipts:

- **Short:** SC4–SC12 construct the actual phase inverse and density. Its
  analytic quadratic polynomial is retained, followed by
  `C*v*log(v)+(C/8)*v^2*log(v)+v^2*epsilon_s(v)` where
  `|epsilon_s(v)|<=C_s*v*(1+|log(v)|)` and epsilon_s tends to zero. This is
  uniform in the compact direction parameter, including the circle axis.
- **Off-cut:** SC6–SC8 include both time roots and the outer moving contact.
  On fixed rectangles the third derivative is bounded, giving an actual
  quadratic density plus `v^2*epsilon_o(v)`, with `|epsilon_o(v)|<=C_o*v`.
- **Cut:** F14–F18 use the actual aggregate primitive
  `N_c(w)=n1*w+n2*w^2+n3*w^3+w^3*epsilon_c(w)`. The bounded epsilon_c tends
  to zero by the **integrable** antipodal-parameter majorant `a^(-1/4)`.
  No pointwise quadratic density jet at the antipode is used.
- **Excess:** the compact SA6 domain with positive fixed excess e0 has
  `W>=nu>0`. Its finite pair mass bounds the normalized integral by a constant
  times `rho^(3/2)*(1+rho^3)*exp(-rho*nu)`, which tends to zero.

For clarity, the signed moment and normalization steps behind these receipts
are compatible, not additional hypotheses. The moment identity below holds
for real `j>-1`; its derivatives at one and two are justified by integrable
log-weighted domination:

```math
\begin{aligned}
J(j)&=\int_0^\infty z^jK(z^2)\,dz
 =-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2),\
J(0)&=J(1)=J(2)=0,\
J'(1)&=\frac1{12},\qquad J'(2)=-\frac{\sqrt\pi}{12},\
\frac{C}{12c}&=320\pi,\qquad
\frac{C\sqrt\pi}{96c^{3/2}}=80\sqrt6\,\pi.
\end{aligned}\tag{SA8}
```

The three zero moments remove the actual analytic polynomials only after
subtraction. The two logarithmic moments remove the possible log-density
terms and produce the two short coefficients, including the point term.
Short/off-cut remainder rescaling is dominated by a constant times
`z^2*|K(z^2)|`. Cut integration by parts is dominated by
`z^4*|K'(z^2)|`. Both are integrable; the corresponding bounded epsilons
tend pointwise to zero after rescaling. All artificial phase-cap boundary
terms and actual/subtracted tails have a fixed positive phase and decay.
These facts are precisely the summable estimates proved in the cited
producers, not a new assumption that smooth geometry implies cancellation.
They give, for our single fixed compatible cutoff,

```math
\begin{aligned}
P_s(\rho)&=\frac{320\pi}{\rho}
 -\frac{80\sqrt6\,\pi}{\rho^{3/2}}+o(\rho^{-3/2}),\
\rho^{3/2}P_o(\rho)&\longrightarrow0,\qquad
\rho^{3/2}P_c(\rho)\longrightarrow0,\qquad
\rho^{3/2}P_e(\rho)\longrightarrow0.
\end{aligned}\tag{SA9}
```

**Deterministic theorem.** For the fixed SA1 geometry and the canonical
SA3 action, SA6 and SA9 imply the complete pair expansion and hence

```math
\begin{aligned}
P(\rho)&=\frac{320\pi}{\rho}
 -\frac{80\sqrt6\,\pi}{\rho^{3/2}}+o(\rho^{-3/2}),\
\lim_{\rho\to\infty}\mathcal A_\rho
 &=\frac4{\sqrt6}\,80\sqrt6\,\pi
 =320\pi=\mathcal T(M,g).
\end{aligned}\tag{SA10}
```

Proof: the sum of the four normalized remainders tends to zero because there
are finitely many and their parameters are already fixed. Substituting into
SA3 cancels the entire physical point and leaves exactly the displayed finite
coefficient. Equivalently, SA7 has limits `320*pi,0,0,0`. This is the whole
action, not a surviving-sector claim. A second compatible fixed cutoff gives
the same SA3 action at every density by SA6, and thus the same conclusion;
no density-dependent cutoff or uniform exchange of limits follows.

SA2 determined the target without SA8–SA10. Agreement is therefore an output.
This geometry supplies a positive instance of the stated 4D contract, not a
counterexample and not a corrected universal theorem.

## 5. Separate transfer to the genuine original-law expectation

Only now use #137. The selected space and measure in Lean are
`Real x SphereCircle.Space 20` and `SphereCircle.slabVolume 20 4`.
The following are existing checked declarations, not new assumed premises:

| Required finite-density fact | Existing implementation |
| --- | --- |
| Actual angular/shortest-circle/product distance, closed measurable order | `RoundSphereDistance.lean`, `SpatialDistance.lean`, `UltrastaticMeasuredOrder.lean`, `SphereCircle.distance_eq` |
| Standard Borel space, finite atomless geometric measure and mass | `SphereCircle.standardBorel`, `.sphereArea_eq_induced`, `.spatialVolume_univ`, `.slabVolume_univ`; `CompactMeasuredOrderRegression.lean` specializes mass to `320 * Real.pi` |
| Ambient closed containment and exclusive/ambient volume equality | `SphereCircle.interval_subset_slab`, `.intervalVolume_ambient` |
| Actual interval/layer/kernel measurability and factorial integrability | `MeasuredOrderBDG4.measurable_intervalVolume`, `.measurable_discreteAction`, `.integrable_discreteAction`, and reused `MeasuredOrderPoisson` |
| Unchanged 4D observable and deterministic normalization | `MeasuredOrderBDG4.discreteAction_eq`, `.action_eq` |
| Constructed original-law bridge at every positive density | `SphereCircle.expectation_eq 20 4`, specialized from `MeasuredOrderBDG4.expectation_eq` |

The actual law is `FinitePoisson.law (ENNReal.ofReal rho • mu)`;
`SphereCircle.probability 20 4 rho` is its abbreviation. There is no second
sprinkling law and no expectation equality in geometry.
`Ultrastatic.ae_supported_layers` proves that its configurations are almost
surely supported in M and simple, and that their layers equal the cardinalities
of the actual ordered-pair sets. Thus this is a genuine finite causal order.
If N is cardinality and L_k counts ordered distinct related pairs with exactly
k other elements in their **closed** interval, the normalized observable and
its integrability bound are

```math
\begin{aligned}
A^{\mathrm{disc}}_\rho(C)
 &=\frac4{\sqrt6\sqrt\rho}\,[N-L_0+9L_1-16L_2+8L_3],\
|A^{\mathrm{disc}}_\rho(C)|
 &\le\frac4{\sqrt6\sqrt\rho}\,[N+34N(N-1)].
\end{aligned}\tag{SA11}
```

The original finite law has mean cardinality `rho*mu(M)` and finite second
factorial moment. Reduced two-point Mecke and the actual exclusive-interval
Poisson counts give the already-proved identities

```math
\begin{aligned}
\mathbb E_\rho N&=\rho\mu(M),\
\mathbb E_\rho L_k&=\rho^2\int_M\int_{M\cap J^+(x)}
 e^{-\rho V(x,y)}\frac{(\rho V(x,y))^k}{k!}\,d\mu(y)d\mu(x),\
1-9z+16\frac{z^2}{2!}-8\frac{z^3}{3!}
 &=1-9z+8z^2-\tfrac43z^3.
\end{aligned}\tag{SA12}
```

Only the selected endpoints are removed from interval counts. Null-related
interior points remain, antipodal pairs remain, and there is no unordered
factor one-half. Atomlessness permits dropping the diagonal in the integral,
not in the definition of the discrete layers. Both density factors in the
pair mean and the single one in the point mean are essential.

SA1–SA3 identify the geometric input to `.action_eq` with F1/F2's **actual**
P, using containment, time Fubini and the already-proved all-partner reduction.
Consequently `.expectation_eq` gives, for every positive density,

```math
\begin{aligned}
\int A^{\mathrm{disc}}_\rho(C)\,
 d\mathrm{FinitePoisson.law}(\rho\mu)(C)
 &=\frac4{\sqrt6}\sqrt\rho\,[320\pi-\rho P(\rho)]
 =\mathcal A_\rho,\
\lim_{\rho\to\infty}\int A^{\mathrm{disc}}_\rho(C)\,
 d\mathrm{FinitePoisson.law}(\rho\mu)(C)
 &=320\pi=\mathcal T(M,g).
\end{aligned}\tag{SA13}
```

The second line follows from the **previous deterministic theorem** and the
first line, not from a presumed interchange of limit and expectation under
a varying law. The notation in SA13 denotes that original constructed law,
not a new distributional definition. No variance, probability, almost-sure
or sample-wise convergence is asserted.

## 6. Acceptance, residual owners and verification boundary

| #153 acceptance item | Discharged here |
| --- | --- |
| Complete normalized deterministic conclusion, not isolated sectors | SA3, exact SA6–SA7, actual remainder receipts and SA9–SA10 |
| Every finite-density boundary and point allocation | Section 3's full ledger; original strict temporal cutoff, both F3 weights, all F20 pieces, point once and full ordered endpoint sum |
| Independent canonical bulk/joint target and exact admissibility | Sections 1–2: every G-SS clause, ambient containment separately, #90 curvature sign, induced volume, empty joint |
| Genuine separate expectation transfer through accepted #137 | Section 5, unchanged law/action, actual interval identification, finite integrability, both factorial density factors and SA13 |
| Fixed parameters, scope and residual coverage | SA1/SA4 and the ledger below; no hidden uniform/shrinking-cutoff claim |

| Coverage axis | What this complete focusing example establishes | Still open / owner |
| --- | --- | --- |
| General metric, bulk and topology | One fixed nonconformally-flat 4D compact-Cauchy slab, nonzero independent curvature bulk, sphere cut/conjugate locus and circle seams all retained | Arbitrary smooth metrics, dimensions and global regions remain #81; #150's general short work does not supply the missing universal long theorem |
| Focusing / full partners | Actual aggregate cut primitive plus matched long-circle and short contributions suffice in this geometry | No arbitrary caustic classification or weighted-cell cut estimate; #151/#81 retain the universal nonlocal and corrected-statement obligations |
| General scope | A complete positive 4D case, not evidence overriding different-dimensional full-action obstructions | No inference to the separately studied 7D sphere-product conclusion; corrected **general** theorem remains #81/#86/#24 |
| Boundary / joint | Exactly two compact spacelike faces and empty joint | General nonempty variable-angle joints and null/mixed/extra strata not discharged; #154–#156 and #81 retain their own inputs |
| Probability | Exact original-law mean at positive density and its limit for this selected geometric order | No new arbitrary-manifold instance, rate, variance or sample-wise theorem |
| Compiled verification | Reuse the checked #137 finite-density foundation | #86 still owns formal ports of the actual interval/pair reductions, summable cut/complement producers, curvature/admissibility arguments and SA10/SA13; no formal limit with those results as geometry fields |
| Independent scrutiny | Written source-linked proof and separately testable finite identities | Independent human mathematical/physical review remains #94/#86; automated checks are not that review |

The general contract and historical predecessor receipts are unchanged. No
success here closes #81 or #24, narrows their universal quantifiers, or supplies
a corrected general theorem. Noncompact tails, finite-regularity relaxations,
degenerating angles, shrinking cutoffs, rates and timelike Conjecture 2 are
outside this result.

`sphere_circle_assembly.py` and `test_sphere_circle_assembly.py` provide
finite-density full/sector and layer-accounting checks using the actual
interval integrals, negative controls for omitted sectors/point/density
factors, finite-order null/antipodal/seam controls, and independent curvature
normalization. They are diagnostics, not numerical proofs of SA9 or SA10.

```sh
.venv/bin/python -m unittest -v test_sphere_circle_assembly
.venv/bin/python sphere_circle_assembly.py
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```

This contribution changes no Lean source, checker, dependency or build input;
no fresh Lean audit or compiled asymptotic theorem is claimed. Local tests,
GitHub equation rendering, CI and the single bounded feedback snapshot are
reported on the PR separately from mathematical acceptance. No merge,
deployment, agent launch or automatic issue closure is authorized.
