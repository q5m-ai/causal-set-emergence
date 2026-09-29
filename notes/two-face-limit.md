# Fixed-cutoff assembly of the flat two-face limits (#67)

**Verification boundary:** this is a conventional proof assembled from the
[short-displacement argument](curved-face-stability.md) and the
[checked long-null theorem](../formal/LONG_NULL_GAP.md). It is **not an
end-to-end Lean proof**. In particular, the geometric short-overlap extension,
its logarithmic asymptotics and the divergence theorem application in #66
remain written mathematics. `TwoFaceAssembly.lean` checks the fixed-cutoff
asymptotic equivalences, cutoff independence and expectation transfer, not the
missing general short limit. The original Lean goals remain unchanged and
unproved. Numerical regressions are not proofs of those goals.

This concerns the original `AdmissibleTwoFace h f` class: two global graphs in
four-dimensional Minkowski space with the original C³ germs, bounded positive
height region, regular joint and strict combined Lipschitz budget. It does
not cover every region with two spacelike faces, the unrestricted Conjecture
1′, other dimensions, curved spacetime, arbitrary null/mixed joints, or
convergence of individual sprinklings. No localization, coarea, limit or
additional noncriticality premise is added to geometric admissibility.

## 1. Statement and the cutoff quantifier

For the unchanged region, action and independently defined joint target, the
conventional theorem is

```math
\begin{aligned}
M&=\{(t,x):f(x)-h(x)\lt t\lt f(x)\},\\
\lim_{\rho\to\infty}\mathrm{continuumMean}(\rho,M)
 &=\mathrm{twoFaceBoundaryIntegral}(h,f)
 =\int_J\coth\theta\,dA_L.
\end{aligned}
\tag{A1}
```

After this deterministic conclusion, the finite-density expectation bridge
implies

```math
\begin{aligned}
\lim_{\rho\to\infty}\mathrm{expectedBDGAction}(\rho,M)
 &=\int_J\coth\theta\,dA_L.
\end{aligned}
\tag{A2}
```

The expectations refer to the separately constructed Poisson law and normalized
discrete BDG action, not to an action defined to equal its proposed limit.

There is an important simplification relative to the suggested G4 route. G3
proves its short coefficient at **every sufficiently small fixed positive
cutoff**, with no cutoff-dependent defect in that coefficient. G1 cancels the
long contribution at **every fixed positive cutoff**. Thus choose one cutoff
in their common range. A subsequent limit of the cutoff to zero is unnecessary.
We remove the auxiliary cutoff from the conclusion by proving the original
full action has the target, not by interchanging limits. Neither uniformity
as the cutoff shrinks nor a density-dependent cutoff is asserted.

## 2. One finite atlas and geometric hierarchy

Write the spatial positive region as Omega and its boundary as S. If Omega is
empty, the region and joint measures vanish and both conclusions are zero.
Otherwise compactness and the original regular C³ boundary supply finitely
many height charts covering a two-sided neighborhood of S. Each chart has a
fixed relatively compact planar domain and a two-sided height interval.
Shrink the domains once so the weighted Jacobians have compact support strictly
inside the original domains. A smaller closed collar lies inside this cover.
The G3 extension uses this same atlas for every source weight, retaining all
products of source weights and collar partition weights on overlaps.
All constructions are in the ambient smooth germs; unrelated exterior zeros
are not mistaken for extra boundary components.

Choose a smooth function equal to one near S and supported in that collar.
Multiply a subordinate finite smooth partition by it to obtain collar weights.
Add finitely many smooth weights covering the remaining compact closed spatial
region. Denote all these weights by the same finite family below. They sum to
one on an **open neighborhood** of the closed positive region, not merely
almost everywhere on its interior:

```math
\begin{aligned}
\sum_{i=0}^{n}a_i&=1,\qquad \sum_{i=0}^{n}\nabla a_i=0.
\end{aligned}
\tag{A3}
```

The complement weights have zero trace on S. They need not have zero gradient
or zero single-face contribution. They may cover positive-height critical
points; no coarea formula is used there. Every weight can be taken smooth and
compactly supported in the common germ neighborhood, then extended by zero.

Fix the chart support margins, collar widths, C³ face bounds, C² weight bounds,
strict spacelike margin and positive joint-angle margins **before** choosing
density. Compactness makes these constants finite. The angle and induced area
margins are consequences of geometry, as proved in
[the joint-geometry layer](../formal/JOINT_GEOMETRY.md), not extra assumptions.
Choose a common positive displacement bound smaller than every chart and
translation margin in (S8) of the short-displacement proof. With a finite family
the minimum is positive and the maximum of the relevant derivative bounds is
finite. Finally choose one strictly smaller positive cutoff. No atlas or
source partition is refined with density.

For the tangent-wedge comparison, use the same induced-area target and the
compact range of positive slopes furnished by the angle margins. Choose the
source weight and bounded regulator of #65 once, uniformly over this range.
Its estimate (W7), used in (S21), has a common finite constant. This is a
superposition of regulated **observables**, not the action of isolated wedge
cells; artificial regulator complements have already been subtracted in #65.

## 3. The exact signed decomposition and all endpoints

Use precisely the cutoff of `shortFuture` and `longFuture`. For a future-causal
displacement let its time component be s, its spatial part b, and put

```math
v=s+|b|,\qquad \sigma=s^2-|b|^2,\qquad
K(u)=(1-9u+8u^2-4u^3/3)e^{-u},\quad c=\pi/24,\quad C_4=4/\sqrt6.
```

The short set has v strictly less than the chosen cutoff; the long set includes
equality. Their disjoint union is the entire future cone, including null
vectors and the vertex. The actual first-endpoint weighted overlaps and short
observables are

```math
\begin{aligned}
V_i(z)&=\int_M a_i(x)\,\mathbf1_M((t,x)+z)\,dt\,dx,\\
S_i(\rho,\delta)&=C_4\sqrt\rho\left[
 \int_\Omega a_i h\,dx
 -\rho\int_{\{z\in J^+(0):v\lt\delta\}}K(c\rho\sigma^2)V_i(z)\,dz\right],\\
L(\rho,\delta)&=-C_4\sqrt\rho\,\rho
 \int_{\{z\in J^+(0):v\ge\delta\}}K(c\rho\sigma^2)V_M(z)\,dz.
\end{aligned}
\tag{A4}
```

At each fixed density all integrands are absolutely integrable: the source and
partner lie in a bounded region, the weights and continuous kernel are bounded
on the relevant compact sets, and the displacement support is bounded. This
justifies Fubini, displacement substitution and finite sums **before** using
signed cancellation. The partition applies to the source only; its partner is
not restricted to the same chart. Consequently

```math
\begin{aligned}
\sum_i V_i&=V_M,\\
\sum_i S_i&=\mathrm{shortContinuumMean}(\rho,\delta,M),\\
\mathrm{continuumMean}(\rho,M)&=\sum_i S_i+L(\rho,\delta).
\end{aligned}
\tag{A5}
```

The point term appears once in this sum. If both endpoints are partitioned,
the identical pair integral instead has a double sum over **all** ordered
labels; off-diagonal labels cannot be discarded. Nothing in (A5) asserts chart
additivity of bilocal region actions. The checked exact short/long identity
and source-partition identities in `ShortDisplacement.lean` use these same
conventions. To prove the weighted short identity itself, for every source
point in M and every displacement use the pointwise equality

```math
\begin{aligned}
\sum_i a_i(x)\mathbf1_M((t,x)+z)
 &=\left(\sum_i a_i(x)\right)\mathbf1_M((t,x)+z)
 =\mathbf1_M((t,x)+z).
\end{aligned}
```

Integrate over the source, multiply by the original signed kernel and integrate
over the common short domain. The finite sum commutes with both integrals by
the absolute integrability just proved. Applying the same finite linearity to
the point terms gives the middle identity in (A5). This is a conventional
proof of weighted short linearity, not a claim that the existing checked
full weighted-action identity alone encodes it, and not an application of a
weighted long-null theorem.

## 4. Short contributions, complement and signed cancellation

Here the input is the conventional proof of #66, not merely its checked exact
partition. Its (S5) and (S6) express each actual causal overlap as a fixed-domain
volume term, a lost single-face slice and a thin joint collar. The C³ height
charts above give the moving collar root and the C³ extension in (S7)–(S11).
The extension agrees with the overlap on the **future cone near zero** only;
no assertion of a smooth global covariogram is used.

Here is the regularity count explicitly. Fix a chart and planar parameter,
and let W be its weighted volume Jacobian. It is C² because the chart is C³
and the source weight is C². Write q for the gap in that chart and eta for its
root; the bound in (S8) gives a positive denominator bounded below by one-half.
Subscripts on q denote partial derivatives at fixed chart height, and those
on eta denote displacement derivatives. The root identity and differentiation
of the oriented integral give

```math
\begin{aligned}
E(z)&=\int_0^{\eta(z)}W(t)[q(t,z)-t]\,dt,
 &\eta_i&=\left.\frac{q_i}{1-q_t}\right|_{t=\eta(z)},\\
E_i(z)&=\int_0^{\eta(z)}Wq_i\,dt,\\
H_{ij}(t,z)&=\frac{Wq_iq_j}{1-q_t},
 &E_{ij}(z)&=\int_0^{\eta(z)}Wq_{ij}\,dt+H_{ij}(\eta(z),z),\\
E_{ijk}(z)&=\int_0^{\eta(z)}Wq_{ijk}\,dt
 +\left[Wq_{ij}\eta_k+\partial_k H_{ij}
             +\partial_t H_{ij}\eta_k\right]_{t=\eta(z)}.
\end{aligned}
```

The first derivative has no upper endpoint term because the gap vanishes
there. The last line uses only one height derivative of W, derivatives of q
through order three, and the controlled inverse denominator. All are continuous
and bounded on the compact chart supports. Displacement differentiation under
the planar integral therefore yields a genuine C³ displacement extension; no C⁴
face or C³ source-weight assumption is needed. Compactness supplies a common
open germ neighborhood and a compactly contained enlargement before choosing
the translation margin. The implicit roots agree on overlapping local root
neighborhoods by uniqueness, hence exist throughout the fixed compact planar
supports for one common sufficiently small displacement ball.

The density is integrated in the same null coordinates as G1. For the cubic
Taylor remainder R, differentiating the moving lower endpoint gives precisely

```math
\begin{aligned}
B_R'''(\sigma)=\int_{S^2}\left[
 \int_{\sqrt\sigma}^{\delta}\partial_\sigma^3(jR)\,dv
 -\frac{\partial_\sigma^2(jR)(\sigma,\sqrt\sigma)}{2\sqrt\sigma}
 \right]d\omega.
\end{aligned}
```

The integrand and its first proper-time derivative vanish at the lower endpoint,
but its second derivative does not. The bulk bound `13T/(8v²)`, the endpoint
bound `T/(8√σ)` and sphere mass `4π` give (S12), whose three right integrations
produce the remainder bound (S13). Subtract its right
quadratic polynomial using all three exact signed moments of the original
kernel; only then apply an absolute bound. Including the full pair
normalization gives the error of order rho to the power minus one quarter in
(S14). The constant is bounded on this one finite atlas. Absolute estimates
on the original unsubtracted pair integral would not suffice.

The four elementary densities (S16) retain both endpoints. The volume
logarithm cancels the entire point term. The linear single-face term has no
surviving logarithm. The quadratic single-face Hessian is **not zero in
general**: (S18) and the divergence identity (S19) give

```math
\begin{aligned}
S_i(\rho,\delta)&\longrightarrow J_i+D_i,\\
J_i&=\int_S a_i\frac{1-|p|^2+p\cdot g}{|g|}\,dA_S,\\
D_i&=\int_\Omega\nabla a_i\cdot p\,dx,
\qquad p=\nabla f,\quad g=\nabla h.
\end{aligned}
\tag{A6}
```

The outward spatial normal is minus g divided by its norm, which fixes the
sign of the joint contribution. The bounded regular C³ domain and the C¹
vector fields on its closure justify the divergence theorem across all
components. All spatial and surface integrals are finite by compactness and
joint nondegeneracy.

For a complement weight the surface term in (A6) vanishes, but its derivative
term generally survives. This explicitly controls the part away from the joint
collar, including any interior critical points. It is **cancellation**, not
absolute vanishing of every artificial patch, that removes the single-face
terms. The same applies to the collar weights: their derivative terms cannot
be thrown away before the finite sum. Equation (A3) gives exactly

```math
\begin{aligned}
\sum_i D_i&=0,\\
\sum_i J_i&=\int_S\frac{1-|p|^2+p\cdot g}{|g|}\,dA_S.
\end{aligned}
\tag{A7}
```

For clarity, (S14) and (S20) provide for each weight a bound

```math
\begin{aligned}
|S_i-J_i-D_i|&\le C_i\rho^{-1/4}+E_{\rho,\delta,i}.
\end{aligned}
\tag{A8}
```

At the fixed positive cutoff every error on the right tends to zero; (S20)
displays the inverse cutoff powers and Gaussian tails explicitly. Since the
number of weights is fixed and finite, summing (A8) proves convergence of the
whole short contribution. No unjustified infinite summation, limit through a
refining atlas, or uniformity in a shrinking cutoff is required. The additional
uniform wedge estimate (S21) compares the same sum to the G2 tangent-wedge
observables; its errors also sum to zero. Thus G2 and G3 are used on one
consistent target and partition, not on incompatible artificial subregions.

## 5. Independent Lorentzian target and the full limit

On the regular joint put the following quantities, with the gradient component
tangent to S taken in its spatial Euclidean metric:

```math
N=1-|p|^2+p\cdot g,\qquad
j_L=\sqrt{1-|p_{\mathrm{tan}}|^2}.
```

The independently defined future unit normals and positive angle obey

```math
\begin{aligned}
N^2-(1-|p-g|^2)(1-|p|^2)&=|g|^2j_L^2,\\
\coth\theta\,j_L&=N/|g|.
\end{aligned}
\tag{A9}
```

All denominators and square-root branches are positive by the unchanged slope
budget and regular compact joint. The measure from #51 is precisely the
spatial joint measure multiplied by this induced Lorentzian Gram density.
Its weighted integral is finite and chart compatible. The spatial area used in
the divergence and coarea calculations is precisely `graphSurfaceMeasure h`:
it is `ENNReal.ofReal (Real.pi / 4) • μH[2]` restricted to `graphJoint h`,
not the unnormalized `μH[2]` of the pinned mathlib version. The checked
scalar-graph area formula identifies this normalization with the classical surface element on the regular
charts. The `withDensity` definition of `twoFaceProjectedArea` then gives
exactly the factor in (A9). Therefore (A7) is the unchanged
`twoFaceBoundaryIntegral`, not ambient Euclidean spacetime area or a target
defined by an action calculation.

The wedge comparison is also measurable: at a fixed positive density its scalar
observable is continuous in the slope on the fixed compact positive slope
interval, by its reduced integral formula and compact domination. Compose this
with the continuous joint angle and integrate against the finite induced area.
No measurable selection of Lorentz frames is required.

Apply `AdmissibleTwoFace.tendsto_normalized_longOverlap` from #61 at the **same**
fixed cutoff. Its actual unweighted overlap, original signed kernel and full
normalization are exactly L in (A4); it tends to zero with no analytic input
from the caller. It treats translated contacts rather than discarding a null
exceptional set. No assertion about a weighted long piece is needed: sum the
source weights before applying this unweighted theorem.

Combining (A5), (A7)–(A9) gives the explicit assembly estimate

```math
\begin{aligned}
&\left|\mathrm{continuumMean}(\rho,M)-\int_J\coth\theta\,dA_L\right|\\
&\qquad\le |L(\rho,\delta)|+\sum_i\left(C_i\rho^{-1/4}+E_{\rho,\delta,i}\right)
\longrightarrow0.
\end{aligned}
\tag{A10}
```

This proves (A1) as a conventional theorem for the full original two-graph
class. The theorem is independent of the arbitrary chosen small cutoff.
Indeed the checked identity and G1 already imply that short actions at any two
fixed positive cutoffs have difference tending to zero, even before their
common limit has been identified. This fact does not justify substituting a
cutoff depending on density, and no such substitution appears in the proof.

## 6. Expectation transfer, only after deterministic assembly

The unchanged region theorem #60 makes M bounded, measurable and ambient
causally convex. At every positive density the independently proved bridge
`BoundedCausalRegion.expectedBDGAction_eq` identifies the expectation with
`continuumMean`. Positive densities are eventual as density tends to infinity.
Replacing a function by an eventually equal one in (A1) proves (A2). No
probabilistic approximation, coupling, variance bound, convergence in
probability or almost-sure convergence is used or inferred.

## 7. Regressions, formal boundary and correction history

- **Original planar caps:** zero future graph reduces the target to the existing
  reciprocal-gradient boundary integral. `TwoFaceAssemblyRegression.lean`
  derives an unconditional planar short limit from the old full graph-cap
  theorem and G1, retaining exactly the original hypotheses.
- **Interior critical points:** `GraphCapRegression.lean` retains the quartic's
  positive-height critical point and now applies the fixed-cutoff short limit
  to that same profile. The written construction never uses collar coarea
  through a critical point.
- **Unequal axes:** the same regression recovers the original ellipsoid value
  with the original positive-axis and strict slope hypotheses. The prior
  canonical-area and expected-action regressions are unchanged.
- **Genuinely curved future face:** the existing sine example retains its
  nonaffinity witness while exercising the checked cutoff-independence result.
  Its full limit here is conventional, not a newly checked Lean limit.
- **Separate null cap:** its old deterministic and expected limits remain
  separate unconditional results with the original algebraic target. It is
  not obtained by degenerating the positive angle in this theorem.
- **Signed assembly diagnostics:** `test_two_face_assembly.py` exercises three
  overlapping source weights, nonzero artificial derivative terms that cancel
  only in the sum, an independent geometric target, the exact short annulus
  across the cutoff endpoint, and distinct fixed cutoffs with large opposing
  changes in short and long pieces. Floating-point tolerances are regression
  thresholds, not certified error bounds or evidence of a new theorem.

The history matters: exact overlap reductions did not supply G1's geometric
jet; its moving-contact and averaging gaps were repaired in #61. The false
uncompensated patchwise claim in G3 was corrected by retaining the derivative
term. Finally, G4's initially suggested cutoff-removal stage is replaced here
by the stronger fixed-cutoff short proposition, **not** by silently asserting
uniform long-null cancellation. The original action, region, induced-area
target, admissibility and goal definitions are unchanged.

The new Lean module proves equivalences and unconditional asymptotic
**differences**. It cannot be cited as a proof term of `TwoFaceLimitGoal` or
`TwoFaceExpectedLimitGoal`. An end-to-end encoding still requires formalizing
the geometric short-overlap extension, signed logarithmic asymptotics and
spatial divergence calculation used above. A conventional theorem and a
machine-checked theorem are distinct deliverables.

## 8. Independent scrutiny and remaining review boundary

Two independent AI readers (GPT-6 Astra and GPT-5.6 Sol, in fresh contexts)
examined the G3 analytic argument and the proposed fixed-cutoff assembly against
base `faee2e3`. Both found the stated regularity, signed constants, endpoint
term and divergence signs sufficient for the unchanged class. They requested
more explicit collar differentiation, weighted-short linearity, normalization
and measurability details rather than stronger hypotheses. Those details are
now included above. Their subsequent source-level reads of this note and the
new assembly/regression Lean files found no remaining mathematical blocker;
the displacement-differentiation wording was clarified in response.

This is **independent AI scrutiny, not expert peer review or a Lean audit**.
The conventional theorem still awaits independent human mathematical review.
The local warnings-as-errors/source/transitive-axiom gate validates only the
encoded declarations; it cannot validate the unencoded G3 analysis. Reproduce
that gate with `(cd formal && ./check.sh)`, and run the Markdown, Python and
symbolic checks described in the repository README. No claim about the
unrestricted conjecture or individual random sprinklings is promoted by these
checks.
