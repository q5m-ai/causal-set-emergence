# Short-displacement stability for two curved faces (#66)

**Status: conventional analytic proof, awaiting independent mathematical review.**
The argument below covers the unchanged `AdmissibleTwoFace` class, in its
specified global two-graph coordinates. It is **not an end-to-end Lean proof**.
`ShortDisplacement.lean` checks the exact short/long split and finite source
partition only; the collar extension, logarithmic asymptotics, divergence
calculation and curved-face comparison below are not checked Lean declarations.
The numerical tests are finite-density diagnostics, not proofs.

The result is local in **displacement**, at a fixed sufficiently small positive
cutoff. It neither assumes #61 nor proves long-null cancellation, a complete
two-face action/expectation limit, G4, or sample-wise convergence. It uses the
[existing region contract](two-face-contract.md), the [exact overlap
representation](../formal/TRANSLATED_OVERLAP.md), and the [regulated wedge
coefficient](regulated-tangent-wedge.md). No action, joint target or admissibility
field is changed.

## 1. Gap found before repair: a weighted patch has an extra term

A spatial first-endpoint weight is not innocuous when the future face curves.
Its short-displacement limit generally contains

```math
\begin{aligned}
D_a&=\int_\Omega \nabla a\cdot\nabla f\,dx.
\end{aligned}
\tag{S1}
```

It is incorrect to compare each such observable directly with just the weighted
joint coefficient, or to discard its single-face term. The repair below
**derives** (S1), retains it in each patch, and cancels it by the differentiated
partition identity only after summing all sources. It is an artificial-cutoff
term, not an extra term in the unweighted action. This corrects a possible
interpretation of G3, not the original theorem contract. In the future-plane
rest frame used in #65 it is zero because the future gradient is zero.

For example, choose a nonnegative smooth weight supported strictly inside a
region where the future Laplacian is positive. Integration by parts gives
$`D_a=-\int a\,\Delta f\lt 0`$, while its joint trace is zero. Such regions occur
in the admissible radius-four sine example near $`x=(-\pi/2,0,0)`$. Taking a
small supported weight there gives a genuine admissible counterexample to
**uncompensated patchwise short-action localization**, not to the unweighted
conjecture or to localization of the full weighted action including long pairs.
No long-pair limit for that weight is assumed here.

## 2. Fixed cutoffs, exact domains, and the proposition

Write, in the contract's spatial Euclidean coordinates,

```math
\begin{aligned}
\Omega&=\{h>0\}, & S&=\partial\Omega, & M&=\{f-h\lt t\lt f\},\\
p&=\nabla f, & g&=\nabla h, & k&=|g|, & \nu&=g/k\quad\text{on }S.
\end{aligned}
```

Thus the outward spatial normal is minus the displayed inward normal. The
empty region has zero contributions throughout; below consider the nonempty
case. Compactness, C³ germs, regularity of the joint and the strict slope
budget are exactly the existing hypotheses. Positive-height critical points
are allowed. Let the real weight be C² on a neighborhood of the closed spatial
region. Smooth compactly supported weights and the constant one are included;
no sign condition is imposed. It is attached to the **first endpoint only**.
For collar constructions one may first multiply by a smooth cutoff equal to
one near the compact closed region and supported in the weight's C² domain,
then extend by zero. This supplies a global C² representative without changing
any source value or derivative used below.

For a future-causal displacement, use the following notation and keep the
original signed kernel and interval coefficient:

```math
\begin{aligned}
z&=(s,b), & r&=|b|, & v&=s+r, & \sigma&=s^2-r^2,\\
c&=\pi/24, & K(x)&=(1-9x+8x^2-4x^3/3)e^{-x}, & C_4&=4/\sqrt6.
\end{aligned}
```

Choose a finite regular collar atlas of the compact spatial joint and a
smaller collar whose closure lies inside it. Extend it by finitely many
patches covering the rest of the compact spatial region. Smooth spatial
partition weights sum to one on an **open neighborhood** of that region.
A compact smooth partition subordinate to a finite open cover supplies these
weights; disjoint patches are neither required nor used. Lifting a weight by
spatial projection gives a source column, **not** a new region with lateral
walls. Section 3 gives the stronger regular collar coordinates used here.

All charts, weights, slope/angle margins and radii are chosen before density.
Choose a positive displacement cutoff small enough that every spatial
translation under consideration remains in the C³ neighborhoods, every moving
zero stays in the smaller collar, and the implicit derivative in §3 is at
least one-half. Concrete sufficient choices in terms of that atlas are given
there. Use the sharp split

```math
\begin{aligned}
\mathcal C_{\lt\delta}&=\{z\in J^+(0):v\lt\delta\},\\
\mathcal C_{\ge\delta}&=\{z\in J^+(0):v\ge\delta\}.
\end{aligned}
\tag{S2}
```

The equality stratum belongs to the long domain. This is a disjoint exact
partition, including null vectors and the vertex. In particular the short
domain still contains nearly-null displacements; it is not a proper-time ball.
The second set is precisely `longFuture δ` used in #61.

Define the actual weighted overlap and the short observable by

```math
\begin{aligned}
V_a(z)&=\int_M a(x)\,\mathbf1_M((t,x)+z)\,dt\,dx,\\
V_a(0)&=\int_\Omega a h\,dx,\\
A^{\lt}_{\rho,\delta}[a]
 &=C_4\sqrt\rho\left[V_a(0)-\rho\int_{\mathcal C_{\lt\delta}}
 K(c\rho\sigma^2)V_a(z)\,dz\right].
\end{aligned}
\tag{S3}
```

In the first line the source point is the integration variable; the weight
does not restrict the partner. Compact domination at each fixed density
justifies absolute integrability, signed Fubini and the endpoint/displacement
substitution. The full first-endpoint observable of #65 is exactly (S3)
**minus** its long pair term, with prefactor $`C_4\rho^{3/2}`$. The point term
is allocated to the short part once, not once per endpoint or per pair.

**Short-displacement proposition.** For every admissible pair there is a
positive cutoff bound determined by the fixed geometric collar. For every
smaller fixed positive cutoff and each weight as above,

```math
\begin{aligned}
A^{\lt}_{\rho,\delta}[a]&\longrightarrow J_a+D_a,\\
J_a&=\int_S a\,\frac{1-|p|^2+p\cdot g}{k}\,dA_S
    =\int_J a\,\coth\theta\,dA_L.
\end{aligned}
\tag{S4}
```

The lifted weight is understood in the last integral. The error is bounded by
a constant times $`\rho^{-1/4}`$ plus explicitly described polynomial and
Gaussian tails in §5. The constant comes from the third derivative of a
**derived** local extension of the actual overlap, not an analytic hypothesis
inserted into admissibility. For weight one the cutoff derivative vanishes.
This does not assert that the omitted long term tends to zero.

## 3. Geometric input proved here: a C³ extension at the displacement origin

The exact causal graph-overlap identity, also valid with a spatial source
weight by the same vertical Fubini argument, gives

```math
\begin{aligned}
q_z(x)&=s-f(x+b)+f(x),\\
V_a(z)&=\int_\Omega a(x)[h(x)-q_z(x)]_+\,dx,\\
(1-\lambda)s&\le q_z(x)\le(1+\lambda)s
                  \qquad (s\ge |b|).
\end{aligned}
\tag{S5}
```

Here the future Lipschitz constant is less than one by the unchanged slope
budget. The envelopes, not globally smooth raw heights, justify (S5). Outside
the positive region the positive-part envelope is zero and the integrand is
zero. Inside it, the lower epigraph is a future set and the upper hypograph a
past set, so the vertical interval really has the indicated length. No other
face, null partner, exterior zero or chart label has been removed.

For causal displacements sufficiently near zero, split this identity exactly:

```math
\begin{aligned}
V_a(z)&=\int_\Omega a h-\int_\Omega a q_z
       +\int_{\{0\lt h\lt q_z\}}a(q_z-h).
\end{aligned}
\tag{S6}
```

This separates the interior volume, the lost single-face slice, and the thin
joint collar. The first two terms use fixed domains. In particular we do not
apply coarea through an interior critical point.

Here are details ensuring regularity of the last term, rather than asserting
that arbitrary translated overlaps are smooth. The implicit function theorem
and regular compact joint give finitely many C³ charts
$`x=\Phi_i(y,t)`$ with $`h(\Phi_i(y,t))=t`$, defined on fixed planar domains
and a two-sided height interval. Choose smooth subordinate weights whose
compact supports lie strictly inside these chart domains and sum to one on a
smaller two-sided collar. The volume Jacobians are C², are nonzero, and the
weighted Jacobians have fixed compact support in the planar variables.

In each chart solve

```math
\begin{aligned}
\eta_i&=q_z(\Phi_i(y,\eta_i)).
\end{aligned}
\tag{S7}
```

For completeness, let the charts be valid for heights of absolute value at
most twice a positive collar width. Let a positive spatial margin keep these
compact charts and the closed positive region inside the common C³
neighborhoods. Let $`H_f`$ bound the future Hessian there and let $`L_\Phi`$
bound the height derivative of the charts. It suffices to take a strictly
smaller positive cutoff than each of

```math
\begin{aligned}
&\text{spatial margin},\qquad
\frac{\text{collar width}}{4(1+\lambda)},\qquad
\frac{1}{4(1+H_fL_\Phi)}.
\end{aligned}
\tag{S8}
```

Shrinking the joint neighborhood first ensures every point of the closed
positive region below twice the collar width is covered; compactness and the
noncritical-band argument justify this step. The mean-value bound gives
$`|\partial_t q_z|\le H_f L_\Phi |b|\lt 1/2`$. The values at the height endpoints
have opposite signs in (S7). Hence its root is unique, stays in the smaller
collar, and is C³ in the displacement and the planar coordinates by the
implicit function theorem. These facts also hold for all sufficiently small
**noncausal** displacements. Use a smaller open Euclidean displacement ball
if needed; on the causal cone, its radius can be chosen to exceed the fixed
cutoff. No regularity is claimed at remote translated tangencies.

Define an extension of the collar term on that ball by the finite sum

```math
\begin{aligned}
&\sum_i\int dy\int_0^{\eta_i(y,z)}
 a(\Phi_i(y,t))\psi_i(\Phi_i(y,t))
 |\det D\Phi_i(y,t)|\,[q_z(\Phi_i(y,t))-t] \,dt.
\end{aligned}
\tag{S9}
```

Oriented integrals allow negative upper endpoints. For causal displacements
this is exactly the last term in (S6). The integrand vanishes at its moving
upper endpoint. Differentiating once therefore has no endpoint term;
differentiating twice gives endpoint terms involving the first derivatives of
the root and of the gap. Differentiating a third time requires at most one
height derivative of the weighted Jacobian and third derivatives of the gap.
All exist continuously. They are uniformly bounded on the fixed compact
chart domains and a smaller displacement ball. Dominated differentiation
therefore proves that (S9), and hence (S6), has a C³ extension, denoted here by
$`\widetilde V_a`$. It extends the **future-cone restriction**, not the actual
covariogram across past and spacelike displacements at zero. This derives the
analytic input from C³ geometry; it does not assume global C³ regularity of the
actual covariogram.

Expanding these fixed-domain expressions to second order gives

```math
\begin{aligned}
\widetilde V_a(s,b)
={}&V_a(0)+\int_\Omega a(-s+p\cdot b)
 +\frac12\int_\Omega a\,D^2f[b,b]\\
 &+\frac12\int_S\frac{a}{k}(s-p\cdot b)^2\,dA_S+R_a(s,b).
\end{aligned}
\tag{S10}
```

Indeed the root's linear term is the linear part of the gap. Integrating
that affine gap minus height from zero to its root gives half its square.
At height zero the chart Jacobian is the canonical spatial area density
divided by the actual gradient norm, by the existing coarea normalization.
Summing the partition gives the surface integral in (S10). This also explains
why no Hessian of the height enters the quadratic joint term.

Let $`T_a`$ bound the operator norm of the third derivative of the extension
on a closed displacement ball containing all short causal vectors. Taylor's
integral remainder, also applied to its first two derivatives, proves

```math
\begin{aligned}
|D^jR_a(z)|&\le T_a |z|^{3-j},\qquad 0\le j\le3.
\end{aligned}
\tag{S11}
```

The harmless sharper factorials have been dropped. The constant is finite by
the just-proved C³ extension and compactness. It can be bounded in terms of
the finite chart C³ bounds, inverse-derivative margin, future C³ bounds,
weight C² bounds and compact chart volumes. These are geometric quantities,
not a premise asserting that the normalized error vanishes.

## 4. Signed cancellation with all density powers

The exact null-coordinate Jacobian, with full sphere area, is

```math
\begin{aligned}
s&=\frac{v+\sigma/v}{2},\qquad
r=\frac{v-\sigma/v}{2},\\
j(v,\sigma)&=\frac{(v-\sigma/v)^2}{8v},\qquad
\sqrt\sigma\le v\lt\delta.
\end{aligned}
```

Thus the short pair integral is the half-line integral of the original kernel
against the short density obtained by integrating $`jV_a`$ over directions and
this interval. It is zero above $`\delta^2`$. Fubini is justified before using
sign cancellation by the bounded original short domain and bounded overlap.
Endpoint changes here affect only Lebesgue-null sets, not an omitted null layer.

### Quantitative remainder lemma, including the lower moving endpoint

Let $`B_R`$ be that density with the remainder (S11) in place of the overlap.
At fixed direction the displacement has norm at most the long coordinate,
and its proper-time derivative has norm at most its reciprocal. Direct
Leibniz differentiation gives

```math
\begin{aligned}
|\partial_\sigma^2(jR_a)|&\le 7T_a/8,\\
|\partial_\sigma^3(jR_a)|&\le 13T_a/(8v^2).
\end{aligned}
```

The integrand and its first proper-time derivative vanish at the lower endpoint
because the Jacobian has a double zero there. Its second derivative there has
absolute value at most $`T_a/4`$. Accordingly the boundary term in the **third**
derivative must be included. Integrating the bounds, including sphere mass,
gives

```math
\begin{aligned}
|B_R'''(\sigma)|&\le 7\pi T_a/\sqrt\sigma
                  \quad(0\lt\sigma\lt\delta^2).
\end{aligned}
\tag{S12}
```

The first two derivatives have right limits at zero: their fixed-coordinate
bounds are respectively constant multiples of the fourth, second and zeroth
powers of the long coordinate, all integrable at zero. The missing lower
intervals tend to zero. Dominated convergence proves these claims without
assuming them. Denote the resulting quadratic Taylor polynomial by $`P_R`$.
Integrating (S12) three times from the right yields

```math
\begin{aligned}
|B_R(\sigma)-P_R(\sigma)|&\le\frac{56\pi T_a}{15}\sigma^{5/2}.
\end{aligned}
\tag{S13}
```

This bound holds on the **whole positive half-line** after setting the actual
short density to zero above the cutoff. To check the extension, the three
Taylor coefficients in absolute value are at most

```math
\frac{\pi T_a\delta^5}{10},\qquad
\frac{\pi T_a\delta^3}{2},\qquad
\frac{7\pi T_a\delta}{4}.
```

For proper time above the cutoff square, their polynomial is bounded by
$`(47\pi T_a/20)\sigma^{5/2}`$, smaller than (S13).

The three exact signed moments of the original kernel annihilate this entire
quadratic polynomial on the half-line. Only **then** take absolute values and
substitute $`z=\sqrt{c\rho}\,\sigma`$. With the finite absolute moment below,

```math
\begin{aligned}
M_{5/2}&=\int_0^\infty z^{5/2}|K(z^2)|\,dz\lt\infty,\\
\left|C_4\rho^{3/2}\int_0^\infty B_R(\sigma)K(c\rho\sigma^2)\,d\sigma\right|
&\le C_4\frac{56\pi T_a}{15}c^{-7/4}M_{5/2}\rho^{-1/4}.
\end{aligned}
\tag{S14}
```

This is the required normalized stability estimate, not an unscaled geometric
Taylor error. It controls the nearly-null layer **inside** the short domain.

### Interior and single-face terms, not just the joint square

Angular integration of (S10) has the form

```math
4\pi V_a(0)+\ell_a s+\alpha_a s^2+\beta_a r^2+\int_{S^2}R_a\,d\omega,
```

where symmetry of the full sphere gives

```math
\begin{aligned}
\ell_a&=-4\pi\int_\Omega a,\\
\alpha_a&=2\pi\int_S a/k\,dA_S,\\
\beta_a&=\frac{2\pi}{3}\left[\int_\Omega a\Delta f
                         +\int_S a|p|^2/k\,dA_S\right].
\end{aligned}
\tag{S15}
```

The four elementary densities, in the same order, are as follows on the
interval from zero to the cutoff square; the usual continuous zero value is
used for a power times its logarithm:

```math
\begin{aligned}
F_0&=\frac{\delta^2}{16}-\frac\sigma4\log\delta
       -\frac{\sigma^2}{16\delta^2}+\frac\sigma8\log\sigma,\\
F_s&=\frac{\delta^3}{48}-\frac{\sigma\delta}{16}
       +\frac{\sigma^2}{16\delta}-\frac{\sigma^3}{48\delta^3},\\
F_{ss}&=\frac{\delta^4}{128}-\frac{\sigma^2}{16}\log\delta
       -\frac{\sigma^4}{128\delta^4}+\frac{\sigma^2}{32}\log\sigma,\\
F_{rr}&=\frac{\delta^4}{128}-\frac{\sigma\delta^2}{16}
       +\frac{3\sigma^2}{16}\log\delta+\frac{\sigma^3}{16\delta^2}
       -\frac{\sigma^4}{128\delta^4}-\frac{3\sigma^2}{32}\log\sigma.
\end{aligned}
\tag{S16}
```

They follow by integrating the Jacobian times the indicated monomial from the
moving lower endpoint. In particular the potentially dangerous fractional
power in the linear-face term **cancels at that endpoint**. Deleting the
linear-face term without this calculation would be invalid. The density is
$`4\pi V_a(0)F_0+\ell_a F_s+\alpha_a F_{ss}+\beta_a F_{rr}+B_R`$.

The signed moment identity and its differentiated versions are

```math
\begin{aligned}
m(j)&=\int_0^\infty z^jK(z^2)\,dz
 =-\frac{j(j-1)(j-2)}{12}\Gamma((j+1)/2),\qquad j>-1,\\
m(0)&=m(1)=m(2)=0,\\
\int_0^\infty z\log z\,K(z^2)\,dz&=1/12,\\
\int_0^\infty z^2\log z\,K(z^2)\,dz&=-\sqrt\pi/12.
\end{aligned}
\tag{S17}
```

For the logarithmic identities differentiate under the integral on a compact
exponent interval around one or two. At zero a slightly smaller power times
an absolute logarithm dominates; at infinity a polynomial times the Gaussian
dominates. The Gamma recurrence then gives the displayed constants. This
justifies the differentiation, rather than using a formal derivative alone.

The volume logarithm has coefficient $`\pi V_a(0)/2`$. Its normalized pair
contribution is exactly $`C_4\sqrt\rho V_a(0)`$ and cancels the point term.
The linear face term has no logarithm and contributes zero in the limit.
The quadratic logarithm has coefficient

```math
\begin{aligned}
L_a&=\frac{\alpha_a-3\beta_a}{32}\\
 &=\frac\pi{16}\left[\int_S\frac{a(1-|p|^2)}k\,dA_S
                       -\int_\Omega a\Delta f\right].
\end{aligned}
\tag{S18}
```

With the **minus sign of the action's pair term**, (S17) multiplies this
coefficient by $`16/\pi`$. This is the full unchanged BDG normalization.

## 5. Artificial terms, tangent wedges and uniformity

The spatial divergence theorem applies on the bounded C³ domain, including
all its components: the regular compact level boundary has a finite atlas,
the vector field is C¹ on its closure, and the outward normal is minus the
inward height normal. Hence

```math
\begin{aligned}
\int_\Omega a\Delta f
 &=-\int_S a\,p\cdot\nu\,dA_S-\int_\Omega\nabla a\cdot p.
\end{aligned}
\tag{S19}
```

Combining (S18) with (S19) proves (S4). This accounts for the surviving
single-face Hessian term: it becomes a genuine joint contribution and the
explicit artificial derivative term (S1), not an omitted curvature term.

To identify the independent geometric target, put
$`N=1-|p|^2+p\cdot g`$. For the two future unit normals the numerator of their
inner product is this positive number. Direct expansion gives

```math
N^2-(1-|p-g|^2)(1-|p|^2)
 =k^2\bigl(1-|p-(p\cdot\nu)\nu|^2\bigr)=k^2j_L^2.
```

Strict spacelike and joint margins make all divisions legitimate, and thus
$`\coth\theta\,j_L=N/k`$. The area density here is the independently proved
Lorentzian Gram density from #51, not Euclidean spacetime area or an area
defined using the action.

**Quantitative error bookkeeping.** Let the polynomial-log expression in
(S16), with its coefficients, be extended without its upper cutoff. Split it
into a polynomial of degree at most two, its two logarithmic terms, and
$`d_3\sigma^3+d_4\sigma^4`$, where

```math
d_3=-\ell_a/(48\delta^3)+\beta_a/(16\delta^2),\qquad
d_4=-(\alpha_a+\beta_a)/(128\delta^4).
```

Besides (S14), an explicit error bound is

```math
\begin{aligned}
E_{\rho,\delta,a}
={}&C_4|d_3|c^{-2}M_3\rho^{-1/2}
  +C_4|d_4|c^{-5/2}M_4\rho^{-1}\\
 &+C_4\rho^{3/2}\int_{\delta^2}^\infty
 |4\pi V_a(0)F_0+\ell_a F_s+\alpha_a F_{ss}+\beta_a F_{rr}|
 |K(c\rho\sigma^2)|\,d\sigma,
\end{aligned}
\tag{S20}
```

where the absolute moments have the same definition as in (S14). For fixed
positive cutoff the last line decays exponentially in density times a
polynomial: bound logarithms by powers away from zero and use Gaussian tails.
This displays all cutoff dependence; no uniform estimate as the cutoff tends
to zero is asserted. Together (S14) and (S20) bound the error in (S4).

**Actual comparison with regulated tangent wedges.** At each joint point use
#65's future-rest-frame wedge with slope $`k_\theta=\tanh\theta`$. Fix once
and for all a compact normal cutoff with trace one and Lipschitz constant,
and a continuous compact tangential weight of integral one in an orthonormal
joint plane. Choose a common source cube radius and regulator height satisfying
$`H\ge2R\sup_J k_\theta`$. Let $`W_\rho(k_\theta)`$ be its genuine
first-endpoint observable (W2), not a fitted coefficient. Define the comparison
superposition by integrating these unit-area observables against the original
weighted induced joint area:

```math
T_\rho[a]=\int_J a\,W_\rho(\tanh\theta)\,dA_L.
```

This is a field of regulated tangent-wedge observables, **not** the action of
a union of isolated wedge cells. Write
$`M^G_1=\int_0^\infty u|G(u)|\,du`$ for #65's **reduced-kernel** moment,
distinct from the original-kernel moments in (S14). Its bound (W7) gives

```math
\begin{aligned}
|T_\rho[a]-J_a|&\le
 \frac{L_B M^G_1}{k_{\min}^2}\rho^{-1/4}\int_J |a|\,dA_L,\\
&0\lt k_{\min}\le\tanh\theta\le k_{\max}\lt 1.
\end{aligned}
\tag{S21}
```

Its invariant meaning and finiteness follow from #51; a measurable choice of
frames is unnecessary since the scalar observable depends only on the slope.
Adding (S14), (S20) and (S21) proves the normalized comparison

```math
\begin{aligned}
A^{\lt}_{\rho,\delta}[a]-D_a-T_\rho[a]&\longrightarrow0.
\end{aligned}
\tag{S22}
```

All regulator parameters and geometry stay fixed. The bound is uniform on
compact joint portions and for finite partitions with common chart bounds,
weight bounds, third-derivative bounds, and fixed positive slope/angle margins.
For families of geometries those common bounds must be specified; mere
admissibility does not give a universal constant. Neither tangential nor null
limits are covered.

**Overlaps and derivatives.** For the constructed finite spatial partition,
linearity gives the exact action and overlap sums, retaining every partner.
Since the sum of weights is one on an open neighborhood, its gradient is zero
on the positive region, so the sum of (S1) is exactly zero. If both endpoints
are partitioned instead, there is a double sum over **all** ordered chart
labels. Off-diagonal labels are not discarded. The sharp displacement boundary
in (S2) introduces no differentiation in spacetime; its moving proper-time
endpoint was retained explicitly in (S12) and (S16). Smooth displacement
cutoffs are not silently substituted for this specified regulator.

## 6. Relation to #61 and G4; scope and regressions

For weight one, subtract from (S3) the normalized integral over
`longFuture δ`. That integral is **exactly** the actual
`longOverlapDensity (twoFaceRegion h f) δ` representation already checked in
#60. The domains have neither a gap nor a double-counted cutoff surface. The
short proposition proves no right-hand expansion for that density, especially
near remote translated tangencies. #61 remains independent and necessary for
this route to the full action. For nonconstant weights even its unweighted
conclusion would not supply a weighted long-pair theorem.

If #61 succeeds at the same fixed small cutoff, the unweighted short result
supplies the other analytic piece. G4 must still assemble and audit the full
statement, its independent target and the expectation transfer, reconciling
cutoff quantifiers. This argument does not require sending the cutoff to zero
to obtain the short coefficient; it does **not** authorize exchanging density
and cutoff limits. Any different chart regulator or globalization route must
retain its own artificial terms.

Regressions in `test_short_displacement.py` check the four densities against
independent integration, the original signed/logarithmic moments, all density
powers, actual curved axial overlaps and short/long accounting, the derived
quadratic coefficient against independent normal/Gram geometry, a nonzero
cutoff-derivative example, planar unequal axes, a boost, and the curved radial
matched-joint family. A separate cosine-future regression makes the integrated
single-face Laplacian nonzero and detects its erroneous omission; it uses the
exact axial overlap, not the full-density solver's monotone-shift assumption. Existing #54 tests continue to exercise finite-density
full actions and independent unreduced integrals. Orders, precision and errors
are recorded in `results/short-displacement.json` by
`reproduce_short_displacement.py`.

Refinement differences are not certified quadrature errors. Floating-point
subtraction of full and long densities and of the bulk/pair terms becomes
ill-conditioned at high density; the tests do not establish a limit, a rate,
uniformity, or #61. The conventional proof, the explicitly limited Lean
identities, and the numerical evidence remain distinct.

Reproduction:

```sh
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce_short_displacement.py
(cd formal && ./check.sh)
```
