# Direct-origin short stability for SmoothPilot3 (#79)

**Delivery: a conventional short-limit proof and executable regressions, not a
new Lean theorem.** Use exactly [#92's `SmoothPilot3`](dimension-two-face-geometry.md),
its action (G16) and its independently defined intrinsic target (G13). The
canonical Lean geometry port belongs to #115 and is still outstanding at this
delivery. No region, admissibility, target or expectation definition is replaced.
Independent human mathematical review is outstanding.

The result below concerns the **actual short observable** at any sufficiently
small fixed positive coordinate cutoff. It does not prove #78's long estimate,
#80's global deterministic/expected limit, or the general conjecture under #24.
The separately checked dimension-indexed Poisson bridge is not used to define an
expectation or infer an expected limit here. There is no density-dependent
geometry, shrinking-cutoff assertion, or individual-sprinkling claim.

## 1. Route choice and the common short/long interface

| Route | Available evidence | Decision for this delivery |
| --- | --- | --- |
| Same-height unweighted planar comparison | #89 has a checked 4D producer and global planar base theorem | Not selected: the corresponding global 3D planar theorem is not available in Lean and would be an additional obligation |
| Weighted tangent-wedge replacement | #88 checks the fixed-regulator coefficient; #66's weighted curved argument is conventional and 4D | Not selected: a wedge coefficient does not bound the actual curved error or remove artificial source terms |
| Direct-origin absolute overlap | #97's integrated 4D proof retains point volume, linear slice, future Hessian and divergence | Selected, with **new 3D** radial measure, moving endpoints, signed moments and remainder calculation below; no 4D analytic theorem is instantiated as if dimension-free |

The planar reference would be geometrically admissible under the pilot's strict
combined budget. The reason not to use it is the unnecessary additional global
analytic theorem, not the independent-envelope obstruction from #85. We do not
enlarge this pilot to class E. The following argument is self-contained at the
conventional level and does not borrow #66's uncompiled weighted estimates as
Lean inputs.

Write the spatial variables in the Euclidean plane, with ordinary area dx and
ordinary arc length on the **entire** regular compact boundary S:

```math
\begin{aligned}
H&=\max(0,h),&\Omega&=\{h>0\},&K&=\overline\Omega,&S&=K\cap\{h=0\},\\
M&=\{(t,x):f(x)-h(x)\lt t\lt f(x)\},&p&=\nabla f,&g&=\nabla h,&k&=|g|\quad\text{on }S.
\end{aligned}
\tag{T1}
```

Let w be a real smooth function on a neighborhood of K, attached only to the
spatial coordinate of the first endpoint. The constant one is included. A smooth
cutoff equal to one near K gives a compactly supported representative when
needed; no source values or derivatives change. Signed and overlapping weights
are allowed. Define the actual weighted covariogram and point volume:

```math
\begin{aligned}
V_w(z)&=\int_M w(x)\,\mathbf1_M((t,x)+z)\,dt\,dx,&V_w(0)&=\int_\Omega wh\,dx,\\
z&=(\tau,b),&r&=|b|,&v&=\tau+r,&\sigma&=\tau^2-r^2,\\
\mathcal C_{\lt\delta}&=\{\tau\ge r,\ v\lt\delta\},&
\mathcal C_{\ge\delta}&=\{\tau\ge r,\ v\ge\delta\}.
\end{aligned}
\tag{T2}
```

The equality stratum belongs to long. The vertex and null displacements remain
in the exact partition; changes on integration endpoints are justified by
Lebesgue nullity. All partner components and all chart-crossing pairs remain.
At each fixed density compact domination gives absolute integrability before
translation, signed Fubini or partition summation.

Use the unchanged constants from [the dimensional kernel note](dimension-kernels.md):

```math
\begin{aligned}
c&=c_3=\pi/12,&a_3&=\beta_3=\frac{2c^{2/3}}{\Gamma(5/3)},\\
K_3(z)&=(1-27z/8+9z^2/8)e^{-z},\\
A^{\lt}_{\rho,\delta}[w]
 &=\rho^{2/3}\left[a_3V_w(0)-\beta_3\rho
       \int_{\mathcal C_{\lt\delta}}K_3(c\rho\sigma^{3/2})V_w(z)\,dz\right].
\end{aligned}
\tag{T3}
```

The point term is allocated to short **once**. The full first-endpoint action
is (T3) minus the signed long pair contribution with prefactor
$`\beta_3\rho^{5/3}`$. In particular w=1 gives exactly #92's full action after
both domains are assembled, not a modified regulator-dependent action.

**Written theorem.** For every `SmoothPilot3(h,f)` there is a positive cutoff
bound such that for every smaller fixed positive cutoff, and every w above,

```math
\begin{aligned}
A^{\lt}_{\rho,\delta}[w]&\longrightarrow J_w+D_w,\\
J_w&=\int_S w\,\frac{1-|p|^2+p\cdot g}{k}\,d\ell_S
     =\int_J w\coth\theta\,dA_J,&
D_w&=\int_\Omega\nabla w\cdot p\,dx.
\end{aligned}
\tag{T4}
```

The geometric cutoff bound can be chosen before w: w changes derivative bounds,
not the overlap's moving roots. For w=1 the limit is the independent target
$`\mathcal J_3(h,f)`$, with no cutoff in its coefficient. Empty geometry has
zero terms throughout. All arguments below concern a nonempty fixed region.

## 2. Actual overlap, not a postulated jet

The global envelopes L=f-H and U=f have strict Lipschitz constants less than
one by the pilot's combined budget. At a future-causal displacement they order
the two lower and upper endpoints in the intersection of vertical fibres.
Consequently vertical Fubini, including the empty fibre case, gives

```math
\begin{aligned}
q_z(x)&=\tau-f(x+b)+f(x),\\
V_w(z)&=\int_\Omega w(x)[h(x)-q_z(x)]_+\,dx,\\
(1-\eta)\tau&\le q_z(x)\le(1+\eta)\tau\qquad(\tau\ge|b|),\\
V_w(z)&=V_w(0)-\int_\Omega wq_z\,dx
              +\int_{\{0\lt h\lt q_z\}}w(q_z-h)\,dx.
\end{aligned}
\tag{T5}
```

Here eta is the global future Lipschitz constant. To check that the positive
part has not acquired exterior partners: the envelope gap is
U(x+b)-L(x)-tau. Positivity forces H(x)>0 by the upper-envelope bound and
H(x+b)>0 by the lower-envelope bound. Outside the positive region the gap is
nonpositive. On the positive region the displayed raw gap agrees exactly.
Thus no raw exterior zero or disconnected component was substituted away.
Only f is translated; its derivatives are used only in a fixed neighborhood
of K containing every sufficiently small translated segment.

### A smooth future-cone extension from a finite height collar

Compactness, smooth germs and nonzero dh on S provide finitely many regular
height charts $`x=\Phi_i(y,t)`$, with **one-dimensional** y, and
$`h(\Phi_i(y,t))=t`$. Choose precompact chart supports, a two-sided height
interval, and smooth subordinate weights summing to one on a smaller collar.
Their weighted volume Jacobians have common compact y supports. Compactness
keeps every sufficiently small positive height in this collar: otherwise a
sequence outside it with heights tending to zero would have a limit in S.
Interior positive-height critical points are not removed or used as charts.

Choose a displacement ball so all translations stay in the smooth domains,
all roots stay in the smaller collar, and the height derivative of q has
absolute value less than one-half. This is possible since it is bounded by
$`|b|`$ times fixed bounds for the future Hessian and chart height derivative.
The implicit function theorem and the endpoint signs then give a unique smooth
root $`t_i=q_z(\Phi_i(y,t_i))`$, including for small noncausal parameters.
On the future cone q is nonnegative and the root is nonnegative. The collar
correction in (T5) equals the finite sum

```math
\begin{aligned}
\sum_i\int dy\int_0^{t_i(y,z)}
 W_i(y,t)[q_z(\Phi_i(y,t))-t]\,dt,\qquad
W_i=(w\psi_i)\circ\Phi_i\,|\det D\Phi_i|.
\end{aligned}
\tag{T6}
```

Oriented upper endpoints define an extension off the future cone, not the
actual covariogram for all spacelike displacements. The first parameter
derivative has no upper-endpoint term because the gap vanishes at its root.
The next two derivatives use at most one height derivative of the weighted
Jacobian and third derivatives of q. Smoothness, the inverse-derivative margin
and the fixed compact domains bound these derivatives uniformly. Dominated
differentiation proves a C³ extension of (T5) on a ball. This derives the
regularity; it is not an admissibility or coarea premise encoding the result.

The fixed-domain bulk expansion and the root's linear term now give

```math
\begin{aligned}
\widetilde V_w(\tau,b)={}&V_w(0)-\tau\int_\Omega w
 +\int_\Omega wp\cdot b+\frac12\int_\Omega wD^2f[b,b]\\
 &+\frac12\int_S\frac{w}{k}(\tau-p\cdot b)^2\,d\ell_S+R_w(\tau,b),\\
|D^jR_w(z)|&\le T_w|z|^{3-j},\qquad j=0,1,2.
\end{aligned}
\tag{T7}
```

Integrating the linear gap minus height to its root produces half its square.
The chart Jacobian at height zero is ordinary arc length divided by k; the
complete partition sum therefore gives the canonical surface integral shown.
Taylor's integral theorem applied also to the first two derivatives supplies
(T7), with finite T from the constructed C³ extension on a smaller closed
ball. Derivative control is essential below; a value-only cubic estimate
would not justify differentiating the null density. The extension and its
remainder are continuous, hence measurable. Neither coarea nor a noncritical
hypothesis is imposed on the fixed interior bulk integrals.

## 3. Angular integration and the **3D** sharp fibres

Use the full circle, with mass $`2\pi`$, zero first moments and second moments
$`\int\omega_i\omega_j\,d\theta=\pi\delta_{ij}`$. The cross time/spatial term
vanishes only after this complete angular integral. Thus

```math
\begin{aligned}
\int_{S^1}\widetilde V_w(\tau,r\omega)\,d\theta
 &=2\pi V_w(0)+\ell_w\tau+\alpha_w\tau^2+\beta_w r^2
       +\int_{S^1}R_w(\tau,r\omega)\,d\theta,\\
\ell_w&=-2\pi\int_\Omega w,&\alpha_w&=\pi\int_S w/k\,d\ell_S,\\
\beta_w&=\frac\pi2\left[\int_\Omega w\Delta f
                       +\int_S w|p|^2/k\,d\ell_S\right].
\end{aligned}
\tag{T8}
```

In particular beta here is a jet coefficient, not the action constant beta_3.
The future Hessian is still present. Spatial polar measure is r dr dtheta,
not the 4D squared-radius measure. The exact change of variables is

```math
\begin{aligned}
\tau&=(v+\sigma/v)/2,&r&=(v-\sigma/v)/2,\\
j_3(v,\sigma)&=\frac{r}{2v}=\frac14(1-\sigma/v^2),&
\sqrt\sigma&\le v\lt\delta,\\
B_w(\sigma)&=\int_{S^1}\int_{\sqrt\sigma}^{\delta}
 j_3(v,\sigma)V_w(\tau,r\omega)\,dv\,d\theta\quad(0\lt\sigma\lt\delta^2).
\end{aligned}
\tag{T9}
```

Set the density to zero above the cutoff square. It is measurable and bounded
for this fixed cutoff and has compact support: the bounded overlap and
$`0\le j_3\le1/4`$ suffice. The signed short pair integral equals the integral
of this density against the kernel, by the already justified finite-density
Fubini/change of variables. Values at isolated endpoints do not change it.

Integrating j times the four modes **from the moving lower endpoint** gives,
without angular mass, on the support interval:

```math
\begin{aligned}
F_0&=\delta/4+\sigma/(4\delta)-\sigma^{1/2}/2,\\
F_\tau&=\delta^2/16-\sigma/8+\sigma^2/(16\delta^2),\\
F_{\tau\tau}&=\delta^3/48+\sigma\delta/16+\sigma^2/(16\delta)
 +\sigma^3/(48\delta^3)-\sigma^{3/2}/6,\\
F_{rr}&=\delta^3/48-3\sigma\delta/16-3\sigma^2/(16\delta)
 +\sigma^3/(48\delta^3)+\sigma^{3/2}/3,\\
B_w&=2\pi V_w(0)F_0+\ell_wF_\tau+\alpha_wF_{\tau\tau}+\beta_wF_{rr}+B_R.
\end{aligned}
\tag{T10}
```

All four fibres vanish at the cutoff square. At zero they have their displayed
continuous limits. The linear fibre has no fractional contribution. The
constant half power and quadratic three-halves powers **do not cancel at the
lower endpoint**: discarding them would destroy both the point cancellation
and the joint coefficient. The identity between the time-square fibre and
the radial-square fibre plus sigma times the constant fibre checks the signs.

## 4. Signed responses, with full normalization

Directly integrate each term of the signed polynomial times its exponential.
For every real j greater than minus one this gives the absolutely convergent
Mellin moment

```math
\begin{aligned}
m(j)&=\int_0^\infty u^j K_3(u^{3/2})\,du
 =\frac23\Gamma\left(\frac{2(j+1)}3\right)
        (1-(j+1))(1-(j+1)/2),\\
m(0)&=m(1)=0,\qquad m(1/2)=-1/12,\qquad m(3/2)=\Gamma(5/3)/4,\\
\rho^{5/3}\int_0^\infty\sigma^j K_3(c\rho\sigma^{3/2})\,d\sigma
 &=c^{-2(j+1)/3}\rho^{(3-2j)/3}m(j).
\end{aligned}
\tag{T11}
```

This is a direct 3D use of the kernel, not the reduced-plane first height
moment. That odd-dimensional height moment is **positive**, as #88 proves;
we do not set it to zero. Nor is any even second height moment assumed finite.

For the calculation temporarily extend each expression in (T10) to the whole
positive half-line. The difference from its actual sharp-cutoff fibre is
supported above the fixed cutoff square. After multiplication by the kernel,
its integral with full normalization tends to zero exponentially: split the
exponential into two equal factors, bound one by its value at the cutoff,
and integrate the other against each polynomial or fractional power. For
density at least one the remaining integrals are bounded by fixed integrable
exponential envelopes times a polynomial in density. This also justifies all
signed splits before taking a limit.

The constant mode's pair integral is $`V_w(0)/\rho`$ after its cancelled
integer moments; multiplication by beta_3 cancels the entire point term since
a_3=beta_3. The linear mode's remaining degree-two polynomial contributes a
vanishing term. The degree-two and degree-three polynomial parts of both
quadratic modes also vanish, by (T11); they must not be declared zero at finite
density. Finally, with the **minus sign** in the action, the critical
three-halves response is

```math
\begin{aligned}
-\beta_3c^{-5/3}m(3/2)&=-6/\pi,\\
-\frac6\pi\left(-\frac{\alpha_w}{6}+\frac{\beta_w}{3}\right)
 &=\frac{\alpha_w-2\beta_w}{\pi}.
\end{aligned}
\tag{T12}
```

Thus the quadratic responses are positive one over pi and negative two over
pi, respectively, not the 4D coefficients. All cutoff-dependent polynomial
terms either cancel or tend to zero. No long estimate or global planar base
limit has entered this computation.

## 5. Derivative-controlled remainder, including nearly-null displacements

Here the 3D Jacobian has only a **single** zero at the moving lower endpoint.
The boundary term therefore occurs in the second derivative, earlier than in
4D. Fix a direction, put $`F=j_3R_w(\tau,r\omega)`$, and use (T7). On the
integration fibre the displacement norm is at most v and its sigma derivative
has norm at most 1/v. Direct differentiation gives

```math
\begin{aligned}
|F|&\le Tv^3/4,&|\partial_\sigma F|&\le Tv/2,&
|\partial_\sigma^2F|&\le3T/(4v),\\
F(\sqrt\sigma,\sigma)&=0,&
\partial_\sigma F(\sqrt\sigma,\sigma)&=-R_w(\sqrt\sigma,0)/(4\sigma),\\
|B_R''(\sigma)|&\le\frac{3\pi T}{2}\log\frac{\delta}{\sqrt\sigma}
                          +\frac{\pi T}{4}.
\end{aligned}
\tag{T13}
```

The last constant includes the Leibniz lower-endpoint term. For example
R=tau cubed gives a nonzero positive one-eighth term before angular integration;
it cannot be omitted. All differentiations here are away from sigma zero, on
compact positive-v intervals. The first two displayed dominators are integrable
down to v=0, so dominated convergence supplies the right limits of B and its
first derivative. In particular, if their affine polynomial is P, then

```math
\begin{aligned}
|P(0)|&\le\pi T\delta^4/8,&|P'|&\le\pi T\delta^2/2,\\
|B_R(\sigma)-P(\sigma)|
 &\le\pi T\sigma^2\left(\frac34\log\frac\delta{\sqrt\sigma}
                              +\frac{11}{16}\right)
               \quad(0\lt\sigma\lt\delta^2),\\
|B_R(\sigma)-P(\sigma)|&\le2\pi T\sqrt\delta\,\sigma^{7/4}
               \quad(\sigma>0).
\end{aligned}
\tag{T14}
```

Integrating (T13) twice gives the middle line, including its constant. For its
global consequence set t=sqrt(sigma)/delta below the cutoff and use
$`\sqrt t\log(1/t)\le2/e`$. Above the cutoff the actual density is zero and
the two coefficient bounds dominate the affine polynomial by at most
$`(5\pi T\sqrt\delta/8)\sigma^{7/4}`$. Thus the last line holds on the
whole half-line, not just pointwise near zero.

The two vanishing signed moments kill P before taking absolute values. The
remaining absolute moment is finite, giving the explicit sufficient estimate

```math
\begin{aligned}
\left|\beta_3\rho^{5/3}\int_0^\infty B_R(\sigma)
                    K_3(c\rho\sigma^{3/2})\,d\sigma\right|
 &\le2\pi\beta_3T\sqrt\delta\,c^{-11/6}\rho^{-1/6}
      \int_0^\infty u^{7/4}|K_3(u^{3/2})|\,du
 \longrightarrow0.
\end{aligned}
\tag{T15}
```

This is a proved, deliberately loose **remainder** estimate for fixed geometry
and cutoff, not a uniform cutoff-removal or full-action rate assertion. The
sharper local logarithmic bound in (T14) is retained rather than asserting a
false pure quadratic remainder. For example R equal to the spatial norm cubed
satisfies the C² derivative bounds and produces a nonzero sigma-squared log
term. Its order is nevertheless strictly sufficient for little-o of sigma to
power three-halves. The nearly-null part of the short domain is included.

## 6. Divergence, artificial partitions and the independent target

Combining (T8), (T12) and (T15) leaves

```math
\begin{aligned}
\frac{\alpha_w-2\beta_w}{\pi}
 &=\int_S\frac{w(1-|p|^2)}k\,d\ell_S-\int_\Omega w\Delta f,\\
\int_\Omega w\Delta f
 &=-\int_S w\,p\cdot g/k\,d\ell_S-\int_\Omega\nabla w\cdot p.
\end{aligned}
\tag{T16}
```

The divergence theorem applies to this bounded smooth domain, with all
components and inner boundary components included; its outward normal is
**minus** g/k. Smooth compact boundary charts and compactness supply a finite
cover and finite area. This theorem is not being applied to a selected
component or to an artificial chart region with its own walls. In particular
the future Hessian becomes both the true joint flux and the derivative term,
not zero by assumption.

Independently, #92 constructs induced positive joint metric, arc length and
future unit normals. Its Gram density is the positive square root of
$`1-|p_T|^2`$, not the Euclidean spacetime graph factor. The positive-normal
angle satisfies the independently derived identity
$`\coth\theta\sqrt{1-|p_T|^2}=(1-|p|^2+p\cdot g)/k`$.
Consequently (T16) identifies the result with exactly (T4). No area measure or
angle is defined from this action coefficient.

For a finite smooth spatial source partition summing to one on a neighborhood
of K, the weighted point terms and actual overlaps sum exactly at every
density. The gradients sum to zero, so all derivative terms in (T4) cancel
**only after the complete sum**. Smoothness and compactness give a common
finite remainder bound. Partners were never weighted or restricted by chart
membership. A weight with zero joint trace can still have nonzero derivative
response; a weighted wedge coefficient alone cannot prove its short limit.
The unweighted argument needs no such source partition, but this calculation
makes the artificial terms explicit rather than suppressing them.

## 7. Regressions and transfer/obstruction ledger

`dimension_short.py` evaluates the 3D sharp basis stably and a clearly labeled
quadratic **model** action using incomplete gamma integrals without dropping
its tail. A separate actual-overlap diagnostic uses
h=a(1-|x| squared) and f=epsilon cos(x_1), with the pilot budget
2a+epsilon less than one. This future is globally Lipschitz, genuinely curved,
and has a nonzero integrated Hessian, avoiding a misleading odd-sine
cancellation. The center's positive-height critical point stays in the region.
Integrating the second spatial coordinate of the exact gap yields

```math
\begin{aligned}
V_w(\tau,b)=\frac4{3\sqrt a}\int_{-1}^1 w(x)
 [a(1-x^2)-\tau+\epsilon(\cos(x+b_1)-\cos x)]_+^{3/2}\,dx.
\end{aligned}
\tag{T17}
```

The independent target test evaluates actual normals and Lorentzian Gram
length using `dimension_joint_geometry.py`, not a value defined by the jet.
Signed overlapping source partitions have nonzero individual derivative terms
and exactly cancelling sums. Null and timelike actual-overlap checks retain
all partners.

For the planar unit disk, f=0 and the exact causal overlap below height a is
pi a/2 times (1-tau/a) squared, so its short action for any cutoff below a is
**exactly** the quadratic model. Two different fixed cutoffs converge in the
diagnostics to the same independent target pi/a. This is a planar short
regression, not a global planar base theorem. For planar axes (b_1,b_2), volume,
overlap and target gain b_1 b_2, reproducing #92's 8 pi at a=1/4 and axes (1,2).

| Dimension | What transfers or is checked | Remaining obligation / forbidden shortcut |
| --- | --- | --- |
| 2 | Existing #92 geometry uses counting measure on every joint point | No 2D short theorem here; the radial measure and constant/log sectors need a separate calculation |
| 3 | Written actual overlap producer, all four responses, derivative remainder and intrinsic identification above | Compile #115's exact geometry and then the analytic producers/consumer; independent human review; #78 long estimate and #80 assembly remain separate |
| 4 | Regressions recover the existing squared-radius Jacobian and all four old fibres; old C³ and independent-envelope Lean results are untouched | Do not import its logarithmic response, three vanishing transverse moments or zero first height moment into 3D |
| 5 | Trial direct-origin scaling has a degree-two cancelled density jet and a critical five-halves response | Recalculate all bases and angular normalization. Third differentiated cubic-remainder integrands have a borderline inverse-v bound, suggesting a sigma-cubed logarithmic residual, but its actual producer/endpoints/domination are **not proved here**. Smooth germs, or the separately proposed C⁵ trial class, are not a substitute for that proof |
| 6 | Trial scaling has a degree-three cancelled jet and a critical cubic-log response | A fourth proper-time derivative needs additional primitive derivative control, not the present C² bounds. A candidate inverse-v-squared bound would give order seven-halves after four integrations; establish it with endpoints and a sufficient geometric regularity class before claiming transfer |

For these last two power counts the general radial factor is
$`(v-\sigma/v)^{d-2}/(2^{d-1}v)`$. Applying k sigma derivatives to a cubic
primitive remainder suggests power $`v^{d-2k}`$; this is an estimate to derive
with actual derivative bounds, not a universal overlap theorem. In even
dimensions the divergent second **height** moment prevents the naive
reduced-plane Taylor route. In odd dimensions the first height moment is
positive. The appropriate fractional/log terms must survive until their
complete signed normalized contribution is evaluated. No all-dimension result
or counterexample to the full conjecture follows from this ledger.

## 8. Exact consumer contract and verification boundary

These are **written interfaces, not compiled declaration names**:

```text
Inputs owned by #115:
  SmoothPilot3(h,f), actual M and volume, finite canonical joint line measure,
  actual causal overlap identity, regular-height atlas/integration with compact
  domination, spatial divergence, independent normal/Gram target identity.
Producer owned by #79:
  a geometry-selected delta0 > 0;
  for every 0 < delta <= delta0, actual short density (T9), exact decomposition
  (T10), and a measurable C2 primitive remainder with bounds (T7).
Consumer proved here conventionally:
  actual A_short(rho,delta;w) -> J_w + D_w; in particular w=1 -> J_3(h,f).
Parallel consumer #78:
  same M, kernel, circle measure, sigma, v and fixed delta;
  actual long pair term over v >= delta, including all partners.
Assembly reserved to #80:
  combine both actual estimates at one common fixed delta, then specialize the
  separately checked finite-density expectation bridge. Two conditional
  consumers are not a proved global pilot limit.
```

- **Written proof:** (T4), using the derived geometry, exact radial responses,
  derivative remainder and independent target identification above.
- **Executable checks:** `test_dimension_short.py` independently integrates
  fibres and signed moments, checks moving endpoints and the nonzero logarithmic
  remainder, full physical normalization, actual planar and curved overlaps,
  normal/Gram targets, signed source partitions and unchanged 4D fibres.
  `check_symbolic.py` includes the new exact basis/normalization checks. Numerical
  comparisons and their tolerances are diagnostics, not certified error bounds
  or proofs of arbitrary-region admissibility or limits.
- **Lean:** no new Lean artifacts, dependencies, checker logic or build inputs
  are changed. No new local Lean audit or compiled 3D short theorem is claimed.
  Future formalization requires the full integrated `formal/check.sh` after the
  final Lean-affecting change, not just a changed-source check or GitHub CI.
- **Independent human mathematical review:** outstanding and separate from
  written arguments, regression tests and the pre-existing checked results.

Local validation passed: all 192 Python tests (including nine new focused
regressions), all symbolic checks, Markdown lint and its 20 tests. This is not
an independent mathematical review or a Lean-check receipt.

```sh
.venv/bin/python -m unittest -v test_dimension_short
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
