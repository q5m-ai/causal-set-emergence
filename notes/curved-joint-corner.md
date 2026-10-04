# Curved joint corner: weighted tangent comparison (#75)

**Conventional written theorem, with separate symbolic and numerical checks;
not a new Lean theorem or independent human mathematical review.** For the
fixed polynomial-density pilot and the original `AdmissibleTwoFace` class,
this note proves `CurvedJointCornerLimit` for the **actual** functional (H16)
of [the boundary-collar handoff](curved-boundary-collar.md). Its compensating
single-face joint flux is essential. The answer is the independently induced
curved area times the positive-normal angle weight; no additional corner
correction survives. This is the joint producer for #76, not a new probability
bridge, general curved theorem, or closure of #24.

## 1. Frozen input and theorem

The integration base is `c6c2477aa5cf1e22cc66759142ca52319af870d3`. In particular
#74's final [PR #123](https://github.com/q5m-ai/causal-set-emergence/pull/123)
is merged at `6b7cac5f2866588eb137ba7bc8136ff62ad7758a`; its (H16), not the
earlier obstructed raw-fibre bound, is the input. The canonical action remains
`BoundaryDraft.conformalAction` in `formal/BoundaryDraft/ConformalAction.lean`.
That file, `ConformalGeometry.lean` and `FiniteMeasureBDG.lean` are unchanged
from #93's merged API (`efe7f8340920f363cb84d69fdc592d553900d5c0`). Its recorded
full source/transitive-axiom audit was on
`9aed02c70f01c9fd4c5d14e5e4b1024d94f8367f`; this source comparison is not a new
audit. No Lean validation input changes in this package.

Keep the original C³ face germs, strict combined slope budget, compact closed
positive region, and regular joint. Do not require C⁴ faces, global smoothness
of clipped envelopes, a connected joint, or absence of positive-height
critical points. Put

```math
\begin{aligned}
\mathcal O&=\{z:h(z)>0\},&\Sigma&=\partial\mathcal O,&\ell&=f-h,\\
M&=\{(t,z):z\in\mathcal O,\ \ell(z)\lt t\lt f(z)\},&
q(t)&=1+t^2,&g&=q^{1/2}\eta,\\
\eta&=\mathrm{diag}(1,-1,-1,-1),&d\mu_g&=q(t)\,dt\,dz,\\
c&=\pi/24,&C&=4/\sqrt6,&K(Z)&=(1-9Z+8Z^2-\tfrac43Z^3)e^{-Z}.
\end{aligned}\tag{J1}
```

Use fixed real C⁵ endpoint fields chi and phi near the closure of M, as in
#74. They may be signed and need not vanish on either face. Use one common
sufficiently small **fixed** positive delta, satisfying (H1)'s field, phase
and collar margins and the derived chart margins in §3 below. Every smaller
fixed positive cutoff also works. Nothing varies with density except rho.

The actual short/long split is still `v = delta_t + spatial_distance`, with
`v < delta` short and equality long; its one point term stays in short. Both
endpoint measures, the closed order, exclusive interval endpoints, and all
causal partners are unchanged. The ambient polynomial interval law is

```math
\begin{aligned}
T&=(u+v)/2,&r&=(v-u)/2,\\
V(x,x+(T,rn))&=c(uv)^2\mathcal H(t,u,v),\\
\mathcal H(t,u,v)&=1+t^2+\tfrac12t(u+v)+\tfrac3{40}(u+v)^2-\tfrac1{30}uv.
\end{aligned}\tag{J2}
```

For actual pairs it equals the canonical restricted interval by causal
convexity and atomlessness. For auxiliary pairs outside M it is only the
ambient law: they cancel exactly in (H3), not by an asserted restricted-volume
identity. We retain them in the following theorem.

```text
PROVED IN WRITING CurvedJointCornerLimit(h,f,delta,chi,phi):
  original AdmissibleTwoFace; q(t)=1+t^2; fixed real C5 endpoint fields
  one common sufficiently small fixed positive delta as above
  J is the actual overshoot integral (H2)-(H4), not a hinge approximation
  T is the single-face joint flux (H15)
  Q_chi,phi(rho) = -C*rho^(3/2)*J_chi,phi(rho) - T_chi,phi
  Q_chi,phi(rho) -> integral_joint chi*phi*coth(theta) dA_g
  the signed comparison error tends to zero for every fixed finite family
  of endpoint weights, with all cross-chart partners retained
```

This is not Lean code. The right side is defined geometrically next, before
any evaluation of J. Empty positive regions give zero on both sides.

## 2. Independent induced geometry and fixed margins

At z in Sigma write p=Df, a=Dh, k=|a| and n_h=a/k. The outward spatial normal
is minus n_h. The two **future** unit normals (past inward, future outward)
and their metric product are

```math
\begin{aligned}
N_f&=q(f)^{-1/4}\frac{(1,p)}{\sqrt{1-|p|^2}},&
N_\ell&=q(f)^{-1/4}\frac{(1,p-a)}{\sqrt{1-|p-a|^2}},\\
\gamma&=g(N_f,N_\ell)
 =\frac{1-|p|^2+p\cdot a}{\sqrt{(1-|p|^2)(1-|p-a|^2)}},\\
(1-|p|^2+p\cdot a)^2-(1-|p|^2)(1-|p-a|^2)
 &=k^2(1-|p|^2)+(p\cdot a)^2>0.
\end{aligned}\tag{J3}
```

Both face slopes are strictly below one by the original combined budget.
The numerator is positive by Cauchy--Schwarz applied to the two face slopes;
the displayed difference is strictly positive since k is nonzero. Thus gamma
is strictly greater than one, not just an unsigned solution of a squared
identity. Define theta as the positive arcosh of gamma. Pointwise conformal
rescaling cancels in gamma, but that fact has not evaluated an action.

The actual joint lift is z mapped to (f(z),z). For spatial tangents v,w
orthogonal to a, put b=p-(p dot n_h)n_h. Computing minus the restricted metric
and its Gram determinant gives

```math
\begin{aligned}
-g((p\cdot v,v),(p\cdot w,w))
 &=\sqrt{q(f)}\{v\cdot w-(p\cdot v)(p\cdot w)\},\\
dA_g&=\sqrt{q(f)}\sqrt{1-|b|^2}\,dA_\Sigma,\\
\coth\theta&=\frac{1-|p|^2+p\cdot a}{k\sqrt{1-|b|^2}},\\
\mathcal I_{\chi,\phi}
 &:=\int_{\mathrm{joint}}\chi\phi\coth\theta\,dA_g
 =\int_\Sigma\sqrt{q(f)}(\chi\phi)_{t=f}
                   \frac{1-|p|^2+p\cdot a}{k}\,dA_\Sigma.
\end{aligned}\tag{J4}
```

Here the spatial reference measure is normalized Euclidean area, not
Euclidean spacetime area. For a regular chart the positive square root of
its actual Gram determinant is the displayed density times its spatial area
Jacobian. On a chart overlap the chain rule multiplies both densities by the
absolute coordinate determinant. The ordinary area change-of-variables
formula therefore equates the induced measures on **every Borel subset of
the overlap**, including non-null overlaps and orientation-reversing frames.
A finite subordinate partition sums these measures independently of charts.

Compactness and continuity give fixed positive lower margins for k, both
normalization denominators, gamma minus one, and the induced area density.
The finite spatial area follows from the finite regular C³ graph atlas;
q(f) is bounded above and away from zero on it. The angle weight and both
field traces are bounded. Thus the measure is finite and the signed target
is absolutely integrable, independently of any action limit. These are
fixed-geometry margins, not uniform estimates near null faces or zero angle.

## 3. Flatten the actual two-boundary overshoot

We now prove the weighted comparison rather than citing the conventional
weighted estimate in #66 or transporting #89's unweighted flat theorem.
From (H2), set d=T+f(z)-f(z+rn). The corner integral is exactly

```math
\begin{aligned}
J_{\chi,\phi}^\delta(\rho)
 &=\int_{S^2}\int_0^\delta\int_0^v\frac{(v-u)^2}{8}
   \int_{\{z\in\mathcal O:h(z)\lt d\}}\int_{h(z)}^d
   q(f(z)-A)q(f(z)-A+T)\\
 &\qquad\cdot\chi(f(z)-A,z)\phi(f(z)-A+T,z+rn)
 K\!\left(c\rho(uv)^2\mathcal H(f(z)-A,u,v)\right)
 \,dA\,dz\,du\,dv\,dS(n).
\end{aligned}\tag{J5}
```

The sphere has mass 4 pi. The future slope margin gives positive d bounded
by v; hence only the regular height collar is used, never an interior
critical level. There is no same-chart restriction on the second endpoint.

Choose finitely many height charts z=Z_i(y,s), h(Z_i(y,s))=s, on a two-sided
collar, and smooth spatial weights sigma_i summing to one on a smaller
collar, compactly supported within these charts. All y integrals may be
taken on fixed compact planar domains. Their weighted volume Jacobians

```math
\begin{aligned}
G_i(y,s)&=\sigma_i(Z_i(y,s))|\det DZ_i(y,s)|,\\
G_i(y,0)\,dy&=\frac{\sigma_i(z)}{k(z)}\,dA_\Sigma(z)
\end{aligned}\tag{J6}
```

are C², not assumed C³. The second identity follows from the height
coordinate Jacobian/coarea normalization. All chart and face bounds below
are on fixed compact thickenings. Decrease delta once so the whole overshoot
lies in the smaller collar and the translated arguments in the common C³
future thickening. The mean-value estimate gives

```math
\begin{aligned}
d_s&=[Df(Z_i)-Df(Z_i+rn)]\cdot\partial_s Z_i,&|d_s|&\le L v\lt1/2.
\end{aligned}\tag{J7}
```

For fixed y,n,u,v introduce beta and lambda in [0,1] by solving

```math
\begin{aligned}
s&=\beta d(Z_i(y,s),u,v,n),&
A&=d[\beta+(1-\beta)\lambda],\\
\frac{\partial s}{\partial\beta}&=\frac{d}{1-\beta d_s},&
\left|\frac{\partial(s,A)}{\partial(\beta,\lambda)}\right|
 &=\frac{(1-\beta)d^2}{1-\beta d_s}.
\end{aligned}\tag{J8}
```

There is one unique root: s minus beta d is strictly increasing; its values
at zero and a sufficiently large fixed collar height bracket zero. It stays
between zero and v. Conversely beta=s/d maps the whole actual height interval
monotonically to [0,1], and lambda then maps exactly A in [s,d]. Thus (J8)
flattens the actual domain with both moving boundaries, including contact;
it is not an unproved positive-part jet. Its endpoints of zero Jacobian are
harmless measure-zero parameter faces. The map and its needed derivatives
extend to a small open parameter neighborhood.

## 4. Exact curved-phase transport and C³ derivative ledger

Suppress the chart index and fixed parameters y,n,beta,lambda. For v positive
let R=u/v and D=d/v after (J8)'s root substitution. With z_0=Z(y,0), f_0=f(z_0)
and p_0=Df(z_0), the tangent gap is

```math
\begin{aligned}
D_0(R)&=\frac{1+R}{2}-\frac{1-R}{2}p_0\cdot n,&
\alpha&=\beta+(1-\beta)\lambda,\\
t&=f(Z(y,s))-v\alpha D,&s&=\beta vD,\\
\Phi(v,R)&=R\sqrt{\mathcal H(t,vR,v)},&w&=v^2\Phi(v,R).
\end{aligned}\tag{J9}
```

The following uniform bounds use only the original C³ geometry:

```math
\begin{aligned}
\|D-D_0\|_{C^3_R}&\le L v,&
\|t-f_0\|_{C^3_R}&\le L v,&
\|d_s\|_{C^2_R}&\le L v,\\
\|G(y,s)-G(y,0)\|_{C^2_R}&\le L v,&
\|\Phi-R\sqrt{q(f_0)}\|_{C^3_R}&\le L v.
\end{aligned}\tag{J10}
```

Here R ranges in a fixed slightly enlarged interval about [0,1]. To check
the regularity explicitly, implicit differentiation of (J8) gives
s_R=O(v), s_RR=O(v²), s_RRR=O(v³). At fixed s, d_R is v times
`(1+Df(Z+rn)[n])/2`, d_RR is `-v²*D²f(Z+rn)[n,n]/4`, and d_RRR is
`v³*D³f(Z+rn)[n,n,n]/8`. The mixed terms in the root derivatives have the
same bounds, using (J7); d_sss need only be bounded, since it multiplies
s_R cubed. Expanding D and D_R at s=v=0 and using these next two derivatives
proves its C³ bound. Composition gives the t bound. Differentiating (J7)
twice in R uses at most D³f, and differentiating G twice uses only G_s and
G_ss. In particular no third derivative of a chart Jacobian is invoked.
The polynomial H then gives the last bound. The same first differentiations
in v give bounded D_v, t_v, (d_s)_v, G_v and Phi_v in C¹_R wherever needed;
Taylor's divided-difference cancellations remove the apparent 1/v factors.
All constants are uniform on the finite compact parameter family.

Consequently, after decreasing the fixed delta again, Phi_R is uniformly
positive. Solve zeta=w/v²=Phi(v,R) for R=U(v,zeta). The inverse differs from
`zeta/sqrt(q(f_0))` by O(v) in C³_zeta; its first v derivative and its first
mixed v,zeta derivative are bounded. These assertions follow by differentiating
the inverse equation and its first three zeta derivatives; the reference
phase is linear and Phi_R stays away from zero.

The exact pushed amplitude, including (J8), is

```math
\begin{aligned}
B(w)&=\int_{\nu(w)}^\delta a(w,v)\,dv,\\
a(w,v)&=v^3\Psi(v,w/v^2),\\
\Psi(v,\zeta)&=\left.
\frac{(1-\beta)D^2(1-R)^2G(y,s)q(t)q(t+v(1+R)/2)}
 {8(1-\beta d_s)\Phi_R}
 \chi(t,Z(y,s))\phi(t+v(1+R)/2,Z(y,s)+v(1-R)n/2)
 \right|_{R=U},\\
\Psi(v,\zeta)&=\Psi_0(\zeta)+E(v,\zeta),\\
|\partial_\zeta^j E|&\le L v\quad(j=0,1,2),\qquad |E_v|\le L.
\end{aligned}\tag{J11}
```

The integral is zero if its lower endpoint exceeds delta. Psi_0 is obtained
by setting v=0 in the displayed formula: its factors are D_0, G(y,0),
q(f_0)², the two joint traces, and the phase derivative sqrt(q(f_0)).
The E estimates follow directly from (J10), the inverse estimates and the
product/quotient rules. The two zeta derivatives of 1/Phi_R use the third
ratio derivative of Phi, not a fourth geometry derivative. Endpoint-field
and partition derivatives are included in E; they are not set to zero.
In particular Phi_R differentiates the **moving source time**, including
both s_R and A_R, not just the explicit u dependence of H.

## 5. Moving diagonal and the signed comparison estimate

At R=1, d=v, s=beta v and A=alpha v exactly. The lower endpoint solves

```math
\begin{aligned}
w&=\nu^2\sqrt{\mathcal H(f(Z(y,\beta\nu))-\alpha\nu,\nu,\nu)},&
\nu_0&=\sqrt w\,q(f_0)^{-1/4},\\
\nu&\asymp\sqrt w,&|\nu-\nu_0|&\le Lw.
\end{aligned}\tag{J12}
```

The diagonal is increasing for the same small fixed cutoff. This follows
from its expansion as v² times a positive C¹ function, uniformly on the
compact parameters. Choose one small phase collar where both lower endpoints
are below delta/2. Subtract the pushed tangent amplitude, which is
`v³*Psi_0(w/v²)` with lower endpoint nu0. On that collar the **exact** difference is

```math
\begin{aligned}
B(w)-B^{\mathrm{tan}}(w)
 &=\int_{\nu_0}^\delta e(w,v)\,dv
    +\int_\nu^{\nu_0}a(w,v)\,dv,&e(w,v)&=v^3E(v,w/v^2),\\
|\partial_w^j e|&\le L v^{4-2j}\quad(j=0,1,2),&|e_v|&\le L v^3,\\
\left|\int_\nu^{\nu_0}a(w,v)\,dv\right|&\le Lw^{7/2}.
\end{aligned}\tag{J13}
```

The last integral is oriented, not discarded or clipped. On its interval
v is comparable to sqrt(w); the length is O(w) and 1-U is O(sqrt(w)).
The exact factor `(1-U)²` in (J11) therefore makes a of order w^(5/2).
The smooth local continuation for U just above one cancels in this oriented
identity. It does not add a physical partner.

For the first integral in (J13), differentiating twice gives

```math
\begin{aligned}
\left(\int_{\nu_0}^\delta e\,dv\right)''
 &=\int_{\nu_0}^\delta e_{ww}\,dv
   -2e_w(\nu_0)\nu_0'-e_v(\nu_0)(\nu_0')^2-e(\nu_0)\nu_0''.
\end{aligned}\tag{J14}
```

Every boundary term is O(sqrt(w)), and e_ww has an integrable constant
majorant in v. The zeroth and first derivatives have stronger bounds.
Split v at a fixed positive epsilon: above it the relevant derivatives are
uniformly continuous on compact sets; below it (J13) bounds their integrals
by constants times epsilon^(5-2j). Taking w to zero, then epsilon to zero,
proves uniform right limits for all three derivatives. The fundamental
theorem of calculus supplies a uniform right quadratic Peano jet. The
oriented strip is of higher order and has zero such jet. Thus

```math
\begin{aligned}
B-B^{\mathrm{tan}}&=b_0+b_1w+b_2w^2+w^2\epsilon(w),&
\sup|\epsilon(w)|&\longrightarrow0,\\
b_j&=\frac1{j!}\int_0^\delta\partial_w^j e(0,v)\,dv\quad(j=0,1,2).
\end{aligned}\tag{J15}
```

The coefficients are bounded and measurable (indeed continuous) in the
compact chart/direction/depth parameters. Actual and tangent amplitudes have
common bounded phase support and are bounded, including their cutoff
endpoints. Consequently the quotient after subtracting this polynomial and
dividing by w² is bounded on the **whole positive half-line**. The three
exact signed moments are

```math
\begin{aligned}
\int_0^\infty z^jK(z^2)\,dz&=0\quad(j=0,1,2),&
\int_0^\infty z^2|K(z^2)|\,dz&\lt\infty.
\end{aligned}\tag{J16}
```

Subtract the polynomial on that whole half-line, rescale by sqrt(c rho),
and apply dominated convergence with the second integrand in (J16). This
proves, uniformly before the finite compact parameter integrations,

```math
\begin{aligned}
C\rho^{3/2}(J_{\chi,\phi}^\delta-J_{\chi,\phi}^{\mathrm{tan},\delta})
 &\longrightarrow0.
\end{aligned}\tag{J17}
```

This is a signed, fully normalized estimate for the actual curved phase,
Jacobians and weights. It is not absolute domination of the original
nearly-null kernel, and not an endpoint-frozen approximation used without
an error proof. Macroscopic partners remain in #121's already averaged long
sector; the raw-first-endpoint obstruction from #118 is not contradicted.

## 6. Evaluate the tangent model and restore the single-face flux

At v=0 in the smooth amplitude, integrating beta and lambda gives 1/2;
(J6) sums the chart weights to one. Therefore the tangent integral identified
by the proof, with the same sharp cutoff, is precisely

```math
\begin{aligned}
J_{\chi,\phi}^{\mathrm{tan},\delta}
 &=\int_\Sigma\frac{q(f)^2(\chi\phi)_{t=f}}{2k}
 \int_{S^2}\int_0^\delta\int_0^v
 \frac{(v-u)^2}{8}(T-rp\cdot n)^2
 K(c\rho q(f)(uv)^2)\,du\,dv\,dS(n)\,dA_\Sigma.
\end{aligned}\tag{J18}
```

This is not a definition of J. Its replacement has now been justified by
(J17), without importing a flat weighted localization theorem. Sphere
averaging gives `T² + |p|²*r²/3`. The finite-cutoff radial primitives and the
signed logarithmic moment in (C12)/(H14), with **positive** C rho^(3/2)
normalization, give responses `-2*q^(-3/2)` to T²K and `6*q^(-3/2)` to r²K.
They use sphere mass 4 pi; no extra angular factor is hidden. Their polynomial
pieces cancel by (J16), while their logarithmic pieces survive. Uniformity
holds over the fixed compact range of q(f). Thus

```math
\begin{aligned}
-C\rho^{3/2}J_{\chi,\phi}^\delta
 &\longrightarrow\int_\Sigma\sqrt{q(f)}(\chi\phi)_{t=f}
                                      \frac{1-|p|^2}{k}\,dA_\Sigma,\\
\mathcal T_{\chi,\phi}
 &=-\int_\Sigma\sqrt{q(f)}(\chi\phi)_{t=f}\frac{p\cdot a}{k}\,dA_\Sigma,\\
\mathcal Q_{\chi,\phi}^\delta(\rho)
 &=-C\rho^{3/2}J_{\chi,\phi}^\delta-\mathcal T_{\chi,\phi}
 \longrightarrow\mathcal I_{\chi,\phi}.
\end{aligned}\tag{J19}
```

In particular the normalized actual corner has a finite limit and is
eventually bounded, not merely a conjectured coefficient. Fixed-density
continuity follows from compact domination in (J5); as rho decreases to zero,
its normalized term tends to zero by the same bound. Together these facts
also give boundedness over all positive densities for each fixed geometry,
cutoff and pair of fields.

The second line is exactly (H15), with outward normal minus a/k. It generally
survives even for unit weights. Dropping it would omit p dot a from the
geometrically derived (J4), giving the wrong answer. Curvature and field
variation inside J are in the controlled error (J17); this does **not** remove
the separate bulk curvature term or either spacetime-face flux from #74.

## 7. Finite summation and the #76 consumer boundary

For any finite first-endpoint partition with sum one near the whole auxiliary
tube, (J5), (J18) and T sum exactly at every density. The proof's constants
may be maximized over that finite family, or its errors summed; all tend to
zero at one common fixed cutoff. Overlapping, signed and refined chart
partitions are allowed. A partition at the second endpoint likewise requires
the full double sum. Keeping only equal chart indices deletes real partners
and is not a localization theorem.

Partition derivatives inside J occur in E and are controlled by (J13)-(J17).
The derivatives in #74's full/single-face terms remain the explicit B and N
of (H16); for phi=1 they cancel only on summing a whole source partition.
For nonconstant phi both spacetime fluxes (H17) remain. No individual weighted
patch is asserted to have just the unweighted action target.

The joint limit (J19) is independent of any permitted **fixed** cutoff and
of field extensions agreeing on M: its right side uses only joint traces.
There is no limit exchange with a shrinking cutoff, singular angle, or
changing geometry. Combined with the already supplied (H16), the summable
consumer output is

```text
CurvedJointCornerLimit supplies I_chi,phi to the existing #74 handoff:
  A_chi,phi - B_chi,phi - N_chi,phi - Q_chi,phi -> 0
  Q_chi,phi -> I_chi,phi
For unit fields: B = half the whole curvature integral; N = 0.
#76 owns the explicit complete deterministic/expected-action assembly and
acceptance audit using #93's separate exact positive-density equality.
```

No probability law is redefined or expectation identity used in this proof.
No rates, arbitrary smooth conformal-factor extension, general curved class,
or individual-sprinkling convergence are claimed.

## 8. Nonzero curvature and varying-angle regressions

Use the original unequal-axis height and two future profiles

```math
\begin{aligned}
h(z)&=\tfrac14(1-z_1^2-z_2^2/4-z_3^2/9),\\
f(z)&=\tfrac18\quad\text{or}\quad\tfrac18+\varepsilon\sin z_1,
 &0&\le\varepsilon\le1/16.
\end{aligned}\tag{J20}
```

The positive-part height is globally 1/2-Lipschitz, the future slope at most
1/16, and their sum is strictly below one. All germs are smooth; k on the
joint ranges from 1/6 to 1/2. The critical point at positive height 1/4 remains
inside the region. For the sine profile the joint time, induced area factor
and angle vary; compact bounds follow as above. On a fixed neighborhood with
absolute time below one, Omega is between one and 2^(1/4). Direct curvature
contraction in the pilot's sign convention gives

```math
\begin{aligned}
R(t)&=3(1-t^2/2)(1+t^2)^{-5/2}>0\quad(|t|\lt1).
\end{aligned}\tag{J21}
```

This is opposite the example sign in #93, as already recorded in (C4)/(C5);
it changes no action API. The planar-future unequal-axis case has coth theta
values 2 and 6 at the first and third axis tips, so even this simpler curved
spacetime has genuinely varying angle. Its unit-weight target is
`48*pi*sqrt(65/64)`, derived from (J4) and the ellipsoidal coarea integral,
not fitted to quadrature. The theorem covers **both** profiles (J20), every
fixed endpoint field in its class, and their original geometry, not just the
numerical sample points.

`curved_joint_corner.py` provides exact algebra certificates. The regressions
compare actual coordinate and flattened integrals, curved normal/Gram
geometry, the tangent coefficient and retained flux, signed weights,
partitions and fixed cutoffs. Numerical convergence is diagnostic evidence,
not the proof of (J17) or the full conjecture. Flat and positive constant
factors calibrate the area scaling; dropping an endpoint measure, freezing
the phase without the proved comparison, dropping T, or using Euclidean
spacetime area are explicitly distinguished from the correct observable.

## 9. Acceptance and verification ledger

- **Same nonvacuous class and independent geometry:** (J1)-(J4), all original
  margins, finite induced chart-compatible area, positive normal angle, and
  the nonzero-curvature/varying-angle examples (J20).
- **Actual weighted tangent estimate with all partners:** (J5)-(J17), both
  endpoint measures, exact ambient auxiliary phase and moving Jacobians,
  including the oriented diagonal strip. No entire #66 estimate or #89
  global weighted theorem is cited as checked.
- **Retained terms and coefficient:** (J19) restores the nonzero single-face
  joint flux. Curvature/partition/field corrections in the corner have proved
  signed control; #74's bulk and spacetime-face terms are not deleted.
- **Common fixed cutoff and summability:** §7 supplies exactly the weighted
  producer for (H16)/(H18), compatible with #121's long sector. No additional
  shrinking-cutoff estimates or unsupported interchange are needed.
- **Evidence boundaries:** the general theorem is written, not Lean-checked.
  Exact symbolic identities and finite quadratures test separate parts.
  Independent human mathematical review is still outstanding. Existing Lean
  geometry and the canonical finite-density API retain their prior status;
  no new full Lean audit is claimed for this Python/documentation package.

```sh
.venv/bin/python -m unittest -v test_curved_joint_corner
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
