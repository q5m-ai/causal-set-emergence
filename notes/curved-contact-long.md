# Contact-averaged curved long cancellation (#117)

**Written result, not a new Lean theorem.** For every original
`AdmissibleTwoFace`, the fixed density `Omega(t)^4 = 1+t^2`, every fixed
positive cutoff, and the smooth endpoint weights specified below, this note
derives the actual contact-averaged right quadratic jet and proves normalized
signed long cancellation. The averaging is essential: the raw
first-spacetime-endpoint domination disproved in
[PR #118 at `9368af9`](https://github.com/q5m-ai/causal-set-emergence/blob/9368af97c6fbc34acf21b85335bda7f30652cdd2/notes/curved-remainders.md)
is neither assumed nor recovered.

This completes the bounded **long-sector** analytic input, not #74's actual
short remainder or supported half-curvature theorem. #75 still needs the
accepted common short/boundary output and its independent joint comparison;
#76 still needs compatible proved bulk and joint components before using the
separate expectation bridge. Independent human mathematical review remains
outstanding. Symbolic/numerical regressions below are evidence separate from
the conventional proof.

## 1. Frozen observable and weighted contract

The source baseline is `bbfafa1e94440cee5bcc3989f4deea995d0979a3`.
`ConformalAction.lean`, `ConformalGeometry.lean`, and `FiniteMeasureBDG.lean`
were compared with #93's audited candidate
`9aed02c70f01c9fd4c5d14e5e4b1024d94f8367f`: unchanged. [PR #101](https://github.com/q5m-ai/causal-set-emergence/pull/101)
records that candidate's audit. This comparison is **not** a new integrated
Lean audit. The production observable is still `conformalAction`, with its
closed causal order, exclusive interval endpoints, both endpoint measures,
and actual restricted interval volume. Causal convexity and atomlessness
identify the latter with the ambient curved interval integral, not the flat
proper-time formula.

Write H for the positive part of the original height h, and set
$`\ell(z)=f(z)-H(z)`$. Its global Lipschitz constants obey
$`\kappa+\eta\lt1`$ for H and f respectively; put
$`m=1-\kappa-\eta>0`$ and $`d_*=(1-\eta)/2>0`$.
The region is $`M=\{(t,z):\ell(z)\lt t\lt f(z)\}`$.
Keep all its original C³ germs, compactness and joint margins, including
positive-height critical points. Fix

```math
\begin{aligned}
q(t)&=1+t^2,&d\mu_g&=q(t)\,dt\,dz,&c&=\pi/24,&C&=4/\sqrt6,\\
K(s)&=(1-9s+8s^2-\tfrac43s^3)e^{-s}.&&&&
\end{aligned}\tag{A1}
```

Let chi and phi be real C² functions on open neighborhoods of the whole
closure of M, independent of density, with their derivatives bounded on
smaller compact neighborhoods. Smooth weights in #74/#75 meet this contract;
constant one is allowed, and support need not avoid either face or the joint.
Signed weights are allowed. The weighted notation means precisely

```math
\begin{aligned}
P_{\chi,\phi}^{\ge}(\rho)
 &=\int_M\int_{M\cap J^+(x)}\chi(x)\phi(y)
    \mathbf1_{\{v\ge\delta\}}K(\rho V_M(x,y))\,d\mu_g(y)\,d\mu_g(x),\\
L_{\chi,\phi}(\rho)&=-C\rho^{3/2}P_{\chi,\phi}^{\ge}(\rho),
 \qquad \delta>0\text{ fixed}.
\end{aligned}\tag{A2}
```

Every future partner is retained. Here $`v=y^0-x^0+|\mathbf y-\mathbf x|`$;
equality belongs to the long sector. No partition restriction is imposed on
the second endpoint. A second-endpoint field is a genuine weight, not a reason
to discard its derivative terms. The theorem proved below is
$`L_{\chi,\phi}(\rho)\to0`$. It is not inferred from a flat weighted theorem.

## 2. Actual phase transport and time averaging

Use $`x=(t,z)`$, $`n\in S^2`$, and
$`y=(t+(u+v)/2,z+(v-u)n/2)`$, with $`0\le u\le v`$.
Ordinary sphere area has mass $`4\pi`$ and the displacement Jacobian is
$`(v-u)^2/8`$. The exact polynomial-density interval law is

```math
\begin{aligned}
V_M(x,y)&=cu^2v^2\mathcal H(t,u,v),\\
\mathcal H&=1+t^2+\tfrac12t(u+v)+\tfrac3{40}(u+v)^2-\tfrac1{30}uv,\\
\mathcal H&=1+(t+(u+v)/4)^2+(3u^2-2uv+3v^2)/240,\\
2\mathcal H+u\mathcal H_u
 &=2+2(t+3u/8+v/4)^2+(3u^2-4uv+4v^2)/160.
\end{aligned}\tag{A3}
```

The final two quadratic forms are positive. Thus
$`w=F(t,u,v)=uv\sqrt{\mathcal H}`$ has
$`F_u=v(2\mathcal H+u\mathcal H_u)/(2\sqrt{\mathcal H})>0`$ for
positive v, and a smooth inverse $`u=U(t,v,w)`$ at and to the right of zero.
It is globally increasing for nonnegative u, starts at zero, and tends to
infinity. In particular $`0\le U\le w/v`$. The phase is exactly
$`\rho V_M=c\rho w^2`$, not frozen at the source density.

Choose a fixed D greater than delta and so large that
$`H_{\max}-d_*D\lt-1`$. All actual long partners have $`v<D`$:
strict upper slope and $`t>\ell(z)`$ imply
$`H(z)>(1-\eta)(u+v)/2\ge d_*v`$.
For small $`0\le w\le e\lt\delta^2/2`$, the condition $`U\le v`$
is automatic. Define the actual upper gap and the full smooth density

```math
\begin{aligned}
G(t,v,w;z,n)&=f(z+(v-U)n/2)-t-(v+U)/2,\\
a(t,v,w;z,n)&=\chi(t,z)\phi(y)q(t)q(t+(v+U)/2)
                \frac{(v-U)^2}{8F_u(t,U,v)},\\
\mathcal F(w;z,n)&=\int_\delta^D\int_{\ell(z)}^{f(z)}
       \mathbf1_{\{U\le v\}}\mathbf1_{\{G>0\}}a(t,v,w;z,n)\,dt\,dv.
\end{aligned}\tag{A4}
```

The last formula defines the fibre for **all** nonnegative w, not only in the
small collar. Empty time intervals mean zero, since $`\ell\le f`$.
The lower-envelope condition on y is automatic for a causal displacement
from x in M: the strict causal epigraph retains it. Thus (A4) is the actual
pair-domain fibre, including both measures. It is not a substituted overlap
model. At each positive density, bounded weights, finite region volume and
bounded kernel justify absolute Fubini and phase transport:

```math
\begin{aligned}
B(w)&=\int_{\mathbb R^3\times S^2}\mathcal F(w;z,n)\,dz\,dS(n),\\
P_{\chi,\phi}^{\ge}(\rho)&=\int_0^\infty K(c\rho w^2)B(w)\,dw.
\end{aligned}\tag{A5}
```

We use (A4) only where its indicators are active; expressions containing phi
elsewhere can be defined by any bounded measurable extension. Smooth
extensions are used below solely on compact neighborhoods of actual endpoint
pairs. B and the fibres are measurable, uniformly bounded and compactly
supported in phase: actual pairs have bounded u, v and t, and
$`F_u\ge v/\sqrt{\mathcal H}`$; all densities and weights are bounded there.
Their spatial support is inside the finite-measure compact set
$`P=\{z:H(z)\ge m\delta/2\}\times S^2`$.

### Why the time boundary is regular without an extra geometric hypothesis

At zero phase set

```math
\begin{aligned}
\tau_0(v)&=f(z+vn/2)-v/2,\\
g_0(v)&=\tau_0(v)-\ell(z)
       =H(z)+f(z+vn/2)-f(z)-v/2.
\end{aligned}\tag{A6}
```

Global Lipschitz control gives
$`g_0(v_2)-g_0(v_1)\le-d_*(v_2-v_1)`$ for $`v_2\ge v_1`$.
At every nonnegative old gap with $`v\ge\delta`$, the source and target
heights are at least $`m\delta/2`$. The source estimate uses upper slope;
the target estimate uses the lower-envelope slope $`\kappa+\eta`$.
All such endpoints therefore lie in compact **positive-height** tubes.
The original C³ face germs, not any raw exterior smoothness, supply uniform
derivative bounds on slightly larger tubes. The same applies to endpoint
weights on compact neighborhoods of the closure. Perturbations of size
$`O(w/\delta)`$ remain there for a common e.

On this compact old-active set, $`G(t,v,0)=\tau_0(v)-t`$ and
$`G_t(t,v,0)=-1`$. The uniform implicit function theorem therefore gives a
C³ time boundary $`t=\tau(v,w)`$ with $`G(\tau,v,w)=0`$; the weights
need only be C². Its local extensions agree by uniqueness. For a common
smaller e, $`G_t\le-1/2`$ on a fixed neighborhood of this boundary.
Outside that neighborhood the sign is unchanged by uniform continuity, so
this root describes the **whole** actual time interval, not just a local
piece of it.

At every fixed t the strict upper Lipschitz bound gives
$`G(t,v,w)\le G(t,v,0)-(1-\eta)U/2`$.
Consequently $`\tau(v,w)\le\tau_0(v)`$, and compact inverse/root bounds give

```math
\begin{aligned}
0\le\tau_0(v)-\tau(v,w)&\le A_\delta w,\\
\partial_v\tau(v,w)&\le-d_*/2
\quad\text{on the old-active tube, for }0\le w\le e.
\end{aligned}\tag{A7}
```

Also $`\tau_0(v)\le f(z)-d_*\delta`$, so the source upper face never
cuts this time interval. Null gaps that are negative or zero cannot open
on the right, even where f is only globally Lipschitz. This covers exact
cutoff contacts of positive parameter measure and all exceptional directions;
no assertion that a contact set has measure zero is used.

If $`g_0(\delta)>0`$, there is one old root $`R\in(\delta,D)`$.
Define the **oriented smooth extension**

```math
\begin{aligned}
J(w,v)&=\int_{\ell(z)}^{\tau(v,w)}a(t,v,w)\,dt,\\
\mathcal F(w;z,n)&=\int_\delta^R
       \mathbf1_{\{\tau(v,w)>\ell(z)\}}J(w,v)\,dv
       \qquad(0\le w\le e).
\end{aligned}\tag{A8}
```

The oriented integral is used only for Taylor analysis, including where tau
has just passed below ell; the indicator restores the actual integral.
All needed extensions stay in the fixed compact tubes above. If
$`g_0(\delta)\le0`$, the actual fibre is identically zero on the right.
This is the essential extra averaging compared with the raw t fibres:
**J vanishes at its contact**.

## 3. Both moving boundaries and every derivative term

Write $`a_j=\partial_w^j a(t,v,0)`$, $`\tau_j=\partial_w^j\tau(v,0)`$,
and $`d(v)=(1-Df(z+vn/2)[n])/2\ge d_*`$.
All t boundary evaluations in the following display are at $`t=\tau_0(v)`$:

```math
\begin{aligned}
J_0(v)&=\int_\ell^{\tau_0}a_0\,dt,\\
J_1(v)&=\int_\ell^{\tau_0}a_1\,dt+a_0(\tau_0,v)\tau_1,\\
J_2(v)&=\frac12\int_\ell^{\tau_0}a_2\,dt
 +a_1(\tau_0,v)\tau_1
 +\frac12\partial_ta_0(\tau_0,v)\tau_1^2
 +\frac12a_0(\tau_0,v)\tau_2.
\end{aligned}\tag{A9}
```

These are Taylor **coefficients**, not all derivatives. In particular the
source time derivative in the third line includes the derivative of chi;
a1 and a2 retain phase, inverse-Jacobian, second-endpoint density and field
derivatives. Nothing is set to zero merely because the production field is
one. At zero phase, with all H derivatives evaluated at
$`(t,u,v)=(\tau_0(v),0,v)`$, put $`b=(1+Df[n])/2`$. Then

```math
\begin{aligned}
U_w&=\frac1{v\sqrt{\mathcal H}},&
U_{ww}&=-\frac{\mathcal H_u}{v^2\mathcal H^2},&
U_{tw}&=-\frac{\mathcal H_t}{2v\mathcal H^{3/2}},\\
\tau_1&=-\frac b{v\sqrt{\mathcal H}},&
\tau_2&=\frac{D^2f[n,n]}{4v^2\mathcal H}
       +\frac{b\mathcal H_u-b^2\mathcal H_t}{v^2\mathcal H^2}.
\end{aligned}\tag{A10}
```

For example differentiate $`G(\tau(v,w),v,w)=0`$ twice:
$`\tau_2=G_{ww}+2G_{tw}\tau_1`$ at zero, since $`G_t=-1`$
and $`G_{tt}=0`$. This gives (A10), including the mixed phase derivative.

For an active cutoff define

```math
\begin{aligned}
F_0&=\int_\delta^R J_0(v)\,dv,\\
F_1&=\int_\delta^R J_1(v)\,dv,\\
F_2&=\int_\delta^R J_2(v)\,dv
       +\frac{a_0(\ell,R)\tau_1(R)^2}{2d(R)}.
\end{aligned}\tag{A11}
```

All three are zero on nonpositive cutoff gaps. The last term is the remaining
v-contact contribution. Its sign follows the endpoint weights; for positive
weights it is positive. It must not be dropped. There is no first-order
v-contact term because $`J_0(R)=0`$.

Here is a direct derivation valid without a uniform active distance from the
cutoff. In the layer lost from the old interval, set $`v=R-ws`$. Pointwise
for each active parameter,
$`(\tau(v,w)-\ell)/w\to d(R)s+\tau_1(R)`$ and
$`J(w,v)/w\to a_0(\ell,R)(d(R)s+\tau_1(R))`$.
The correction to the oriented integral is its negative on the lost interval.
By (A7) that interval has length at most $`A_\delta w/d_*`$; hence bounded
convergence in s gives precisely the triangle area
$`a_0(\ell,R)\tau_1(R)^2/(2d(R))`$ after division by $`w^2`$.
Equivalently the moving v root has derivative $`\tau_1(R)/d(R)`$;
Leibniz' rule gives the same term. Its acceleration multiplies J0(R)=0,
not a silently neglected nonzero boundary value.

## 4. Dominated right jet on the remaining variables

On each old fixed interval (A8), the C² smooth integral has its Peano expansion
with coefficients (A9). Compact derivative bounds give a uniform quadratic
error after subtracting its first two terms. On the lost layer,
$`0\le g_0\le A_\delta w`$ and $`|\tau-\ell|\le A_\delta w`$.
Its length is at most $`A_\delta w/d_*`$, and
$`|J|\le\|a\|_\infty A_\delta w`$. Thus its correction is uniformly
$`O_\delta(w^2)`$, including when the whole old interval has already closed.
The coefficients (A9)–(A11) themselves are uniformly bounded on P. Together
with the pointwise triangle limit this proves

```math
\begin{aligned}
\mathcal F(w;p)&=F_0(p)+F_1(p)w+F_2(p)w^2+w^2E(w;p),\\
E(w;p)&\longrightarrow0\quad(w\downarrow0)\text{ for every }p=(z,n),\\
|E(w;p)|&\le C_\delta\mathbf1_P(p),\qquad 0\lt w\le e.
\end{aligned}\tag{A12}
```

For fixed active p the lost interval eventually does not reach delta, so the
pointwise triangle calculation applies. For exact/nonpositive cutoff contact
all quantities are zero. Approaching active contacts need not have a
**uniform** little-o remainder; the uniform O bound in (A12) is sufficient.
No spatial critical point, direction or cutoff level has been removed.

Measurability does not require selecting roots measurably: F0 is the measurable
zero probe of (A4), F1 is the limit of its measurable first difference
quotients along a fixed positive sequence, and F2 is the corresponding second
quotient after subtracting F0 and F1. Formula (A12) proves these limits
pointwise. The uniform compact bounds give $`|F_j|\le C_j\mathbf1_P`$,
so all coefficients are integrable. Dominated convergence on the **remaining**
space/direction variables, after the time and v integrations, proves

```math
\begin{aligned}
B(w)&=b_0+b_1w+b_2w^2+o(w^2),& b_j&=\int F_j(p)\,dp.
\end{aligned}\tag{A13}
```

This proves the required jet for the actual indicator-weighted amplitude.
It does not assume cancellation or a jet in geometric admissibility.

## 5. Fully normalized signed limit and summable interface

The original kernel has the exact signed moments
$`\int_0^\infty z^jK(z^2)\,dz=0`$ for j=0,1,2. Subtract the polynomial
of (A13) on the **whole half-line** before taking absolute values. Its
remainder quotient is bounded: use (A12) near zero and bounded compact support
of B away from zero, where its degree-two polynomial has bounded quotient.
With $`s=\sqrt{c\rho}`$, the exact normalized expression is

```math
\begin{aligned}
L_{\chi,\phi}(\rho)
 &=-\frac C{c^{3/2}}\int_0^\infty z^2K(z^2)
 \frac{B(z/s)-b_0-b_1z/s-b_2(z/s)^2}{(z/s)^2}\,dz
 \longrightarrow0.
\end{aligned}\tag{A14}
```

The value of the quotient at z=0 is irrelevant. Its dominating function is
a constant times $`z^2|K(z^2)|`$, which is integrable. Alternatively use
(A12) before integrating p: bounded phase support and the same coefficient
bounds extend its quotient bound to the whole half-line by a constant times
1P. This yields an integrable density-uniform bound for the **time-averaged**
normalized signed fibre and its limit zero, for every fixed positive lower
density threshold. It supplies no integrable bound on the raw t fibre.

For clarity, the written consumer signature is:

```text
PROVED IN WRITING CurvedContactAveragedLong(h, f, delta, chi, phi):
  original AdmissibleTwoFace h f; q(t)=1+t^2; fixed delta>0;
  fixed real C2 endpoint weights on neighborhoods of closure M
  actual restricted interval and both endpoint measures as in #93
  actual time/v-averaged coefficients F0,F1,F2, measurable and integrable
  right quadratic Peano jet with |E(w;p)| <= C_delta * 1_P(p)
  -C*rho^(3/2) * P_long(chi,phi;rho) -> 0
```

This is a theorem-contract description, **not a compiled Lean declaration**.
For every finite smooth first-endpoint partition with sum one on M, take
phi=1 and sum (A2). At each finite density the point/pair identity is exactly

```math
\begin{aligned}
A_g(\rho,M)&=\sum_i\left(S_{\chi_i,1}(\rho)+L_{\chi_i,1}(\rho)\right),\\
S_{\chi,\phi}(\rho)&=C\sqrt\rho\int_M\chi\phi\,d\mu_g
                   -C\rho^{3/2}P_{\chi,\phi}^{<}(\rho).
\end{aligned}\tag{A15}
```

The point term is allocated once to short; the complementary cutoff is
strict. No cross-chart partner is removed. A finite family of endpoint
fields can also be summed by linearity, but the derivative and contact terms
in (A9) must remain until that sum is performed. This theorem covers exactly
such smooth weighted long terms, not arbitrary measurable weights or any
weighted short/joint theorem. Constants may depend on geometry, cutoff and
weights. No shrinking-cutoff uniformity or convergence rate is asserted.

No additional long term survives in this class. This does **not** identify a
bulk or joint coefficient: those still require the actual short analysis,
independent curvature/area identification and compatible boundary accounting.
The separately checked finite-density expectation theorem is not used in
this proof, and alone supplies no curved expectation limit.

## 6. Actual regression geometries and negative controls

`curved_contact_long.py` supplies exact phase/Leibniz certificates;
`test_curved_contact_long.py` evaluates the actual region fibres independently.
The fixtures use
$`h(z)=(1-\sum_i(z_i/b_i)^2)/4`$,
$`f(z)=1/8+\epsilon\sin z_1`$, with axes at least one and
$`|\epsilon|\le1/8`$. Their positive-height slope bound is at most 1/2,
the future bound is at most 1/8, and all joint/face margins are unchanged.
They include:

- The planar-future unit ball, its positive-height critical center, exact
  cutoff contacts and approaching active contacts. Numerical evaluation uses
  the actual phase inverse and time interval, not an assumed hinge.
- The required unequal-axis member $`(b_1,b_2,b_3)=(1,2,3)`$, epsilon=0.
  Its spacetime scalar curvature is
  $`3(1-t^2/2)/(1+t^2)^{5/2}`$, nonzero on this region, independently of the
  action. The positive-normal angle weights at the first/third axis joint
  points are 2 and 6; conformal rescaling preserves the angle. A nonzero sine
  future additionally exercises the Hessian term in (A10).
- Nonconstant signed source and target weights, including a time-varying source,
  so omitting either measure, mixed phase derivatives, source derivatives,
  field derivatives or either moving-boundary contribution is detectable.
- Original-coordinate signed pair quadrature versus the phase-pushed,
  time-averaged expression. Kernel signs and the original normalization remain.
- The raw-first-endpoint negative control from #118, independently reproduced
  in the fixed planar region. Near its time contact put
  $`a=2(f-t)-\delta>0`$ and probe
  $`\rho_a=(1/100)/(2ca^2(\delta+a)^2)`$. All long partners are then in the
  positive kernel band; their normalized signed mass grows at least like
  $`1/a`$. This is nonintegrable in source time. Averaging before domination
  avoids, rather than contradicts, that obstruction.

At a source-space cutoff contact in the planar geometry,
$`g_0(\delta)=0`$, the whole time-averaged right fibre is zero. Approaching
from active source points, take the unit-ball fixture with delta=1/8 and
unit weights. Let p_a approach the contact along the first spatial axis,
with $`g_0(\delta;p_a)=a>0`$, and write a_c, d_c and tau_c for the values
of a0, d and tau1 at the limiting contact. For bounded nonnegative lambda,
(A8) and ordinary smooth Taylor estimates give the uniform scaling

```math
\begin{aligned}
\mathcal F(a\lambda;p_a)&=\frac{a_c}{2d_c}\,a^2
       (1+\tau_c\lambda)_+^2+O(a^3).
\end{aligned}\tag{A16}
```

This is a local scaling diagnostic, not a substituted amplitude; the additive
error also makes sense when the fibre has closed. At sources whose gap is
proportional to w, the quadratic
remainder quotient can stay nonzero but bounded. Tests distinguish that
behavior from both exact-contact zero and the divergent raw-time quotient.

## 7. Verification and handoff boundary

- **Conventional proof:** actual disintegration, compact positive-height tubes,
  regular time boundary, both moving-contact contributions, dominated remaining
  jet and signed normalized limit, §§2–5. Requires independent human review.
- **Executable evidence:** exact symbolic certificates and independent
  high-precision/original-coordinate quadrature regressions. Finite tests do
  not prove the universal theorem or a full-action limit.
- **Lean:** no Lean source, checker, dependency or build input changes. No new
  Lean proof or integrated audit is claimed. A formal port must pass the full
  local `formal/check.sh` source/transitive-axiom gate after its last
  validation-affecting change.
- **Still open:** #74's actual short remainder and supported half-curvature
  theorem; #75's curved joint comparison and coefficient; #76's complete
  deterministic/expected assembly. No arbitrary conformal-factor extension,
  density-dependent geometry, full-action rate, shrinking-cutoff interchange,
  general curved limit or individual-sprinkling convergence follows.

```sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
