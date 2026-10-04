# Interior short remainder and supported curved bulk (#74)

**Written theorems, not new Lean proofs.** This note proves
`CurvedInteriorShortRemainder` from the actual integral for the fixed density
`Omega(t)^4 = 1+t^2`. It then consumes
[`CurvedContactAveragedLong`](curved-contact-long.md#5-fully-normalized-signed-limit-and-summable-interface)
from merged [PR #121](https://github.com/q5m-ai/causal-set-emergence/pull/121),
without re-proving that theorem, to obtain the supported bulk response.
The coefficient is compared with scalar curvature calculated from the metric,
not used to define curvature. The old quadratic jet is now justified for
**compact interior source supports**, not for boundary-truncated cones.

The base is `7d2bd5f7be2078febc552ccb35e315418f0d9458`, containing #118 and #121.
The canonical observable remains `BoundaryDraft.conformalAction`; no Lean,
checker, dependency or build input is changed. No new integrated Lean audit,
Poisson theorem, independent human review, or complete curved-action limit is
claimed. #74 stays open for the unresolved boundary-collar handoff in §7;
#75/#76 must not silently replace that collar by full cones.

## 1. Fixed hypotheses and actual weighted component

Keep every original `AdmissibleTwoFace h f` hypothesis: the C³ face germs,
strict slope budget, compactness and joint margins, with positive-height
critical points allowed. The region M, future orientation, closed causal order
and exclusive interval endpoints are unchanged. Use signature (+---) and

```math
\begin{aligned}
q(t)&=1+t^2,&\Omega(t)&=q(t)^{1/4},&d\mu_g&=q(t)\,dt\,dz,\\
c&=\pi/24,&C&=4/\sqrt6,&K(a)&=(1-9a+8a^2-\tfrac43a^3)e^{-a}.
\end{aligned}\tag{S1}
```

Let chi be a fixed real smooth function with compact support S in the
**interior** of M. Let phi be a fixed real C⁵ function on an open neighborhood
of the closure of M. Smooth fields in the previous contracts meet this
regularity; C⁵ suffices for the five mixed derivatives used below. No new
regularity is imposed on the faces. For the short theorem alone it suffices
that phi be C⁵ near the closed short cones over S.

Choose one fixed positive delta such that all those closed cones are in M.
Indeed, S has positive Euclidean distance to the complement of M, and a
future displacement with $`v=T+r\le\delta`$ has Euclidean norm at most delta.
Shrink delta once if necessary to meet the Taylor-domain bound before (C15)
of [the pilot](curved-bulk-pilot.md#explicit-remainder-domain-and-why-taylor-alone-does-not-finish-the-proof).
Nothing depends on density. Every sufficiently small **fixed** delta works;
no uniform shrinking-cutoff conclusion is made.

For $`x=(t,z)`$, $`n\in S^2`$, put
$`T=(u+v)/2`$, $`r=(v-u)/2`$, and $`\Delta=(T,rn)`$.
The sphere measure has mass $`4\pi`$. Causal convexity and atomlessness,
as in (C1)/(A3), give the actual restricted interval law

```math
\begin{aligned}
V_M(x,x+\Delta)&=c(uv)^2\mathcal H(t,u,v),\\
\mathcal H(t,u,v)&=1+t^2+\tfrac12t(u+v)
                    +\tfrac3{40}(u+v)^2-\tfrac1{30}uv,\\
I_<^{\mathrm{actual}}(\rho,x;\phi)
 &=\int_{S^2}\int_0^\delta\int_0^v
 \frac{(v-u)^2}{8}\,q(t+T)\phi(x+\Delta)
 K(c\rho(uv)^2\mathcal H(t,u,v))\,du\,dv\,dS(n).
\end{aligned}\tag{S2}
```

This is the full actual short cone, not a coordinate approximation or a
proper-time cutoff. Define the weighted component by the canonical pair
integral with chi at the first endpoint and phi at the second:

```math
\begin{aligned}
A_{\chi,\phi}(\rho)&=S_{\chi,\phi}(\rho)+L_{\chi,\phi}(\rho),\\
S_{\chi,\phi}(\rho)&=C\sqrt\rho\int_M\chi\phi\,d\mu_g
 -C\rho^{3/2}\int_M\chi I_<^{\mathrm{actual}}\,d\mu_g.
\end{aligned}\tag{S3}
```

Here L is exactly (A2): every partner with $`v\ge\delta`$ is retained,
including partners outside a source chart. The point term is allocated once,
to short. The first-endpoint density in (S3) and the second-endpoint density
in (S2) are both present. For phi=1, this is a first-endpoint partition
component of the production action, not a replacement action definition.

## 2. An exact interpolation whose second jet is (C11)

Introduce an auxiliary parameter $`0\le\lambda\le1`$ only for the proof:

```math
\begin{aligned}
H_\lambda&=\mathcal H(t,\lambda u,\lambda v),\\
G_\lambda&=q(t+\lambda T)\phi(x+\lambda\Delta),\\
I_\lambda&=\int_{S^2}\int_0^\delta\int_0^v
 \frac{(v-u)^2}{8}G_\lambda
 K(c\rho(uv)^2H_\lambda)\,du\,dv\,dS(n),\\
I_<^{\mathrm{jet}}&=I_0+\left.\partial_\lambda I_\lambda\right|_0
                      +\tfrac12\left.\partial_\lambda^2I_\lambda\right|_0.
\end{aligned}\tag{S4}
```

The geometry, cutoff and production density have not been varied with rho;
only the integrand is interpolated. At lambda=1 this is (S2). Taylor
segments stay in the closed cones. Fixed-density differentiation is justified
on their compact parameter domain. At zero, writing $`s=uv`$ and $`q_j=q^{(j)}(t)`$,

```math
\begin{aligned}
H_\lambda&=q+\lambda q_1T/2
             +\lambda^2q_2(3T^2/20-s/60),\\
\langle G_\lambda\rangle
 &=q\phi+\lambda T(q\phi_t+q_1\phi)\\
 &\quad+\lambda^2\{q[T^2\phi_{tt}/2+(T^2-s)\Delta_z\phi/6]
                +q_1T^2\phi_t+q_2T^2\phi/2\}+O(\lambda^3).
\end{aligned}\tag{S5}
```

Brackets mean sphere **average**, so the integral still has its factor
$`4\pi`$. Multiplication with the full kernel Taylor polynomial gives exactly
(C11), including the $`K''`$ term and the mixed density/field term.
Thus (S4) defines the entire old model, at the same finite radial cutoff;
it does not select just the terms that will survive. Bounds like (C17) on the
absolute coordinate remainder do not justify the following limit.

## 3. Phase transport and the moving diagonal

For each lambda use the exact phase
$`w=uv\sqrt{H_\lambda}`$, with inverse $`u=U_\lambda(t,v,w)`$.
The positive decompositions in (A3), evaluated at lambda u and lambda v,
prove its u derivative is positive; it starts at zero and is unbounded.
Write $`\nu_\lambda(t,w)`$ for the unique solution of
$`w=\nu^2\sqrt{\mathcal H(t,\lambda\nu,\lambda\nu)}`$.
The diagonal phase is also strictly increasing: for
$`H_d=1+t^2+\lambda t v+4\lambda^2v^2/15`$,

```math
\begin{aligned}
4H_d+v\partial_vH_d
 &=4+4(t+5\lambda v/8)^2+3\lambda^2v^2/80>0.
\end{aligned}\tag{S6}
```

For each fixed x,n the exact pushed density is

```math
\begin{aligned}
a_\lambda(w,v)&=
 \frac{q(t+\lambda(U_\lambda+v)/2)
       \phi(x+\lambda((U_\lambda+v)/2,(v-U_\lambda)n/2))
       (v-U_\lambda)^2}
      {8\,\partial_u(uv\sqrt{H_\lambda})|_{u=U_\lambda}},\\
B_\lambda(w)&=\int_{\nu_\lambda(t,w)}^\delta a_\lambda(w,v)\,dv
 \quad\text{if }\nu_\lambda\lt\delta,\quad 0\text{ otherwise},\\
I_\lambda&=\int_{S^2}\int_0^\infty K(c\rho w^2)B_\lambda(w)\,dw\,dS(n).
\end{aligned}\tag{S7}
```

In particular neither the phase nor the endpoint measure is frozen at x.
All these B have a common bounded phase support and uniform bounds for x in
S, n on the sphere and lambda in [0,1]. Take a common small phase collar
$`0\lt w\lt e_0\lt\delta^2/4`$, so that
$`\nu_\lambda\le\sqrt w\lt\delta/2`$.

Here is the uniform estimate that replaces the absolute coordinate bound.
Set $`e=\lambda v`$, $`\zeta=w/v^2`$, and solve
$`\zeta=R\sqrt{\mathcal H(t,eR,e)}`$ for R near [0,1]. Then

```math
\begin{aligned}
a_\lambda(w,v)&=v\,\Psi(x,n,e,\zeta),\\
\Psi&=\frac{q(t+e(1+R)/2)
 \phi(x+e((1+R)/2,(1-R)n/2))(1-R)^2}
 {8\,\partial_R[R\sqrt{\mathcal H(t,eR,e)}]},\\
\left|\partial_\lambda^p\partial_v^k\partial_w^j a_\lambda\right|
 &\le C_{p,k,j}v^{1+p-k-2j}
 \quad(\nu_\lambda\le v\le\delta).
\end{aligned}\tag{S8}
```

The last bound is used for j=0,1,2 and p+k at most 3, only for combinations
appearing below. On the relevant compact set the inverse derivative is
bounded away from zero; the inverse and all its needed derivatives are
bounded. The fixed C⁵ field supplies every mixed derivative of Psi used
here. For example $`\partial_\lambda=v\partial_e`$ and
$`\partial_w=v^{-2}\partial_\zeta`$; a fixed-w v derivative differentiates
both e and zeta and costs at most one power of v because both are bounded.
This proves (S8), uniformly in x,n,lambda. No jet regularity is being assumed.

The implicit function theorem near w=0 gives a smooth positive d such that

```math
\begin{aligned}
\nu_\lambda(t,w)&=\sqrt w\,d(t,\lambda\sqrt w),&d(t,0)&=q(t)^{-1/4},\\
\nu_\lambda&\asymp\sqrt w,&
 |\partial_\lambda^p\nu_\lambda|&\le C_p\nu_\lambda^{p+1}
 \quad(p=1,2,3).
\end{aligned}\tag{S9}
```

Uniformity follows from compact source times and the nonzero derivative of
$`d^2\sqrt{\mathcal H(t,ed,ed)}=1`$ at e=0.
Importantly, at the moving diagonal both a and its first w derivative
vanish, because of $`(v-U_\lambda)^2`$. Consequently for w in this collar

```math
\begin{aligned}
\partial_w^jB_\lambda(w)
 &=\int_{\nu_\lambda}^\delta\partial_w^j a_\lambda(w,v)\,dv,
 \qquad j=0,1,2.
\end{aligned}\tag{S10}
```

There is no boundary of M in this calculation: it was excluded by the proved
full-cone margin, not by discarding a boundary contribution.

### All third interpolation-derivative contact terms

For $`f=\partial_w^j a_\lambda`$, put
$`r_p=\partial_\lambda^p\nu_\lambda`$. The third derivative of the moving
integral in (S10) is its integral of $`f_{\lambda\lambda\lambda}`$ minus

```math
\begin{aligned}
\mathcal C_j={}&3f_{\lambda\lambda}r_1
 +3f_{\lambda v}r_1^2+f_{vv}r_1^3
 +3f_\lambda r_2+3f_vr_1r_2+fr_3,
 \qquad v=\nu_\lambda.
\end{aligned}\tag{S11}
```

None of these terms is declared zero. From (S8)/(S9), every term in (S11)
is bounded by $`C\nu_\lambda^{5-2j}`$, whereas the remaining integrand is
bounded by $`Cv^{4-2j}`$. For j=2 these are respectively $`O(\sqrt w)`$
and an integrable constant on [0,delta]. The cases j=0,1 are stronger.
Thus, for $`Q_\lambda(w)=\partial_\lambda^3B_\lambda(w)`$,

```math
\begin{aligned}
\partial_w^jQ_\lambda(w)&\longrightarrow
 \int_0^\delta\partial_\lambda^3\partial_w^j
                         a_\lambda(0,v)\,dv,
 \qquad j=0,1,2,
\end{aligned}\tag{S12}
```

uniformly in x,n,lambda. To verify the uniform convergence, split the v
integral at a fixed positive epsilon. Above epsilon, use uniform continuity
of the mixed derivatives on a compact set. Below epsilon the integral is
at most $`C\epsilon^{5-2j}`$, and (S11) tends uniformly to zero.
Take w to zero first, then epsilon to zero. Interior mixed derivatives commute
since the field is C⁵. The three uniform limits in (S12), and the fundamental
theorem of calculus, extend Q to a right C² function with uniformly bounded
coefficients and a uniform second-derivative modulus. This is not a claim
that B itself has a right C² extension; its logarithmic terms matter.

## 4. Actual signed short remainder, including the outer integral

Define the **difference**, not the actual amplitude alone,

```math
\begin{aligned}
D_{x,n}(w)&=B_1(w)-B_0(w)
 -\left.\partial_\lambda B_\lambda(w)\right|_0
 -\tfrac12\left.\partial_\lambda^2B_\lambda(w)\right|_0\\
 &=\tfrac12\int_0^1(1-\lambda)^2Q_\lambda(w)\,d\lambda
 \quad(0\lt w\lt e_0),\\
D_{x,n}(w)&=d_0(x,n)+d_1(x,n)w+d_2(x,n)w^2+w^2E_{x,n}(w),\\
d_j(x,n)&=\frac1{2j!}\int_0^1(1-\lambda)^2\int_0^\delta
 \partial_\lambda^3\partial_w^j a_\lambda(0,v)\,dv\,d\lambda
 \quad(j=0,1,2),\\
\sup_{x\in S,n\in S^2}|E_{x,n}(w)|&\longrightarrow0.
\end{aligned}\tag{S13}
```

The coefficients and E are uniformly bounded in this collar by (S12).
They are continuous in x,n and hence measurable and integrable on the compact
source/direction domain. Globally D is bounded with a common compact phase
support. Indeed the first two lambda derivatives of B are integrals of the
corresponding derivatives of a: a and its first lambda derivative vanish
at the diagonal. Bounds (S8) with j=k=0 give bounded integrals for p=0,1,2.
At the upper corner $`\nu_\lambda=\delta`$, these integrals tend to zero,
so the zero extension remains C² in lambda. This also justifies passing
those two derivatives through the phase integral in (S7), and identifies D
with **exactly** (S4)'s actual-minus-jet integral, including moving supports.

Set $`s_\rho=\sqrt{c\rho}`$. The three signed moments
$`\int_0^\infty z^jK(z^2)\,dz=0`$ for j=0,1,2 allow subtraction of
(S13)'s polynomial on the **whole half-line**. The normalized difference is

```math
\begin{aligned}
&C\rho^{3/2}\int_0^\infty K(c\rho w^2)D_{x,n}(w)\,dw\\
&\quad=\frac C{c^{3/2}}\int_0^\infty z^2K(z^2)
 \frac{D_{x,n}(z/s_\rho)-d_0-d_1z/s_\rho-d_2(z/s_\rho)^2}
 {(z/s_\rho)^2}\,dz\longrightarrow0.
\end{aligned}\tag{S14}
```

The quotient is uniformly bounded on the whole half-line: use (S13) near
zero and the common support and bounded coefficients away from zero.
The majorant is a constant times $`z^2|K(z^2)|`$, which is integrable.
The convergence is uniform on S and the sphere. Multiply by the bounded
source density and $`|\chi|`$, integrate, and obtain the promised contract:

```text
PROVED IN WRITING CurvedInteriorShortRemainder(h, f, delta, chi, phi):
  original AdmissibleTwoFace; fixed q(t)=1+t^2
  fixed smooth chi with compact interior support S
  fixed C5 phi near the closed short cones over S
  one fixed delta>0 with all those closed cones contained in M
  actual integral (S2), entire (C11) jet (S4), original cutoff/normalization
  C*rho^(3/2) * integral_M chi * (I_actual - I_jet) dmu_g -> 0
  in fact the normalized inner difference tends to zero uniformly on S
```

This is not Lean code. The uniform signed argument, rather than a pointwise
operator limit or an absolute Taylor bound, justifies the outer integration.
It does not contradict #118: its obstructed fibres encounter the sharp
region/cutoff contact, absent from these uniformly interior full cones.

## 5. Supported response and independent curvature identification

The entire jet's normalized response was derived in (C12)–(C14) by the finite
radial primitives and logarithmic kernel moments. It is

```math
\begin{aligned}
\mathcal J\phi&=q^{-1/2}\left[
 \phi_{tt}-\Delta_z\phi+\frac{q'}{2q}\phi_t
 +\left(\frac{3q''}{4q}-\frac{9(q')^2}{16q^2}\right)\phi\right].
\end{aligned}\tag{S15}
```

That calculation also passes uniformly through the outer integral here:
its coefficients are bounded on S, q is bounded above and below, and delta
is fixed. The finite list of scaled radial responses has the same Gaussian
tail bounds uniformly for q in that compact positive interval. The powers
and logarithms in (C12), including their finite-cutoff terms, therefore give
uniform convergence to (S15). No coefficients or cutoff derivatives are
removed before this calculation. Combine this with (S14) to prove the short
response $`S_{\chi,\phi}\to\int\chi\mathcal J\phi\,d\mu_g`$.

Independently use the Levi-Civita connection of $`g=\Omega^2\eta`$ and
**exactly** (C4)'s Riemann sign:

```math
\begin{aligned}
R^a{}_{bcd}&=\partial_d\Gamma^a_{cb}-\partial_c\Gamma^a_{db}
 +\Gamma^a_{de}\Gamma^e_{cb}-\Gamma^a_{ce}\Gamma^e_{db},\\
\mathrm{Ric}_{bd}&=R^a{}_{bad},\qquad R=g^{bd}\mathrm{Ric}_{bd},\\
R&=6\Omega^{-3}\Omega''=\frac{3(1-t^2/2)}{(1+t^2)^{5/2}},\\
\Box_g\phi&=q^{-1}\partial_\mu(qg^{\mu\nu}\partial_\nu\phi)
 =q^{-1/2}\left(\phi_{tt}-\Delta_z\phi+\frac{q'}{2q}\phi_t\right),\\
\mathcal J\phi&=\Box_g\phi+\tfrac12R\phi.
\end{aligned}\tag{S16}
```

For example contraction gives
$`\mathrm{Ric}_{00}=3(\log\Omega)''`$ and
$`\mathrm{Ric}_{ij}=-[(\log\Omega)''+2((\log\Omega)')^2]\delta_{ij}`$.
The calculator `conformal_geometry.py` uses the opposite Riemann sign, so
its scalar is **minus** R here. The tests explicitly perform that conversion,
then compare the independent contraction and divergence operator with the
kernel-derived coefficient. Neither the action API nor geometric
admissibility is changed to enforce this equality.

Now apply #117/#121's `CurvedContactAveragedLong` with these endpoint weights
and this same delta. Its C² weight requirements are satisfied, including
phi on a neighborhood of the whole closure. It gives
$`L_{\chi,\phi}\to0`$, with all its contact terms already retained.
This yields the second written contract:

```text
PROVED IN WRITING CurvedSupportedBulk(h, f, delta, chi, phi):
  short hypotheses above; additionally phi is C5 near closure M
  consume CurvedContactAveragedLong from #117 / merged #121
  A_chi,phi(rho) -> integral_M chi * (Box_g phi + R*phi/2) dmu_g
  for phi=1: limit = (1/2) * integral_M chi * R dmu_g
```

The constant is the original $`C=4/\sqrt6`$, not a fitted renormalization.
For nonvacuity take the planar-future unit-ball member (C2), a nonzero
nonnegative smooth chi supported where $`|t|,|z|\lt1/64`$, and delta=1/16.
The closed short cones lie strictly inside M, and R is strictly positive
there. Its supported half-curvature integral is therefore nonzero.
The same hypotheses allow the original unequal-axis member; no condition
on the joint angle, source critical points or source level sets is added.

## 6. Derivatives and finite summation: the accepted interior output

For compact interior chi, integration by parts gives the exact derivative
accounting

```math
\begin{aligned}
\int_M\chi\Box_g\phi\,d\mu_g
 &=-\int_M g^{\mu\nu}(\partial_\mu\chi)(\partial_\nu\phi)\,d\mu_g.
\end{aligned}\tag{S17}
```

These terms need not vanish for nonconstant fields. With phi=1 they do
vanish; a first-endpoint partition by itself introduces no second-endpoint
field derivatives. Auxiliary second-endpoint fields summing to one cancel
their Box terms only after the **whole** sum, without restricting partners
to the same chart. For a finite collection of interior source supports choose
one common sufficiently small positive delta. Linearity at every finite
rho and the finite sum of (S14)/(S16) are the summable interior output for
#75/#76. This does not turn a finite family of compact interior supports
into a cover up to the boundary.

## 7. Boundary collar retained: the remaining #74/#75/#76 gate

Let $`\chi_{\mathrm{int}}`$ be a finite sum of such compact interior weights,
and let $`\chi_{\mathrm{col}}=1-\chi_{\mathrm{int}}`$ on a neighborhood
of the closure of M. Both are smooth fixed weights. The exact common split is

```math
\begin{aligned}
A_g(\rho,M)&=S_{\chi_{\mathrm{int}},1}(\rho)
 +S_{\chi_{\mathrm{col}},1}(\rho)
 +L_{\chi_{\mathrm{int}},1}(\rho)
 +L_{\chi_{\mathrm{col}},1}(\rho),\\
A_g(\rho,M)-\tfrac12\int_M\chi_{\mathrm{int}}R\,d\mu_g
 -S_{\chi_{\mathrm{col}},1}(\rho)&\longrightarrow0.
\end{aligned}\tag{S18}
```

The second line uses the proved interior theorem and **both** long terms
from #121. It leaves the actual collar short term in place, not its full-cone
surrogate. In particular it does not identify the whole bulk integral merely
because the collar has small volume. Its signed short action can carry
single-face, joint and partition/contact terms at leading order.

```text
OPEN CurvedBoundaryShortHandoff(h, f, delta, chi_col, ...):
  same original geometry, density, observable and fixed cutoff as (S18)
  derive the actual boundary-truncated short amplitudes and signed remainders
  retain the collar curvature integral, single-face/joint and partition terms
  identify what cancels only after finite summation with the #75 joint terms
  output a proved summable collar component; do not assume its limit
```

This remains under #74/#75's shared decomposition; no competing raw-fibre
long-domination problem or second production observable is introduced.
#76 may use (S18) now as a proved **partial** deterministic reduction, but
cannot invoke the separate #93 expectation equality to fill the missing
collar/joint estimate. No new issue is needed to hide that remaining obligation:
#74 stays open. A future collar identification must restore any artificially
subtracted contact layer and account for boundary fluxes absent from (S17).
No boundary or nonlocal contribution is declared zero by hypothesis.

## 8. Verification ledger

- **Conventional proof:** the interpolation identity, uniform symbol bounds,
  all moving-diagonal terms, right quadratic difference jet and signed
  outer-integrated remainder, followed by the supported response and (S18).
  Independent human mathematical review remains outstanding.
- **Symbolic checks:** `curved_interior_short.py` checks the exact interpolation,
  its entire angular second jet, scaled Jacobian, diagonal positivity and
  full third-order moving-boundary formula. Curvature/Box tests use an
  independent connection contraction with the explicit sign conversion.
- **Numerical regressions:** `test_curved_interior_short.py` evaluates the
  actual phase inverse and short integral, compares the entire finite-cutoff
  jet at multiple densities and fixed cutoffs, retains nonconstant endpoint
  fields, and integrates a compact interior source weight with the outer
  metric density. Negative controls freeze the interval phase or omit the
  target measure. None of these finite calculations proves a general limit
  or measures a claimed convergence rate.
- **Lean:** no sources, checker, dependencies or build configuration changed;
  no new Lean theorem or full integrated audit is claimed. A formal port must
  run the complete local `formal/check.sh` gate after its final relevant edit.
- **Still open:** boundary-truncated short accounting, the curved joint
  comparison, complete deterministic/expected assembly, arbitrary conformal
  factors, shrinking-cutoff interchange, rates and individual sprinklings.

```sh
.venv/bin/python -m unittest -v test_curved_interior_short
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
