# Nonpolynomial conformal short estimates and assembly (#136)

**Conventional written proof, with separate executable diagnostics; not a new
Lean theorem or independent human mathematical review.** The integration input
is `a64af01f518c859aa63417bb619022fe8b8ac4d8` on
`origin/issue-81-general-coverage`. It includes #133 / PR #143 (merge
`096cbc8`) and completed #76 / PR #135 (merge `d41a062`). This package consumes
[the actual time-only long theorem](general-metric-atlas-gate.md#3-c--nonpolynomial-conformal-branch)
and [the completed assembly interfaces](curved-assembly.md), not their older
obstruction-only predecessors. No shared geometry, action, probability or
formal definition is changed. #81/#24 remain open.

The new work is the **actual signed short remainder**, including full cones,
single-face strips and two-boundary overshoots for the nonpolynomial phase.
The polynomial identities (S6), (H9) and the truncated expression for
H-lambda in (S5) are not identities for this metric. They are replaced below.

## 1. Frozen class and independent targets

Fix a smooth member of the original `AdmissibleTwoFace h f`, with the closure
of its region contained in the open slab of absolute time less than 1/2.
The smoothness assumption here is the requested smooth subclass, not an
extension of the original compiled admissibility structure. Its strict
combined global Lipschitz budget, compact positive spatial closure and regular
joint are unchanged. Positive-height critical points, disconnected positive
regions and every joint component are retained. Write

```math
\begin{aligned}
\mathcal O&=\{z:h(z)>0\},&\Sigma&=\partial\mathcal O,&\ell&=f-h,\\
M&=\{(t,z):z\in\mathcal O,\ \ell(z)\lt t\lt f(z)\},&
J&=\{(f(z),z):z\in\Sigma\},\\
\Omega(t)&=(1-t)^{-1},&q(t)&=(1-t)^{-4},&g&=\Omega^2\eta,\\
c&=\pi/24,&C&=4/\sqrt6,&
K(Z)&=(1-9Z+8Z^2-\tfrac43Z^3)e^{-Z}.
\end{aligned}\tag{N1}
```

The metric has signature (+---), future increasing time and volume q dt dz.
Use exactly #90's Riemann sign, opposite the example calculator in #93.
Direct Levi-Civita contraction gives R = 6 Omega''/Omega cubed = 12.
The independent wave operator and target, for fixed real C5 endpoint fields
chi and phi on a neighborhood of the whole closure, are

```math
\begin{aligned}
\Box_g\phi&=(1-t)^2(\phi_{tt}-\Delta_z\phi)+2(1-t)\phi_t,\\
\mathcal B_{\chi,\phi}&=\int_M\chi(\Box_g\phi+6\phi)q\,dt\,dz,\\
p&=Df,\quad a=Dh,\quad k=|a|,\quad
b=p-(p\cdot a)a/k^2\quad(z\in\Sigma),\\
\gamma&=\frac{1-|p|^2+p\cdot a}
 {\sqrt{(1-|p|^2)(1-|p-a|^2)}},\qquad\theta=\mathrm{arcosh}\,\gamma>0,\\
dA_g&=\sqrt{q(f)}\sqrt{1-|b|^2}\,dA_\Sigma,\\
\mathcal I_{\chi,\phi}&=\int_J\chi\phi\coth\theta\,dA_g
 =\int_\Sigma\sqrt{q(f)}(\chi\phi)_f
          \frac{1-|p|^2+p\cdot a}{k}\,dA_\Sigma.
\end{aligned}\tag{N2}
```

Indeed the future unit graph normals are
`Omega(f)^(-1)*(1,p)/sqrt(1-|p|^2)` and the same formula with p-a.
Their product is gamma. Subtracting the squared denominator from the squared
numerator gives `k^2*(1-|b|^2)>0`; future orientation makes the numerator
positive. Restricting minus g to the actual lift of spatial joint tangents
gives the stated Gram determinant. Change of chart multiplies its square-root
density by the absolute coordinate determinant, so the induced measures agree
on every Borel overlap. Compactness and the strict slope/regular-height margins
make both target integrals finite. These are geometric calculations before
any action limit; conformal angle invariance alone is not a corner estimate.

Use unchanged `conformalAction`, its closed causal order and **exclusive
restricted** interval volume. For weighted notation its expansion is

```math
\begin{aligned}
V_M(x,y)&=\mu_g(M\cap(I[x,y]\setminus\{x,y\})),\\
A_{\chi,\phi}(\rho)&=C\sqrt\rho\left[
 \int_M\chi\phi\,d\mu_g-\rho\int_M\int_{M\cap J^+(x)}
 \chi(x)\phi(y)K(\rho V_M(x,y))\,d\mu_g(y)d\mu_g(x)\right].
\end{aligned}\tag{N3}
```

This is notation for the canonical integral, not a new production API. Both
endpoint measures and null relations remain. Original causal convexity proves
ambient interval containment for endpoints in M; intrinsic global hyperbolicity
alone is not used to assert it. Endpoint removal is volume-null.

## 2. Exact phase and its nonpolynomial derivative ledger

Let D be the unit rest diamond of volume c, with endpoints (-1/2,0) and
(1/2,0). Put T=(u+v)/2, r=(v-u)/2 and sigma=uv. Boosting and scaling gives
#133's exact phase (the scaling determinant is sigma squared):

```math
\begin{aligned}
L&=T/2+T\alpha+r\beta_1,\\
H(t,u,v)&=c^{-1}\int_D q(t+L)\,d\alpha\,d\beta,\\
V(x,x+(T,rn))&=c(uv)^2H(t,u,v),\\
H_\lambda(t,u,v)&=c^{-1}\int_Dq(t+\lambda L)\,d\alpha\,d\beta
 =H(t,\lambda u,\lambda v).
\end{aligned}\tag{N4}
```

For auxiliary endpoints outside M, V here is the **ambient** volume only.
Choose a compact tube inside the controlled slab and the field/face
neighborhoods, then a sufficiently small fixed positive delta so all short
auxiliary diamonds lie there. All derivatives of q are bounded there, with q
bounded positively below. Differentiation of the compact integral proves
bounds for every required mixed derivative of H, including on a slightly
enlarged ratio interval about [0,1]. Only this local inverse domain is needed.
No global polynomial positivity identity or global phase inverse is claimed.

The rest moments, obtained by integrating the transverse ball sections, are

```math
\begin{aligned}
\langle L\rangle_D&=T/2,&
\langle L^2\rangle_D&=3T^2/10-\sigma/30,&
\langle L^3\rangle_D&=T^3/5-T\sigma/20,\\
H_\lambda&=q+\lambda q'T/2
 +\lambda^2q''(3T^2/20-\sigma/60)+\mathcal R_\lambda,\\
\mathcal R_\lambda&=\frac{\lambda^3}{2c}
 \int_D L^3\int_0^1(1-s)^2q'''(t+s\lambda L)\,ds\,d\alpha\,d\beta.
\end{aligned}\tag{N5}
```

For this q, `q'''(t)=120*(1-t)^(-7)`, so the displayed remainder is generally
nonzero. In particular the cubic diagonal coefficient is q'''/40. Formula
(N5) identifies the second jet but does **not** estimate the normalized
coordinate Taylor error. That estimate is proved using phase transport next.

A useful independent exact diagnostic formula follows by first integrating
beta_1 over the transverse disks. With A=1-t, B=A-T, y=uv/(4AB),

```math
\begin{aligned}
H&=32\int_0^{1/2}s^3\left[
 \frac1{(A-us)^2(A-vs)^2}+\frac1{(B+us)^2(B+vs)^2}\right]ds\\
 &=\frac{S(y)}{A^2B^2},\qquad
 S(y)=\frac{2}{y^2}\left[\log(1+y)-\frac{y}{1+y}\right],\quad S(0)=1,\\
S(y)&=2\sum_{j=0}^{\infty}(-1)^j\frac{j+1}{j+2}y^j\quad(|y|\lt1).
\end{aligned}\tag{N6}
```

For the first equality use radius `s=1/2-|alpha|` and
`integral_{-s}^s (s^2-b^2)/(a-r*b)^4 db = 4*s^3/(3*(a^2-r^2*s^2)^2)`.
For the second equality substitute x=s/A and x=-s/B in the two terms.
An antiderivative of `x^3/((1-u*x)^2*(1-v*x)^2)` has log coefficients
`(3*u-v)/(u^2*(u-v)^3)` and `(u-3*v)/(v^2*(u-v)^3)` and rational part
`1/(u^2*(u-v)^2*(1-u*x))+1/(v^2*(u-v)^2*(1-v*x))`.
The two endpoint log products both equal 1+y; their coefficients sum to
`1/(u*v)^2`. The rational endpoint difference is
`-y/((u*v)^2*(1+y))`, proving (N6). Coincident u,v and null u=0 follow by
continuity. The series follows by subtracting the logarithm and geometric
series; the tail after degree m is
at most `2*abs(y)^(m+1)/(1-abs(y))`. The proof below uses (N4), not truncation
of this series. (N6) is useful for stable independent finite quadrature.

## 3. Actual full-cone signed primitive remainder

For each source x in the **whole compact closure**, not just an interior
support, define I-lambda by the full short cone integral with Jacobian
`(v-u)^2/8`, target density `q(t+lambda*T)`, target field `phi(x+lambda*(T,rn))`
and kernel `K(c*rho*(uv)^2*H_lambda)`. The point term belongs only to short.
Define I-jet as its value plus first and half second lambda derivatives at
zero. Fixed-density differentiation is legitimate on this compact domain.
At lambda=1 the auxiliary cone is exact; §5 restores the nonphysical partners.

Set e=lambda v and R=u/v. The ratio phase is
`Phi(t,e,R)=R*sqrt(H(t,e*R,e))`. At e=0 its R derivative is sqrt(q(t)).
Compact continuity gives a common positive lower bound for Phi_R, also on
the enlarged ratio interval. Its inverse R=U(t,e,zeta), zeta=w/v squared,
has all required bounded derivatives by implicit differentiation. Thus the
**actual**, not frozen, pushed amplitude is

```math
\begin{aligned}
a_\lambda(w,v)&=v\Psi(x,n,e,w/v^2),\\
\Psi&=\left.\frac{(1-R)^2q(t+e(1+R)/2)
 \phi(x+e((1+R)/2,(1-R)n/2))}{8\Phi_R}\right|_{R=U},\\
|\partial_\lambda^p\partial_v^k\partial_w^j a_\lambda|
 &\le C_{p,k,j}v^{1+p-k-2j}.
\end{aligned}\tag{N7}
```

Here j=0,1,2 and the combinations with p+k at most three used below are
bounded; the largest field derivative order is five. The q derivatives
needed for the phase denominator also exist. The bound follows directly from
`partial_lambda=v*partial_e`, `partial_w=v^(-2)*partial_zeta`; a fixed-w v
derivative costs one power since e and zeta stay in compact sets. This
supplies the actual nonpolynomial symbol estimate, not merely smoothness of
an unscaled coordinate amplitude.

The diagonal is now the integral equation

```math
\begin{aligned}
w&=\nu_\lambda^2\sqrt{H(t,\lambda\nu_\lambda,\lambda\nu_\lambda)},\\
H(t,e,e)&=q+q'e/2+2q''e^2/15+q'''e^3/40+O(e^4),\\
\nu_\lambda&=\sqrt w\,d(t,\lambda\sqrt w),\quad d(t,0)=q(t)^{-1/4},\\
\nu_\lambda&\asymp\sqrt w,\qquad
|\partial_\lambda^p\nu_\lambda|\le C_p\nu_\lambda^{p+1}
 \quad(p=1,2,3).
\end{aligned}\tag{N8}
```

Its derivative is positive for the chosen small fixed cutoff: it is v times
`2*sqrt(q(t))+O(v)`, uniformly. The smooth positive function d follows from
the implicit equation `d^2*sqrt(H(t,e*d,e*d))=1`. This replaces (S6); it is
not its polynomial formula with coefficients renamed.

Write `B_lambda(w)=integral_{nu_lambda}^delta a_lambda(w,v) dv`, zero when the
lower endpoint exceeds delta. The factor (1-U) squared makes both a and a_w
zero on the true diagonal, so the first two w derivatives of B are the
integrals of the corresponding derivatives of a. Put f=a differentiated j
times in w, and r_p=partial_lambda^p nu. Its third lambda derivative is

```math
\begin{aligned}
\partial_\lambda^3\int_\nu^\delta f\,dv
 &=\int_\nu^\delta f_{\lambda\lambda\lambda}\,dv-\mathcal C_j,\\
\mathcal C_j&=3f_{\lambda\lambda}r_1+3f_{\lambda v}r_1^2
 +f_{vv}r_1^3+3f_\lambda r_2+3f_vr_1r_2+fr_3,\\
|\mathcal C_j|&\le C\nu^{5-2j},\qquad
|f_{\lambda\lambda\lambda}|\le Cv^{4-2j}.
\end{aligned}\tag{N9}
```

All six contact terms are retained. For j=2 the interior bound is integrable
and the boundary bound tends to zero. Splitting v at a fixed positive
number, uniform continuity above it and the bound below it show uniform
right limits of `partial_w^j partial_lambda^3 B_lambda`, for j=0,1,2. The
fundamental theorem of calculus therefore supplies a right quadratic Peano
jet for the **difference**

```math
\begin{aligned}
D(w)&=B_1-B_0-\partial_\lambda B_0-\tfrac12\partial_\lambda^2B_0
 =\tfrac12\int_0^1(1-\lambda)^2\partial_\lambda^3B_\lambda(w)\,d\lambda,\\
D(w)&=d_0+d_1w+d_2w^2+w^2E(w),\qquad\sup|E(w)|\longrightarrow0,\\
d_j&=\frac1{2j!}\int_0^1(1-\lambda)^2\int_0^\delta
 \partial_\lambda^3\partial_w^j a_\lambda(0,v)\,dv\,d\lambda.
\end{aligned}\tag{N10}
```

Uniformity is over the compact source, direction and interpolation variables.
It is not a claim that B itself is C2 at zero; B's logarithms matter.
At the cutoff corner nu=delta the amplitude and its first lambda variation
vanish. Hence the zero extension has the needed first two lambda derivatives,
with common bounded phase support, and differentiation under the phase integral
identifies (N10) with the exact I-actual minus I-jet. All coefficients are
bounded and measurable. Subtract their polynomial on the whole half-line.
Using the three signed moments gives

```math
\begin{aligned}
\int_0^\infty z^jK(z^2)\,dz&=0\quad(j=0,1,2),\\
C\rho^{3/2}\int_0^\infty K(c\rho w^2)D(w)\,dw&\longrightarrow0.
\end{aligned}\tag{N11}
```

Indeed after `z=sqrt(c*rho)*w` the remaining integrand is bounded by a constant
times `z^2*abs(K(z^2))`. The quotient `(D-d0-d1*w-d2*w^2)/w^2` is bounded
near zero by (N10) and away from zero by bounded support and coefficients.
Dominated convergence is uniform in the remaining parameters and survives
the outer integral with bounded chi and the **source** density q. This proves
the actual full-cone signed remainder on the whole collar as well as inside.

## 4. Entire second jet and the bulk coefficient

Let Z=c rho q sigma squared; phi and its derivatives below are at x. From
(N5), angular averaging gives the following complete degree-zero/two jet:

```math
\begin{aligned}
g_0&=q\phi,\qquad g_1=T(q\phi_t+q'\phi),\\
g_2&=q\{T^2\phi_{tt}/2+(T^2-\sigma)\Delta_z\phi/6\}
       +q'T^2\phi_t+q''T^2\phi/2,\\
z_1&=Zq'T/(2q),\qquad z_2=Zq''(3T^2/20-\sigma/60)/q,\\
\langle\mathrm{jet}\rangle
 &=g_0K+(g_1K+g_0z_1K')
   +(g_2K+(g_1z_1+g_0z_2)K'+g_0z_1^2K''/2).
\end{aligned}\tag{N12}
```

Both interval second-jet terms, both endpoint measures and the K-double-prime
term are present. Only the **generic radial identities** of #74 are reused:

```math
\begin{aligned}
J_0&=(\delta^2-\sigma^2/\delta^2)/8+\sigma\log(\sigma/\delta^2)/4,\\
J_1&=(\delta-\sigma/\delta)^3/24,\\
J_2&=(\delta^4-\sigma^4/\delta^4)/64
             +\sigma^2\log(\sigma/\delta^2)/16,\\
\int_0^\infty z^jK(z^2)\,dz
 &=-j(j-1)(j-2)\Gamma((j+1)/2)/12.
\end{aligned}\tag{N13}
```

They follow by integrating `(v-sigma/v)^2/(4v)` times 1,T,T squared,
respectively, between sqrt(sigma) and delta. The pair Jacobian is half of
this radial measure; sphere integration therefore gives the factor 2 pi.
Differentiating the last identity at j=1,2 gives 1/12 and minus sqrt(pi)/12.
After including the point term, the first logarithm cancels that term;
polynomial moments vanish, and the critical logarithms in (N12) give

```math
\begin{aligned}
\mathcal J\phi&=q^{-1/2}\left[\phi_{tt}-\Delta_z\phi
 +\frac{q'}{2q}\phi_t+
 \left(\frac{3q''}{4q}-\frac{9(q')^2}{16q^2}\right)\phi\right]\\
 &=(1-t)^2(\phi_{tt}-\Delta_z\phi)+2(1-t)\phi_t+6\phi.
\end{aligned}\tag{N14}
```

For the K, Z K-prime and Z-squared K-double-prime critical responses the
multipliers are 1, -3/2 and 15/4, obtained by integration by parts of the same
log moment. All finite-cutoff powers in (N13) remain until their limits;
Gaussian tails are uniform for q in its compact positive range. Equations
(N11)-(N14) prove `S_full -> B_chi,phi`, with B independently defined in (N2).
A local curvature calculation without (N7)-(N11) would not establish this.

## 5. Actual single-face estimate, including its moving strip

Set A=f(z)-t and `d=T+f(z)-f(z+rn)`. The strict upper envelope gives
`(1-eta)*T <= d <= v`. The lower envelope already admits every future target;
the actual upper test is A>d. For the **actual weighted kernel** W, including
q(f-A)q(f-A+T), chi, phi and H(f-A,u,v), use the exact identity

```math
\begin{aligned}
\mathbf1_{d\lt h}\int_d^h W(A)\,dA
 &=\int_0^hW(A)\,dA-\int_0^dW(A)\,dA
      +\mathbf1_{h\lt d}\int_h^dW(A)\,dA,\\
S&=S^{\mathrm{full}}+C\rho^{3/2}F-C\rho^{3/2}J_c.
\end{aligned}\tag{N15}
```

This restores every auxiliary partner exactly, including contact h=d. F is
the whole future-face strip; J_c is the true two-boundary overshoot supported
where `0<h<d<=delta`. There is no deletion by chart membership or by small
collar volume.

Flatten F with A=b d, b in [0,1], R=u/v and D=d/v. Taylor's integral formula
for the smooth future face yields

```math
\begin{aligned}
D&=D_0+vD_1+O_{C^3_R}(v^2),\\
D_0&=(1+R)/2-(1-R)Df[n]/2,\qquad
D_1=-(1-R)^2D^2f[n,n]/8,\\
t&=f-bvD,\qquad\Phi=R\sqrt{H(t,vR,v)},\\
\partial_uw&=\frac{v[2H+u(H_u-bd_uH_t)]}{2\sqrt H},\qquad
 d_u=(1+Df(z+rn)[n])/2.
\end{aligned}\tag{N16}
```

The moving-source-time term is essential. The ratio phase has a uniform
positive derivative by (N4) and its limit sqrt(q(f)). Implicit differentiation
and the compact derivative bounds give, after phase transport,

```math
\begin{aligned}
a^F(w,v)&=v^2\Psi(v,w/v^2),\\
\Psi&=\left.\frac{D(1-R)^2q(t)q(t+v(1+R)/2)
 \chi(t,z)\phi(t+v(1+R)/2,z+v(1-R)n/2)}{8\Phi_R}\right|_{R=U},\\
\Psi&=\psi_0+v\psi_1+E,\qquad
|\partial_\zeta^jE|\le Cv^2\ (j=0,1,2),\quad |E_v|\le Cv.
\end{aligned}\tag{N17}
```

For explicit justification, all mixed derivatives through two v and two zeta
derivatives of this inverse/composition are bounded; the denominator uses
one additional ratio derivative of the smooth phase. Integral Taylor in v
then gives these bounds. Five field derivatives suffice; geometry and q are
smooth. We do not assume the clipped integral has a jet.

At R=1, d=v. The correct diagonal, not (H9), is

```math
\begin{aligned}
w&=\nu^2\sqrt{H(f-b\nu,\nu,\nu)},\qquad
\nu_0=\sqrt w\,q(f)^{-1/4},\\
H(f-bv,v,v)&=q+q'(1/2-b)v
 +q''(b^2/2-b/2+2/15)v^2+O(v^3),\\
\nu&\asymp\sqrt w,\qquad |\nu-\nu_0|\le Cw.
\end{aligned}\tag{N18}
```

The nonzero higher derivatives are controlled by (N4); diagonal positivity
again follows from `v*(2*sqrt(q(f))+O(v))`. To identify the physical face jet,
replace v by e=lambda v in D, H and the field displacements, but keep the
physical depth factor vD. Its value and first derivative at lambda=0 give
exactly the displacement-degree-one/two face terms. The lower endpoint's
first variation is zero because (1-U) squared vanishes there. Thus their
pushed density is `v^2*psi0+v^3*psi1` with reference lower limit nu0.
The **exact** difference, on a common small phase collar, is

```math
\begin{aligned}
B^F-B^{F,\mathrm{jet}}&=\int_{\nu_0}^\delta e(w,v)\,dv
 +\int_\nu^{\nu_0}a^F(w,v)\,dv,\qquad e=v^2E(v,w/v^2),\\
|\partial_w^je|&\le Cv^{4-2j}\ (j=0,1,2),\quad |e_v|\le Cv^3,\\
\left|\int_\nu^{\nu_0}a^F\,dv\right|&\le Cw^3,\\
\left(\int_{\nu_0}^\delta e\,dv\right)''
 &=\int_{\nu_0}^\delta e_{ww}\,dv-2e_w(\nu_0)\nu_0'
       -e_v(\nu_0)(\nu_0')^2-e(\nu_0)\nu_0''.
\end{aligned}\tag{N19}
```

The oriented strip is retained: its length is O(w), v is comparable to
sqrt(w), and (1-U) squared is O(w), giving the displayed bound. A local
continuation just beyond U=1 cancels in this identity, not a physical partner
addition. Each boundary term in the last line is O(sqrt(w)); e_ww has an
integrable constant majorant. The same split-and-continuity argument as §3
proves a uniform right quadratic Peano jet for the first integral. The strip
is o(w squared). Both densities have common bounded support, including the
cutoff contact; (N11)'s signed argument proves
`C*rho^(3/2)*(F-F_jet) -> 0` uniformly before compact parameter integration.

All fields in the next formula are evaluated at (f(z),z). Angular averaging
and depth integration give the entire face jet, with Z=c rho q(uv) squared:

```math
\begin{aligned}
\langle W^{F,\mathrm{jet}}\rangle
 &=a_1TK(Z)+a_2T^2K(Z)+a_3r^2K(Z)+a_4r^2ZK'(Z),\\
a_1&=q^2\chi\phi,\quad a_2=q^2(\chi\phi_t-\chi_t\phi)/2,\\
a_3&=-q^2\{\chi\phi\Delta f/6+|p|^2(\chi_t\phi+\chi\phi_t)/6
                         +\chi p\cdot\nabla\phi/3\}
                         -qq'\chi\phi|p|^2/3,\\
a_4&=-qq'\chi\phi|p|^2/6,\\
(TK,T^2K,r^2K,r^2ZK')&\longmapsto q^{-3/2}(0,-2,6,-9).
\end{aligned}\tag{N20}
```

These formulas are generic **jet algebra**, not an imported polynomial
remainder theorem: the endpoint density correction is qq'(T-2A), the phase
correction is `(q'/q)*Z*(T/2-A)`, and the gap terms are
`T-r*Df[n]-r^2*D2f[n,n]/2`. Their integrals give (N20), and (N13) gives its
responses with positive C rho-to-three-halves normalization. K-double-prime
first contributes at degree three here and is in the proved remainder, not
deleted by assertion. Define

```math
\begin{aligned}
N_k&=\partial_t+Dk\cdot\nabla_z,\qquad\nu_{\mathcal O}=-a/k,\\
\mathcal N_{\chi,\phi}&=\int_{\mathcal O}\sqrt{q(f)}
             (\phi N_f\chi-\chi N_f\phi)_f\,dz,\\
\mathcal T_{\chi,\phi}&=\int_\Sigma\sqrt{q(f)}(\chi\phi)_f
                                      Df\cdot\nu_{\mathcal O}\,dA_\Sigma,\\
C\rho^{3/2}F&\longrightarrow\mathcal N_{\chi,\phi}-\mathcal T_{\chi,\phi}.
\end{aligned}\tag{N21}
```

The density in (N20) is that of N minus
`div_z(sqrt(q(f))*chi_f*phi_f*Df)`, including total derivatives of both
traces and q(f). Apply spatial divergence on every component. For unit
fields this response is **minus T**, generally not zero.

## 6. Actual corner signed comparison and independent joint

Use finite smooth height charts z=Z_i(y,s), h(Z_i)=s, with subordinate
weights sigma_i summing to one on the whole regular collar. Put
`G_i(y,s)=sigma_i(Z_i)*abs(det DZ_i)`; at s=0,
`G_i dy = sigma_i/k dA_Sigma`. The target endpoint is unrestricted by the
chart label. For beta,lambda in [0,1], set

```math
\begin{aligned}
s&=\beta d(Z_i(y,s),u,v,n),\qquad
A=d[\beta+(1-\beta)\lambda]=\alpha d,\\
d_s&=[Df(Z_i)-Df(Z_i+rn)]\cdot Z_{i,s}=O(v),\\
\left|\frac{\partial(s,A)}{\partial(\beta,\lambda)}\right|
 &=\frac{(1-\beta)d^2}{1-\beta d_s}.
\end{aligned}\tag{N22}
```

Choose delta once so |d_s|<1/2 and the whole overshoot lies in these charts.
The root is unique, by strict increase of s-beta d; it parametrizes the
entire interval 0<s<d. Then lambda covers s<A<d exactly. This is the actual
two-boundary domain, not a positive-part Taylor model.

With R=u/v, D=d/v, z0=Z_i(y,0), t=f(Z_i(y,s))-alpha vD, the ratio phase is
`Phi=R*sqrt(H(t,vR,v))`. Implicit differentiation of the height root gives
`s_R=O(v)`, `s_RR=O(v^2)`, `s_RRR=O(v^3)`. Smooth Taylor bounds and (N4) yield

```math
\begin{aligned}
\|D-D_0\|_{C^3_R}+\|t-f(z_0)\|_{C^3_R}
 +\|\Phi-R\sqrt{q(f(z_0))}\|_{C^3_R}&\le Cv,\\
\|d_s\|_{C^2_R}+\|G_i(y,s)-G_i(y,0)\|_{C^2_R}&\le Cv,\\
a^J(w,v)&=v^3\Psi(v,w/v^2),\\
\Psi&=\left.\frac{(1-\beta)D^2(1-R)^2G_i(y,s)q(t)q(t+v(1+R)/2)}
 {8(1-\beta d_s)\Phi_R}\chi(t,Z_i)\phi(t+v(1+R)/2,Z_i+v(1-R)n/2)
 \right|_{R=U},\\
\Psi&=\Psi_0+E,\qquad |\partial_\zeta^jE|\le Cv\ (j=0,1,2),
 \quad |E_v|\le C.
\end{aligned}\tag{N23}
```

Here D0 is (N16) at z0 and Psi0 sets v=0 in this formula. The inverse exists
by the same positive derivative margin. Its three ratio derivatives suffice
for two derivatives of the reciprocal phase derivative; compact mixed bounds
and integral Taylor in v prove the last line. In particular Phi_R differentiates
**all** of the moving t, including s_R and A_R. Chart, partition and field
derivatives occur in E and are not assumed zero.

On the true diagonal, d=v, s=beta v, A=alpha v. Therefore

```math
\begin{aligned}
w&=\nu^2\sqrt{H(f(Z_i(y,\beta\nu))-\alpha\nu,\nu,\nu)},\qquad
\nu_0=\sqrt w\,q(f(z_0))^{-1/4},\\
|\nu-\nu_0|&\le Cw,\qquad\nu\asymp\sqrt w,\\
B^J-B^{J,\mathrm{tan}}&=\int_{\nu_0}^\delta v^3E(v,w/v^2)\,dv
                         +\int_\nu^{\nu_0}a^J(w,v)\,dv,\\
|\partial_w^j(v^3E)|&\le Cv^{4-2j},\quad
|\partial_v(v^3E)|\le Cv^3,\qquad
\left|\int_\nu^{\nu_0}a^J\,dv\right|\le Cw^{7/2}.
\end{aligned}\tag{N24}
```

The strip length and quadratic diagonal zero give the last bound. The three
boundary terms in (N19), now with e=v cubed E, are again O(sqrt(w)). Thus the
same explicit derivative argument gives a uniform quadratic Peano difference
jet, with coefficients `(1/j!)*integral_0^delta partial_w^j e(0,v) dv`.
The signed moment argument (N11), after the finite chart/depth integrations,
proves `C*rho^(3/2)*(J_c-J_tan) -> 0`. This is the actual corner estimate;
no flat global action theorem or raw first-endpoint dominator is invoked.

Integrating beta,lambda gives 1/2, and summing G_i(y,0) gives dA/k. The now
justified tangent model and its response are

```math
\begin{aligned}
J_{\mathrm{tan}}&=\int_\Sigma\frac{q(f)^2(\chi\phi)_f}{2k}
 \int_{S^2}\int_0^\delta\int_0^v\frac{(v-u)^2}{8}
 (T-rp\cdot n)^2K(c\rho q(f)(uv)^2)\,du\,dv\,dS(n)\,dA_\Sigma,\\
-C\rho^{3/2}J_c&\longrightarrow
 \int_\Sigma\sqrt{q(f)}(\chi\phi)_f\frac{1-|p|^2}{k}\,dA_\Sigma,\\
\mathcal Q&=-C\rho^{3/2}J_c-\mathcal T_{\chi,\phi}
                  \longrightarrow\mathcal I_{\chi,\phi}.
\end{aligned}\tag{N25}
```

Sphere averaging gives T squared plus |p| squared r squared /3; the two
responses in (N20) give the second line. Since
`T_flux=-integral_Sigma sqrt(q(f))*chi_f*phi_f*(p dot a)/k dA`, the last line
is exactly the independent normal/area target (N2). The raw corner alone
omits p dot a. Curvature in the whole collar remains in B, not in a discarded
small-volume error.

## 7. Deterministic theorem, complete partitions and expectation

Choose one fixed delta meeting the finitely many derived smallness bounds
above. #133's time-only contact-averaged long theorem applies to exactly H
in (N4), this delta and these C5 fields (it needs only C2 fields). It retains
the moving time boundary and the v-contact triangle, both measures and every
partner, and proves L -> 0. It does not assert a raw-time dominator or uniform
little-o at cutoff contacts. By (N15) there is the exact residual identity

```math
\begin{aligned}
A_{\chi,\phi}-\mathcal B_{\chi,\phi}-\mathcal N_{\chi,\phi}
             -\mathcal I_{\chi,\phi}
 &=(S^{\mathrm{full}}-\mathcal B_{\chi,\phi})
 +(C\rho^{3/2}F-\mathcal N_{\chi,\phi}+\mathcal T_{\chi,\phi})\\
 &\quad+(-C\rho^{3/2}J_c-\mathcal T_{\chi,\phi}
                   -\mathcal I_{\chi,\phi})+L\longrightarrow0.
\end{aligned}\tag{N26}
```

This is the **complete conventional deterministic theorem**. With unit fields
N and Box(1) vanish, but T has already been retained and restored, not assumed
zero. For clarity, if the bulk is integrated by parts, both oriented
spacetime-face fluxes remain:

```math
\begin{aligned}
\int_M\chi\Box_g\phi\,d\mu_g
 &=-\int_M g^{\mu\nu}\partial_\mu\chi\partial_\nu\phi\,d\mu_g
 +\int_{\mathcal O}\sqrt{q(f)}(\chi N_f\phi)_f\,dz
 -\int_{\mathcal O}\sqrt{q(\ell)}(\chi N_\ell\phi)_\ell\,dz.
\end{aligned}\tag{N27}
```

There is no lateral face integral since its time interval has zero length.
For finite smooth source and target partitions summing to one on a neighborhood
of the whole auxiliary tube, sum **all ordered pairs** of labels. Finite
linearity holds for every term in (N15), including the point allocation
`sum_i,j chi_i(x)*phi_j(x)=1`. The errors above are uniformly bounded over a
finite family, so one common delta works. Box/field/partition derivatives
cancel only after these full sums. Off-diagonal chart pairs, non-null overlaps,
all components and the complement of the regular collar are retained. No
isolated-chart action or finite collection of interior supports replaces M.
The target is independent of the chosen permitted fixed cutoff and auxiliary
extension; no density-dependent cutoff is taken.

Only now apply #93. Define Omega globally by (1-t) inverse on the open slab
of absolute time less than 1/2, and one off it. It is Borel measurable;
smoothness outside the controlled neighborhood is not required. On that open
slab it is smooth of all orders and lies between 2/3 and 2. The closure of M
is contained there by hypothesis. These discharge **every field** of
`ControlledConformalFactor`. Original admissibility supplies bounded Borel M
and ambient causal convexity. The checked API then supplies finite atomless
restricted volume, measurable actual interval volume and kernel, integrability
of the signed pair and discrete action, the constructed finite Poisson
probability law and its supported, duplicate-free finite causal orders.
Extension independence is the existing `conformalAction_congr` and
`conformalProbability_congr`; no flat interval formula is substituted.

For every positive rho, the universal
`AdmissibleTwoFace.conformal_expectedAction_eq` therefore applies to this same
instance. Its law and discrete observable, independently of the limit, are

```math
\begin{aligned}
\Pi_{\rho,g,M}&=\mathrm{FinitePoisson.law}(\rho\mu_g|_M),\\
A_\rho^{\mathrm{disc}}&=\frac4{\sqrt6\sqrt\rho}
       [N-N_0+9N_1-16N_2+8N_3],\\
\mathbb E_{\Pi_{\rho,g,M}}[A_\rho^{\mathrm{disc}}]&=A_g(\rho,M),\\
\lim_{\rho\to\infty}A_g(\rho,M)
 &=\lim_{\rho\to\infty}\mathbb E_{\Pi_{\rho,g,M}}[A_\rho^{\mathrm{disc}}]
 =6\mu_g(M)+\int_J\coth\theta\,dA_g.
\end{aligned}\tag{N28}
```

N_k counts ordered distinct pairs and exactly k other points in the closed
interval. Mecke's pair density is rho squared, and kernel coefficients are
`(1,-9,16,-8)` with factorial denominators. Equality on the positive-density
tail transfers the already proved deterministic limit; there is no exchange
of expectation with a random limit. Empty regions give zero throughout.
This is a **written application** of the checked finite-density theorem, not
a newly compiled instance or a compiled curved limit.

## 8. Nonvacuous examples and verification ledger

For #133's exact unequal-axis member use

```math
\begin{aligned}
h(z)&=\tfrac14(1-z_1^2-z_2^2/4-z_3^2/9),\qquad f=1/8,\\
\mathcal B&=48\pi\int_{-1/8}^{1/8}
                (1/2+4t)^{3/2}(1-t)^{-4}\,dt>0,\\
\mathcal I&=48\pi(1-1/8)^{-2}=3072\pi/49.
\end{aligned}\tag{N29}
```

Its positive-part height has global Lipschitz constant 1/2 and its regular
joint gradient ranges from 1/6 to 1/2. Joint angle weights at the first and
third axis tips are 2 and 6. The bulk is six times the metric volume, not a
fitted coefficient. The future profile `f=1/8+epsilon*sin(z1)`, for
`0<epsilon<=1/16`, is a second included member: its combined budget is at most
9/16, time closure lies within [-3/16,3/16], and its future face is nonplanar.
Its T flux is nonzero: on the joint its density is proportional to
`x*cos(x)/(1-1/8-epsilon*sin(x))^2`; pairing x and -x gives a strictly positive
integral. Thus it detects omission of the compensating flux, not just area
scaling in a planar example.

| Acceptance | Evidence | Verification boundary |
| --- | --- | --- |
| Actual nonpolynomial signed primitive | (N4)-(N11), nonzero cubic remainder and all six contacts | Written proof, not smoothness alone |
| Entire interval/density jet and independent R | (N12)-(N14), direct metric contraction | No target-valued admissibility |
| Actual face/corner, moving strips, all fluxes | (N15)-(N25), (N27) | No polynomial S6/H9 transplant |
| Matched deterministic then expected theorem | (N26), then (N28) with all controlled-factor fields discharged | Existing checked finite-density bridge only |
| Whole collar, partitions and examples | §§7-8, actual weighted diagnostics | No same-chart restriction or fitted limit |

`nonpolynomial_short.py` and `test_nonpolynomial_short.py` supply finite symbolic
and numerical checks: independent rest-diamond/section phase, nonzero higher
jets, original versus transported integrals, physical second jets, nonconstant
fields, moving boundary Jacobians, both endpoint measures, full/short/long and
full/face/corner restoration, complete signed partitions, independent induced
geometry and retained flux, and flat/nonunit constant calibrations. Numerical
refinement is evidence, not a certified error bound or a convergence proof.

No Lean source, checker, dependency or build input is changed; no fresh formal
audit is claimed or required for this documentation/Python package. A future
formal port must first freeze bounded producers for (N7)-(N11), (N16)-(N24),
induced joint geometry, and #133's long contact argument, before composing them
with the existing finite-density bridge and running the final integrated local
audit. Those are future proof obligations, not compiled declarations here.
Independent human mathematical review remains outstanding. No general metric,
spatially varying factor, noncompact tail, degenerating-angle uniformity, rate,
shrinking-cutoff or sample-wise result is asserted.

```sh
.venv/bin/python -m unittest -v test_nonpolynomial_short
.venv/bin/python nonpolynomial_short.py
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
