# Sphere-dependent conformal factors with retained focusing (#81)

**Conventional written theorem, not a Lean result or independent acceptance.**
This removes the sphere-independence restriction in RC1 of
[the integrated #165 proof](curved4-corrected-convergence.md). It changes no
predecessor statement, proof, certificate or historical receipt. In particular,
[#164's complete-action obstruction](curved4-complete-action-obstruction.md)
and its model-only certificate remain unchanged. Its published independent AI
audit is supporting evidence, not human acceptance or formal certification.

The [geometric continuation](geometric-long-cancellation.md) goes beyond this
family, including a nonempty-joint application and the remaining #81 matrix.
Neither note completes #81/#24. Final human scrutiny remains #94/#86.

## 1. Metric, actual order and independently calculated target

Let Omega be any fixed smooth strictly positive function on
`R x S²_1 x (R/20Z)`. No symmetry, smallness, polynomiality or analyticity is
required. On the same ambient product and width-four slab set

```math
\begin{aligned}
M&=(-2,2)\times S^2_1\times(\mathbb R/20\mathbb Z),\\
g_0&=dt^2-h_{S^2}-dz^2,&g&=\Omega(t,p,z)^2g_0,&\omega&=\Omega^4,\\
R_g&=2\Omega^{-2}+6\Omega^{-3}
 (\Omega_{tt}-\Omega_{zz}-\Delta_{S^2}\Omega),\\
\mathcal T_g&=\frac12\int_M R_g\,d\mu_g
 =\int_{-2}^{2}\int_0^{20}\int_{S^2}
 [\Omega^2+3\Omega(\Omega_{tt}-\Omega_{zz}-\Delta_{S^2}\Omega)]\,dA\,dz\,dt,\\
\lim_{\rho\to\infty}\mathcal A_{\rho,4}(M,g)
 &=\mathcal T_g,&
\lim_{\rho\to\infty}\mathbb E_{\rho\mu_g}A^{\mathrm{disc}}_{\rho,4}
 &=\mathcal T_g.
\end{aligned}\tag{SW1}
```

The Laplacian has `Delta p_i=-2 p_i`; the Riemann sign is exactly the general
contract's. Contract the product curvature first, then apply the conformal
scalar formula. The sphere derivative term cannot be omitted. This calculation
does not use any action coefficient. For example, for `Omega=1+epsilon*p_3`,
with `abs(epsilon)<1`, sphere integration gives

```math
\begin{aligned}
\mathcal T_g&=320\pi(1+7\epsilon^2/3),\\
\mu_g(M)&=320\pi(1+2\epsilon^2+\epsilon^4/5).
\end{aligned}\tag{SW2}
```

The causal order is still `tau >= sqrt(theta²+b²)`, where theta is round
sphere distance and b shortest signed circle displacement. Every causal
circle lift, including the entire interval, is unique since `tau<4<10`.
Positive conformal change preserves this order, global hyperbolicity and the
two spacelike compact Cauchy faces. Monotonicity of time separately proves
ambient interval containment. The joint is empty. The Weyl square is
`4/(3*Omega^4)`, so this is not a conformally flat pilot. Antipodal focusing
remains; it is not removed as a measure-zero inconvenience.

## 2. Exact volume and both-measure pushforward without rotational averaging

Retain an oriented endpoint frame `(p,n)` on the unit tangent bundle of the
sphere; put `k=p cross n` and `q_theta=cos(theta)*p+sin(theta)*n`. Its measure
is `dA(p) dphi(n)`, of total mass `8*pi²`. It is **not** permissible to replace
an integrand depending on this frame by its value in one chosen frame.
For a physical intermediate sphere point Y put
`r_1=d(p,Y)`, `r_2=d(Y,q_theta)`. The actual interval is

```math
\begin{aligned}
V_g(s,p,z;\tau,q_\theta,b)
 &=\int_{S^2}\int_{\mathbb R}
 \mathbf1_{\{d_1+d_2\lt\tau\}}
 \int_{d_1}^{\tau-d_2}\omega(s+t,Y,z+Z)\,dt\,dZ\,dA(Y),\\
d_1&=\sqrt{r_1^2+Z^2},&d_2&=\sqrt{r_2^2+(Z-b)^2},\\
\omega_-W(\sqrt{\tau^2-b^2},\theta)
 &\le V_g\le\omega_+W(\sqrt{\tau^2-b^2},\theta).
\end{aligned}\tag{SW3}
```

Here the positive lower and upper bounds are on the entire compact causal
tube, not just endpoints. Empty clock fibres have zero weight. This is a
physical union counted once, not a sum over meridians.
With `s=-2+xi*(4-tau)`, the exact full pair integral is

```math
\begin{aligned}
d\gamma&=dA(p)\,d\phi(n)\,dz\,d\xi,\\
F&=(4-\tau)\sin\theta\,
 \omega(s,p,z)\omega(s+\tau,q_\theta,z+b)K_4(\rho V_g),\\
P_g(\rho)&=\int_{US^2\times[0,20]\times[0,1]}d\gamma
 \int_0^\pi d\theta\int_\theta^4 d\tau
 \int_{-\sqrt{\tau^2-\theta^2}}^{\sqrt{\tau^2-\theta^2}} F\,db,\\
\mathcal A_{\rho,4}&=\frac4{\sqrt6}
 [\sqrt\rho\,\mu_g(M)-\rho^{3/2}P_g(\rho)].
\end{aligned}\tag{SW4}
```

The first measure includes the frame once, not an additional rotational
factor. Both circle signs and both
endpoint densities remain. Bounded kernel and finite measures justify
finite-density Fubini, not a normalized limit.

### The missing signed sphere-point map

Use planar coordinates `(x,y)` with foci `(0,0)` and `(theta,0)`, and let
`r=sqrt(x²+y²)`, `v=sqrt((x-theta)²+y²)`. In the regular triangle range
`r+v<2*pi-theta`, define

```math
\begin{aligned}
D_\theta(r,v)&=\prod_{u\in\{(r+v+\theta)/2,(r+v-\theta)/2,
 (\theta+r-v)/2,(\theta-r+v)/2\}}\mathrm{sinc}(u),\\
Y_\theta(x,y)&=\cos r\,p+
 \frac{\cos v-\cos\theta\cos r}{\sin\theta}\,n
 +y\frac{\sqrt{D_\theta(r,v)}}{\mathrm{sinc}\theta}\,k,\\
Q_\theta(r,v)&=\frac{\mathrm{sinc}r\,\mathrm{sinc}v}{\sqrt{D_\theta(r,v)}}.
\end{aligned}\tag{SW5}
```

The third coordinate has the **sign of y**. Squaring it using the spherical
Gram determinant proves `abs(Y)=1`; dotting with p and q_theta gives the two
prescribed distances. Each open planar half maps bijectively to its own
spherical orientation. The area Jacobian on **each** half is Q, as follows
by differentiating those two dot products. Thus the whole signed plane
already includes the two orientations: neither another factor two nor an
orientation-averaged weight belongs in the integral.

All apparent zero-distance square roots are removable in the even analytic
functions in SW5. At theta zero the continuous map is the exponential map
`cos(r)*p+sinc(r)*(x*n+y*k)`. For example the n component can be evaluated as

```math
\begin{aligned}
Y_\theta(x,y)\cdot n
 &=\frac{(x-\theta/2)\mathrm{sinc}((r+v)/2)\mathrm{sinc}((r-v)/2)
 +(\theta/2)\mathrm{sinc}(\theta/2)^2\cos r}
 {\mathrm{sinc}\theta}.
\end{aligned}\tag{SW6}
```

This also proves smooth extension at the long circle axis. It is not valid
to copy RC4 with a density independent of Y.

In RC4's full spatial boost, keep its `x=X_1`, `y=X_2`, `t_*`, `Z_*` and
replace its integrand by
`Q_theta(r_1,r_2)*omega(t_*,Y_theta(X_1,X_2),Z_*)`.
The determinant is still `q²`, where `q=tau²-theta²-b²`. SW5 proves this is
the **exact** physical weighted volume. On every compact off-cut long set,
the map and its derivatives in `h=sqrt(q)` are uniformly bounded.
Simultaneously reflecting `(B_2,B_3)` sends h to minus h in the integral.
The integral is even and smooth in h, hence smooth in q by Taylor's integral
remainder (use twice as many h derivatives). No symmetry of Omega is needed.
Its positive zero coefficient follows by integration of the positive density.
All radial and phase derivatives needed below are uniform, also at theta zero.
One need not differentiate the singular polar coordinate m at its poles;
use the smooth spatial direction vector, or bounded radial/phase derivatives
with m fixed. The outer contacts occur strictly away from those poles.

## 3. New focusing estimate: sphere motion is on the scale sqrt(e/a)

Put `a=pi-theta`, `u=theta+e`, and use exactly RC6's straightened closing
variables

```math
\begin{aligned}
B(u)&=\sqrt{16-u^2},\qquad b=B(u)v,\\
\tau&=\sqrt{u^2+B(u)^2v^2},\qquad s=-2+\xi(4-\tau),\\
4-\tau&=\frac{B(u)^2(1-v^2)}{4+\tau},\\
j(a,e,\zeta)&=(4-\tau)\frac{uB(u)}\tau
 \omega(s,p,z)\omega(s+\tau,q_\theta,z+b),\\
d\nu_c&=\sin a\,j(a,e,\zeta)\,da\,de\,d\zeta,
 \qquad\zeta=(p,n,v,\xi,z).
\end{aligned}\tag{SW7}
```

The frame is part of zeta. The compact ranges for v,xi,z and the frame retain
every closing source and partner. The displayed factor vanishes at v=±1,
not in its neighborhood. All its e derivatives are bounded.

Use RC7's bounded time/circle boost on the fixed diamond D0. In its planar
sphere coordinates
`x=theta*ell+e*B_1`, `y=sqrt(e*(2*theta+e))*B_2`,
`ell=1/2+A+B_1`. Insert SW5 in the **interior** weight. This gives

```math
\begin{aligned}
V_g&=e^2 H_c(a,e,\zeta),\\
H_c&=(2\theta+e)^2\int_{D_0}
 Q_\theta(r_1(e),r_2(e))
 \omega(t_*(e),Y_\theta(x(e),y(e)),Z_*(e))\,dA\,dB,\\
\widetilde H&=\sqrt a\,H_c,\qquad 0\lt c\le\widetilde H\le C,\\
|\partial_e^j\widetilde H|&\le C_j a^{-j}\quad(0\le j\le4),
 \qquad 0\le e\le\eta a.
\end{aligned}\tag{SW8}
```

Here is the additional derivative proof, including the longitudinal tips.
It is the step that sphere-independent RC8 did not prove.
Set `e=a*h²`. F9's polynomials in e and the even entire sine products give
`D_theta(e)/D_theta(0)` holomorphic, bounded and bounded away from zero on
one fixed complex disk in `e/a`. At zero,
`D_theta(0)=sinc(theta)*sinc(theta*ell)*sinc(theta*(1-ell))`.
In particular `D_theta(0)<=C*a`. F9–F11's pointwise comparison also bounds
`Q_theta(e)/Q_theta(0)` and all its derivatives in this rescaled disk.

The p coordinate of Y is an entire function of `r_1²`. In its n coordinate,
each positive-order e derivative of the cosine numerator is bounded uniformly
on D0; the division costs at most `C/a`. After rescaling, its j-th derivative
for j≥1 costs `a^(j-1)`, which is bounded. At zero it is simply
`sin(theta*ell)`. These statements use the polynomials in squared distances,
so they remain true when ell approaches zero or one.
The k coordinate is
`h*sqrt(a*(2*theta+a*h²))*B_2*sqrt(D_theta(a*h²))/sinc(theta)`.
Its derivatives in h are uniformly bounded because
`sqrt(a*D_theta(0))/sinc(theta)<=C`, including both tips.
The bounded time/circle boost has the same smooth h bounds.
Extend the smooth sphere density to a compact tubular neighborhood in R³ to
apply ordinary chain rules; its values on the actual sphere are unchanged.

Consequently the weighted integrand, after multiplication by sqrt(a), has
bounded h derivatives through any fixed finite order. At negative h use the
same formula; reflection of **both** B2 and B3 gives the same integral.
The even-smooth lemma therefore gives the asserted e derivative bounds.
The integral of `sqrt(a)*Q_theta(0)` has a positive uniform lower bound on
`1/4<=ell<=3/4`; multiply by omega_- and shrink a single eta to obtain the
lower bound in SW8. This proves, rather than assumes, the weighted phase
bounds. Treating Y's transverse displacement as uniformly O(sqrt(e)) would
have lost the essential inverse power of a.

On the whole cut box, including `e=2*a`, SW3 and F13 independently give

```math
\begin{aligned}
c\frac{e^2}{\sqrt{a+e}}&\le V_g(a,e,\zeta)
 \le C\frac{e^2}{\sqrt{a+e}},\\
&0\le a\le a_0,\qquad0\lt e\le e_0.
\end{aligned}\tag{SW9}
```

No derivative across the secondary transition is inferred from that inequality.
For perspective, the exact antipodal leading coefficient is now a weighted
meridian integral, not D times a source value. For fixed source and b, with
`tau_0=sqrt(pi²+b²)`, dominated rescaling of the clock fibres in SW3 gives

```math
\begin{aligned}
\lim_{e\downarrow0}\frac{V_g(s,p,z;\sqrt{(\pi+e)^2+b^2},-p,b)}{e^{3/2}}
 &=\frac43\int_0^{2\pi}\int_0^\pi
 \sin r\sqrt{\frac{2r(\pi-r)}\pi}\,
 \omega(s+\tau_0 r/\pi,Y(r,\varphi),z+br/\pi)\,dr\,d\varphi,\\
Y(r,\varphi)&=\cos r\,p+\sin r(\cos\varphi\,n+\sin\varphi\,k).
\end{aligned}\tag{SW10}
```

The support is bounded after scaling the transverse circle coordinate by
sqrt(e), exactly as in F5; the compact density bounds dominate it. This
coefficient depends on the whole family of meridians. The cancellation proof
uses the averaged estimate below, not vanishing of this positive coefficient.

## 4. Actual primitive, moving contacts and critical signed control

Use `w=sqrt(V_g)`, with no flat-volume constant inserted. Define the capped
sublevel primitive before assuming any monotonicity along the moving fibres:

```math
\begin{aligned}
f_c(a,\zeta,w)&=\int_0^{e_0}j(a,e,\zeta)
          \mathbf1_{\{V_g(a,e,\zeta)\le w^2\}}\,de,\\
N_c(w)&=\int\sin a\, f_c(a,\zeta,w)\,da\,d\zeta,\\
\left|\sin a\frac{f_c-c_1w-c_2w^2-c_3w^3}{w^3}\right|
 &\le C a^{-1/4},\\
N_c(w)&=n_1w+n_2w^2+n_3w^3+o(w^3).
\end{aligned}\tag{SW11}
```

Derivation: SW9 confines **every** sublevel to `e<=eta*a` when
`w<=kappa*a^(3/4)`. SW8 then makes `e*sqrt(H_c)` strictly increasing on that
wedge. Its inverse and the integral of j have exactly RC10's coefficients,
now at every actual zeta; in particular j includes both endpoint factors in
SW7. After `e=a*E`, `w=a^(3/4)*W`, inverse Taylor gives
`abs(c_i)<=C*a^(1-3*i/4)` and the cubic quotient bound `C*a^(-5/4)`.
For fixed a>0 the quotient tends to zero. Outside this wedge SW9 gives
`e<=C*(a^(1/4)*w+w^(4/3))<=C*w^(4/3)` on each sublevel, without assuming a
global inverse. This bounds f_c and all three subtracted terms by the same
cubic quotient bound. Multiply by the **actual** sine measure and integrate
over compact zeta. Dominated convergence yields SW11. Both orientations and
all moving time/circle contacts are in that dominator.

For off-cut long partners, the exact weighted full boost following SW6 gives
`V=q²H`, with H smooth, positive, and uniform on `r>=delta/2`, `theta<=d<pi`.
Invert `w=q*sqrt(H)` at fixed frame and source variables. Use RC5's physical
Jacobian `r²*sinc(theta)/(2*tau)`, but retain the frame measure and the two
actual endpoint densities. Both roots `r²+Q(r,...,w)=delta²,16` have derivative
`2r+O(w)` bounded away from zero. The artificial sphere contact roots satisfy
`r=d/sqrt(1-m²)` and meet the outer time root at
`abs(m)=sqrt(1-d²/16)`, with nonzero m derivative. They may depend on the
frame, source time fraction and circle coordinate. Straighten each moving
radial interval and each of the two sign-specific outer intervals before
Taylor expansion. Their full Leibniz boundary terms are retained. Uniform
bounds imply the actual density `B_o=b_0+b_1*w+b_2*w²+O(w³)`.
The small-r long set stays in the positive-phase complement, not outside the
observable. No assumption of evenness of H in theta or of Omega in b is used.

The disjoint exhaustive sectors are those of RC15: strict temporal short;
off-cut long; the full small cut box; and excess. One sufficiently small
fixed delta is used for S30 and all these sectors. Choose fixed a0,e0,w0
compatibly, with `pi+e0<4`. SW9 and compactness give a positive phase floor
on excess and on the retained above-cap pieces. Their finite pair measure
makes the normalized response exponentially small. On the small collar,

```math
\begin{aligned}
\int_0^\infty z^jK_4(z^2)\,dz&=0\quad(j=0,1,2),\\
\rho^{3/2}P_o(\rho)&\longrightarrow0,&
\rho^{3/2}P_c(\rho)&\longrightarrow0,&
\rho^{3/2}P_e(\rho)&\longrightarrow0.
\end{aligned}\tag{SW12}
```

Subtract the density polynomial for off-cut before absolute estimates.
For cut integrate `K_4(rho*w²) dN_c` by parts, then subtract its three
primitive terms. The bounded vanishing remainder quotient in SW11 is
dominated after rescaling by `C*z^4*abs(K_4'(z²))`. All phase-cap boundary
terms and polynomial tails are retained and exponentially small. This proves
SW12 without asserting a uniform density jet at the antipode.

## 5. Complete restoration, partitions and separate expectation

S30 applies to this smooth G-SS metric at the same fixed delta. Its compact
causal tubes, finite normal/face atlas, smooth unit fields and actual geometric
target are as checked in CP2; no joint chart is needed for this slab. Thus

```math
\begin{aligned}
S_g^\delta&=\frac4{\sqrt6}
 [\sqrt\rho\,\mu_g(M)-\rho^{3/2}P_s],&
S_g^\delta&\longrightarrow\mathcal T_g,\\
\mathcal A_{\rho,4}&=S_g^\delta-\frac{4}{\sqrt6}\rho^{3/2}(P_o+P_c+P_e)
 \longrightarrow\mathcal T_g.
\end{aligned}\tag{SW13}
```

The physical point is in short once. Every cutoff shell is the exact G2
mask difference with opposite signs, not a presumed negligible macroscopic
shell. Smooth source/target partitions can either be restored before SW4 or
retained in its amplitudes: compact derivative bounds and the same reflected
point maps prove the estimates with those smooth endpoint factors as well.
The full **ordered** double sum equals one. Same-chart-only masks do not.
The sphere poles and circle seam are coordinate artifacts, not boundary faces;
no causal partners are clipped there.

Only now specialize the existing checked `MeasuredOrderBDG4.expectation_eq`
to `mu=omega*(dt dA dz)|M`. The manifold is standard Borel, its conformally
unchanged order is closed, the measure is finite and atomless, and SW3 is the
actual exclusive interval volume by containment and endpoint nullity.
Under the unchanged `FinitePoisson.law (rho • mu)`, reduced two-point Mecke gives

```math
\begin{aligned}
\mathbb E L_k&=\rho^2\int_{x\prec y}
 e^{-\rho V_g(x,y)}\frac{(\rho V_g(x,y))^k}{k!}\,d\mu(x)\,d\mu(y),\\
\mathbb E A^{\mathrm{disc}}_{\rho,4}
 &=\frac4{\sqrt6\sqrt\rho}\mathbb E[N-L_0+9L_1-16L_2+8L_3]
 =\mathcal A_{\rho,4}\longrightarrow\mathcal T_g.
\end{aligned}\tag{SW14}
```

Finite Poisson second moments justify the signed finite sum. This is a
written geometric specialization of a checked generic bridge, not a newly
compiled instance. In particular it is not the unweighted
`SphereCircle.probability` abbreviation. No random-limit exchange, variance,
probability or almost-sure result is asserted.

## 6. Evidence and boundaries

`sphere_weighted_lenses.py` computes the actual signed two-distance point map
and an independent polar/clock integral. It checks both orientations, the full
spatial boost, circle axis/seam, weighted antipodal coefficient, both transition
sides, moving closing fibres and both endpoint densities. Its clock gap is
rationalized with ellipse-root products, avoiding the subtractive-gap issue
reported on #165 after that PR's bounded feedback pass. The old code and its
historical receipt are not silently repaired or recertified here.

Nineteen focused tests also check the independent Laplacian target, rotation
negative controls, constant scaling and finite ordered-partition identities.
Finite floating ranges do **not** prove SW8/SW11 or certify a complete action.
There is no new Arb certificate. The accompanying PR records actual full-suite,
CI, Markdown, browser-rendering and bounded-feedback results separately.
No Lean-affecting input changes; no fresh Lean audit is claimed.

**Physical content:** changing local volume density along the meridians changes
the interval phase and its coefficients, but the resolved transverse motion
and physical endpoint abundance still make the critical remainder integrable.
This is why this continuous focusing family cancels, whereas the fully matched
quartic family in #164 has a surviving response. Neither fact makes focusing
in general harmless. Sphere-dependent factors are a milestone, not the corrected
general theorem required by #81.

Refs #81, #24, #165, #164, #94, #86.
