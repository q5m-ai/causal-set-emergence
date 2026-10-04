# Curved boundary-collar handoff and #74 acceptance

**Conventional written results, not new Lean theorems.** This completes the
non-joint boundary-collar producer left in (S18) of
[the interior proof](curved-interior-short.md#7-boundary-collar-retained-the-remaining-747576-gate).
The actual truncated short integral is decomposed exactly, its bulk and
single-future-face remainders are controlled with the signed kernel, and the
remaining **actual corner functional** is handed to #75 with its precise
normalization and compensating joint flux. Its limit is not assumed or proved
here. #75 owns that joint comparison/coefficient; #76 owns assembly and the
separate expectation transfer.

The base is `8b05befffd4a24fea3724f2d5ed41d33684b9fc5`, after merged #122.
We consume #122's interior analysis and #117/#121's averaged long theorem.
We neither recreate the Poisson bridge nor import a flat action theorem into
a curved patch. Independent human mathematical review remains outstanding.

## 1. Original class, fixed cutoff and extension convention

Use the original `AdmissibleTwoFace`, the density $`q(t)=1+t^2`$,
$`d\mu_g=q(t)\,dt\,dz`$, and the constants and signed kernel (S1).
The original closed causal order, exclusive interval endpoints, normalization
and both endpoint measures are unchanged. Write

```math
\begin{aligned}
\mathcal O&=\{z:h(z)>0\},&\ell(z)&=f(z)-h(z),\\
M&=\{(t,z):z\in\mathcal O,\ \ell(z)\lt t\lt f(z)\},&
\nu_{\mathcal O}&=-Dh/|Dh|\quad\text{on }\partial\mathcal O.
\end{aligned}\tag{H1}
```

All boundary components are included. If the positive region is empty the
identities are zero. Otherwise its closure is compact and its boundary is a
regular C³ level. Positive-height critical points remain allowed.
The original C³ future germs give a common smooth thickening of the closed
positive spatial region; this geometric fact is also recorded in
`AdmissibleTwoFace.exists_smooth_future_thickening`. No extra exterior
regularity or C⁵ face hypothesis is imposed.

Let chi and phi be fixed real C⁵ functions on a neighborhood of the closure
of M; smooth partition weights and the constant one qualify. Choose a common
fixed sufficiently small positive delta. Its restrictions are only derived
ones: the closed 4-delta tube of the closure is in the field neighborhood,
translated spatial arguments are in the future face's C³ thickening, the
phase derivatives below are positive, and the height band below delta is a
regular joint collar. These follow from compactness, the original margins
and continuity. For finitely many fields choose the minimum of their positive
cutoff bounds. All geometry, fields and this cutoff stay fixed as density
increases. No shrinking-cutoff uniformity or rate is asserted.

The auxiliary integrals below evaluate fields just outside M, within that
fixed neighborhood. For them use the **ambient** polynomial-density interval
law (S2). For actual pairs in M it equals the original restricted interval
volume by causal convexity and atomlessness. **No such equality is asserted
for auxiliary endpoints outside M.** Their added contributions are subtracted
exactly before taking a limit; they are not another production action.

## 2. Exact full/face/corner identity for the actual truncated amplitude

Fix z in the positive region, a sphere direction n, and
$`0\le u\le v\lt\delta`$. Put $`T=(u+v)/2`$, $`r=(v-u)/2`$ and

```math
\begin{aligned}
a&=f(z)-t,&d(z,u,v,n)&=T+f(z)-f(z+rn),\\
(1-\eta)T&\le d\le T+\eta r\le v,&0&\le\eta\lt1,\\
W_\rho(a)&=q(f-a)q(f-a+T)\chi(f-a,z)\phi(f-a+T,z+rn)\\
&\qquad\cdot K\!\left(c\rho(uv)^2\mathcal H(f-a,u,v)\right).
\end{aligned}\tag{H2}
```

The lower causal envelope keeps every future partner above the lower face.
Thus the actual upper-face test is exactly $`a>d`$, with $`0<a<h(z)`$;
there is no second spatial/chart restriction. The displacement measure is
$`(v-u)^2\,du\,dv\,dS(n)/8`$ with sphere mass $`4\pi`$.
For every positive density the identity

```math
\begin{aligned}
\mathbf1_{\{d\lt h\}}\int_d^h W_\rho(a)\,da
 &=\int_0^hW_\rho(a)\,da-\int_0^dW_\rho(a)\,da
   +\mathbf1_{\{h\lt d\}}\int_h^dW_\rho(a)\,da
\end{aligned}\tag{H3}
```

is just an equality of actual time intervals, valid also at contact. Multiply
by the displacement Jacobian and integrate over z,n,u,v. Denote the three
right-hand integrals by $`P^{\mathrm{full}}_{\chi,\phi}`$,
$`F_{\chi,\phi}`$, and $`J_{\chi,\phi}`$, respectively. They include W,
its measures and its curved phase, not just interval lengths. Then

```math
\begin{aligned}
P^<_{\chi,\phi}&=P^{\mathrm{full}}_{\chi,\phi}-F_{\chi,\phi}+J_{\chi,\phi},\\
S_{\chi,\phi}(\rho)&=S^{\mathrm{full}}_{\chi,\phi}(\rho)
                  +C\rho^{3/2}F_{\chi,\phi}(\rho)
                  -C\rho^{3/2}J_{\chi,\phi}(\rho),\\
S^{\mathrm{full}}_{\chi,\phi}
 &=C\sqrt\rho\int_M\chi\phi\,d\mu_g
                         -C\rho^{3/2}P^{\mathrm{full}}_{\chi,\phi}.
\end{aligned}\tag{H4}
```

There is one point term. Every actual short partner is retained, and every
added partner cancels. In F the source runs from the future face down a depth
d, even when that passes below the past face. J restores precisely that
overshoot. It is supported where $`0<h(z)<d\le\delta`$: a genuine joint
collar, not the whole boundary. Its two auxiliary endpoints straddle the two
faces. J can have either signed value because K is signed; the positive
length of the overshoot does not make its normalized action nonnegative.
All integrals are absolutely finite at each fixed positive density on the
compact domains above, justifying these changes of order.

## 3. Full-cone bulk estimate without deleting its correction

The auxiliary full cones over the whole closure of M lie in one compact field
neighborhood. The proof of (S8)–(S14) is uniform on any such compact source set:
it uses the polynomial phase, the field's C⁵ bounds and the complete cone, not
source distance to a face. In #122 that distance was needed to identify the
cone with the actual inner integral. Here (H3) supplies the exact correction
instead. Repeating those same uniform bounds with source set the closure of M
and multiplying by the bounded measurable weight chi times the indicator of M
gives

```math
\begin{aligned}
S^{\mathrm{full}}_{\chi,\phi}(\rho)
 &\longrightarrow\mathcal B_{\chi,\phi}
 :=\int_M\chi(\Box_g\phi+R\phi/2)\,d\mu_g.
\end{aligned}\tag{H5}
```

This is an auxiliary full-cone lemma, not an application of the old
interior-support theorem with its hypothesis removed. Its proof retains the
entire (C11) jet, including $`K''`$, and its uniformly vanishing signed
actual-minus-jet remainder. The finite radial responses are uniform for source
q in a compact positive interval. No integration by parts in chi was used.
The scalar and wave operator are independently defined by (C4)/(S16), with
signature (+---) and the recorded sign conversion to `conformal_geometry.py`.

## 4. Signed single-face remainder with only C³ face geometry

We next prove the actual F estimate. Flatten its time interval by
$`a=b\,d`$, $`0\le b\le1`$, before transporting phase. Write
$`R_0=u/v`$ temporarily for a ratio, not scalar curvature, and set

```math
\begin{aligned}
D(z,n,v,R_0)&=\frac{1+R_0}{2}
 +\frac{f(z)-f(z+v(1-R_0)n/2)}v,\\
D_0(R_0)&=\frac{1+R_0}{2}-\frac{1-R_0}{2}Df(z)[n],\\
D_1(R_0)&=-\frac{(1-R_0)^2}{8}D^2f(z)[n,n],\\
\|D-D_0-vD_1\|_{C^3(R_0)}&\le Av^2,\\
\|\partial_v(D-D_0-vD_1)\|_{C^1(R_0)}&\le Av.
\end{aligned}\tag{H6}
```

The bounds are uniform on a fixed slightly enlarged ratio interval about
[0,1], z in the closed positive region and n on the sphere. They follow from
ordinary C³ Taylor estimates, not four or five derivatives of f. For example,
with $`s=(1-R_0)/2`$, the first three ratio derivatives of D are
$`1/2+Df(z+vsn)[n]/2`$,
$`-vD^2f(z+vsn)[n,n]/4`$ and
$`v^2D^3f(z+vsn)[n,n,n]/8`$.
Taylor's theorem for the first two and boundedness of the third give (H6);
the v derivative needs only the stated C¹ ratio norm. This is why blindly
asking for five mixed geometry derivatives would strengthen the wrong class.

Put $`t=f(z)-bvD`$. The exact phase after this flattening is

```math
\begin{aligned}
w&=v^2\Phi(z,n,b,v,R_0),\\
\Phi&=R_0\sqrt{\mathcal H(f-bvD,vR_0,v)},\\
\partial_u w
 &=\frac{v\{2\mathcal H+u(\mathcal H_u-bd_u\mathcal H_t)\}}
         {2\sqrt{\mathcal H}},\qquad
 d_u=\frac{1+Df(z+rn)[n]}2.
\end{aligned}\tag{H7}
```

In the last line H is evaluated at t=f-bd. The mixed source-time term in this
Jacobian is essential. At v=0 the ratio phase is $`R_0\sqrt{q(f)}`$.
Compactness and (H6) give a common small delta with
$`\Phi_{R_0}\ge1/2`$ on the enlarged ratio interval. The inverse ratio
$`R_0=U(z,n,b,v,\zeta)`$, $`\zeta=w/v^2`$, and the pushed amplitude obey

```math
\begin{aligned}
A(w,v;z,n,b)&=v^2\Psi(z,n,b,v,\zeta),\\
\Psi&=\left.
 \frac{D(1-R_0)^2q(t)q(t+v(1+R_0)/2)
       \chi(t,z)\phi(t+v(1+R_0)/2,z+v(1-R_0)n/2)}
      {8\Phi_{R_0}}\right|_{R_0=U},\\
\Psi(v,\zeta)&=\psi_0(\zeta)+v\psi_1(\zeta)+E(v,\zeta),\\
|\partial_\zeta^jE|&\le Av^2\quad(j=0,1,2),&
|\partial_vE|&\le Av.
\end{aligned}\tag{H8}
```

Here and below omitted z,n,b parameters range over a fixed compact set.
For completeness, (H6) gives a C³ ratio expansion of Phi through first
order in v with C³ remainder bounded by $`Av^2`$. Its zeroth phase is
linear and its first coefficient is quadratic in the ratio. Solving the
inverse equation and differentiating it three times therefore gives the same
expansion in the inverse C³ norm without differentiating the C³ error again.
Substitute in
the numerator and denominator of (H8). The denominator is bounded away from
zero; its two zeta derivatives use at most the third ratio derivative of Phi.
The C⁵ fields and the second bound of (H6) give the stated E and its first v
bound. Only continuity in z,n,b is needed. Thus this argument does not
presuppose a quadratic phase jet for a clipped geometric amplitude.

### Moving diagonal and its retained thin strip

At $`u=v`$, d=v, independent of n and the slope of f. The diagonal phase is

```math
\begin{aligned}
w&=\nu^2\sqrt{q(f)+f(1-2b)\nu+(b^2-b+4/15)\nu^2},\\
\nu_0&=(w/\sqrt{q(f)})^{1/2},&
\nu&\asymp\sqrt w,&|\nu-\nu_0|&\le Aw.
\end{aligned}\tag{H9}
```

It is increasing for the same sufficiently small fixed cutoff. The exact
amplitude is integrated over $`\nu\lt v\lt\delta`$ and is zero if this
interval is empty. Both it and its first ratio variation vanish on its actual
diagonal through the factor $`(1-U)^2`$.

The pushed amplitude of the physical face two-jet is
$`v^2\psi_0+v^3\psi_1`$, integrated from nu0 to delta. One way to check
this assertion without ignoring moving supports is to introduce e=lambda v
in D and Phi in (H8), keep the physical Jacobian factor $`vD(e,R_0)`$,
and evaluate the fields at the corresponding scaled displacements. The
family at lambda=1 is exactly F. Its value and first lambda derivative at
zero are precisely the physical terms of displacement degrees one and two.
The first lower-endpoint term is zero because the amplitude vanishes there.
Fixed-density differentiation on the original compact cone is legitimate.

On a common small phase collar, write the exact pushed difference as

```math
\begin{aligned}
B^{\mathrm{face}}-B^{\mathrm{face,jet}}
 &=\int_{\nu_0}^\delta v^2E(v,w/v^2)\,dv
   +\int_\nu^{\nu_0}A(w,v)\,dv,\\
\left|\int_\nu^{\nu_0}A(w,v)\,dv\right|&\le Aw^3.
\end{aligned}\tag{H10}
```

The last integral is oriented and retained, not set to zero. On its interval,
$`v\asymp\sqrt w`$, its length is $`O(w)`$, and $`|1-U|=O(\sqrt w)`$.
Thus A is $`O(w^2)`$, proving (H10). The smooth extension used when U exceeds
one stays in the chosen compact neighborhood and cancels in the oriented
identity.

For the first integrand $`e(w,v)=v^2E(v,w/v^2)`$, (H8) gives

```math
\begin{aligned}
|\partial_w^j e|&\le Av^{4-2j}\quad(j=0,1,2),&
|\partial_v e|&\le Av^3,\\
\left(\int_{\nu_0}^\delta e\,dv\right)''
 &=\int_{\nu_0}^\delta e_{ww}\,dv
 -2e_w(\nu_0)\nu_0'-e_v(\nu_0)(\nu_0')^2-e(\nu_0)\nu_0''.
\end{aligned}\tag{H11}
```

Every displayed boundary term is $`O(\sqrt w)`$. The integral's second
w derivative has an integrable constant majorant on [0,delta]. Its zeroth
and first derivatives have stronger bounds. Splitting at a fixed positive v
and using uniform continuity above it shows that all three derivatives have
uniform right limits as w tends to zero. Their coefficients are explicitly
$`(1/j!)\int_0^\delta\partial_w^j e(0,v)\,dv`$ for j=0,1,2.
The fundamental theorem of calculus therefore gives a uniform right quadratic
Peano jet. The oriented strip in (H10) is of higher order.

The complete difference has a common bounded phase support and bounded
coefficients, including its cutoff corner at v=delta. Subtract the polynomial
on the whole phase half-line and use the three zero signed moments exactly
as in (S14). The majorant is a constant times $`z^2|K(z^2)|`$.
The strip bound may alternatively be integrated absolutely, giving a term
that tends to zero, plus an exponentially small fixed-phase tail. We obtain

```math
\begin{aligned}
C\rho^{3/2}\bigl(F_{\chi,\phi}-F^{\mathrm{jet}}_{\chi,\phi}\bigr)
 &\longrightarrow0,
\end{aligned}\tag{H12}
```

uniformly before integration over the compact z,n,b variables. This proves
the signed single-face remainder for the actual curved amplitude, not merely
its formal Taylor coefficients or an absolute bound on the original kernel.

## 5. Entire face jet, its signed response and the surviving flux

All fields and their derivatives in this section are evaluated at (f(z),z).
Put $`q=q(f(z))`$, $`q_1=q'(f(z))`$, $`p=|Df|^2`$ and
$`m=Df\cdot\nabla_z\phi`$. After sphere average, integration in a of the
whole degree-one/two Taylor polynomial gives

```math
\begin{aligned}
\langle W^{\mathrm{face,jet}}\rangle
 &=a_1TK(Z)+a_2T^2K(Z)+a_3r^2K(Z)+a_4r^2ZK'(Z),\\
Z&=c\rho q(uv)^2,\\
a_1&=q^2\chi\phi,\qquad
 a_2=\tfrac12q^2(\chi\phi_t-\chi_t\phi),\\
a_3&=-q^2\left[\frac{\chi\phi\Delta_z f}6
       +\frac{p(\chi_t\phi+\chi\phi_t)}6+\frac{\chi m}3\right]
       -\frac{q q_1\chi\phi p}3,\\
a_4&=-\frac{q q_1\chi\phi p}6.
\end{aligned}\tag{H13}
```

For example, start with
$`d_1=T-rDf[n]`$, $`d_2=-r^2D^2f[n,n]/2`$.
The two endpoint densities have first correction $`q q_1(T-2a)`$,
and the phase correction is $`(q_1/q)Z(T/2-a)K'(Z)`$.
Their a integrals and the sphere identities
$`\langle n_i\rangle=0`$ and $`\langle n_i n_j\rangle=\delta_{ij}/3`$
give (H13). No target coefficient has been inserted. The bulk's $`K''`$
term remains in (H5); in the face integral it first occurs at displacement
degree three and is covered by (H12), not deleted without an estimate.

The original finite radial primitives (C12) and their signed log moments give
these normalized **positive-sign** face responses:

```math
\begin{aligned}
(TK,\ T^2K,\ r^2K,\ r^2ZK')
 &\longmapsto q^{-3/2}(0,-2,6,-9),\\
\mathcal F_{\chi,\phi}(z)
 &=\sqrt q\{(1-p)\chi_t\phi-(1+p)\chi\phi_t
             -2\chi m-\chi\phi\Delta_z f\}
       -\frac{q_1}{2\sqrt q}\chi\phi p,\\
C\rho^{3/2}F_{\chi,\phi}(\rho)&\longrightarrow
                                      \int_{\mathcal O}\mathcal F_{\chi,\phi}\,dz.
\end{aligned}\tag{H14}
```

The finite-cutoff terms in (C12), including the nonzero finite-density TK
response, remain until their limits are taken. Those responses and the
remainders are uniform for the compact range of q and field/face data.
The limit is independent of the selected sufficiently small fixed cutoff;
this does not exchange a cutoff limit with density.

Define the coordinate normal-flux operator
$`N_k=\partial_t+Dk\cdot\nabla_z`$ and the joint flux

```math
\begin{aligned}
\mathcal N_{\chi,\phi}
 &=\int_{\mathcal O}\sqrt{q(f)}(\phi N_f\chi-\chi N_f\phi)_{t=f}\,dz,\\
\mathcal T_{\chi,\phi}
 &=\int_{\partial\mathcal O}\sqrt{q(f)}(\chi\phi)_{t=f}
                              Df\cdot\nu_{\mathcal O}\,dA,\\
\int_{\mathcal O}\mathcal F_{\chi,\phi}\,dz
 &=\mathcal N_{\chi,\phi}-\mathcal T_{\chi,\phi}.
\end{aligned}\tag{H15}
```

Indeed the pointwise difference between the density of N and (H14) is
$`\mathrm{div}_z(\sqrt{q(f)}\chi_f\phi_f Df)`$, including the total
spatial derivatives of the traces. The spatial divergence theorem gives
(H15) on every boundary component. For unit weights the single-face term is
**minus T**, not automatically zero. It vanishes for a planar future face,
but in general must be retained with the corner term.

## 6. Summable handoff, partitions and both spacetime boundary fluxes

Combine (H4), (H5) and (H14). This is the completed short producer:

```text
PROVED IN WRITING CurvedBoundaryShortHandoff(h,f,delta,chi,phi):
  original AdmissibleTwoFace; q(t)=1+t^2; fixed real C5 endpoint fields
  one common sufficiently small fixed delta from geometric/field margins
  actual S, exact F and J from (H2)-(H4); both endpoint measures retained
  S_chi,phi(rho) - B_chi,phi - N_chi,phi + T_chi,phi
                   + C*rho^(3/2)*J_chi,phi(rho) -> 0
  the error is summable for every fixed finite family of endpoint weights
```

The statement retains J as an explicitly specified geometric functional,
not a vanishing remainder. Add the already proved
`CurvedContactAveragedLong` from #117/#121 with exactly these weights and
cutoff. There is no new raw first-endpoint domination requirement. Set

```math
\begin{aligned}
\mathcal Q_{\chi,\phi}^{\delta}(\rho)
 &:=-C\rho^{3/2}J_{\chi,\phi}^{\delta}(\rho)-\mathcal T_{\chi,\phi},\\
A_{\chi,\phi}(\rho)-\mathcal B_{\chi,\phi}
 -\mathcal N_{\chi,\phi}-\mathcal Q_{\chi,\phi}^{\delta}(\rho)
 &\longrightarrow0.
\end{aligned}\tag{H16}
```

This is a statement about the actual weighted pair integral. Every artificial
partner in its auxiliary representation has been restored. For any finite
first-endpoint partition with sum one on a neighborhood of the closure,
choose delta so the same partition identity holds on the auxiliary tube.
At every density its short, long, full, face and corner terms sum exactly.
With phi=1 the N terms cancel only after this sum, since the derivatives of
all source weights sum to zero. Their individual terms need not vanish.
Auxiliary second-endpoint partitions likewise require their full sum, never
same-chart partner restrictions; all field and phase derivatives in (H13)
are retained until then.

Without interior support the integration-by-parts formula is explicitly

```math
\begin{aligned}
\int_M\chi\Box_g\phi\,d\mu_g
 &=-\int_M g^{\mu\nu}\partial_\mu\chi\,\partial_\nu\phi\,d\mu_g\\
 &\quad+\int_{\mathcal O}\sqrt{q(f)}(\chi N_f\phi)_{t=f}\,dz
       -\int_{\mathcal O}\sqrt{q(\ell)}(\chi N_\ell\phi)_{t=\ell}\,dz.
\end{aligned}\tag{H17}
```

Both spacetime faces and their orientations are present. This follows directly
by time integration and spatial integration with variable graph endpoints;
the lateral integral at the spatial joint has zero time length. It is not a
license to drop either displayed face flux. For compact interior chi it
reduces to (S17). For the unit field all wave/field-flux terms vanish.

### Resolving precisely the collar in (S18)

Let chi_int be as in (S18), extended by zero off its compact interior support,
and chi_col=1-chi_int on the auxiliary tube. Further decrease the fixed delta
once so the original full-cone margin over that support holds. In the face
strip $`a\le d\le\delta`$ chi_int is zero; it is also zero in the artificial
overshoot below the past face. Thus its F and J vanish **exactly**, not just
in the limit. At the future face chi_col is one with zero derivatives. Hence

```math
\begin{aligned}
S_{\chi_{\mathrm{col}},1}(\rho)
 -\tfrac12\int_M\chi_{\mathrm{col}}R\,d\mu_g
 -\mathcal Q_{1,1}^{\delta}(\rho)&\longrightarrow0,\\
A_g(\rho,M)-\tfrac12\int_MR\,d\mu_g
 -\mathcal Q_{1,1}^{\delta}(\rho)&\longrightarrow0.
\end{aligned}\tag{H18}
```

The entire collar curvature integral is now restored. The two long terms in
(S18) were consumed from #121. The remaining Q is solely the explicit corner
integral plus its already identified joint flux. No small-volume argument or
unweighted full-cone substitution was used.

For any two allowed **fixed** cutoffs, (H16) also proves that their Q values
differ by a quantity tending to zero, since A, B and N are the same. This
proves asymptotic cutoff compatibility, not existence of the joint limit or
shrinking-cutoff uniformity. Likewise different C⁵ extensions of the same
fields on M have identical bulk and boundary traces; the actual weighted
action is identical. Their Q difference therefore tends to zero. Auxiliary
extension choices cannot manufacture a surviving physical correction.

## 7. Named #75 obligation and #76 dependency

The missing analytic estimate now belongs precisely to #75's existing
joint tangent-comparison/weighted-estimate acceptance, not to another bulk
remainder. Its input is the **actual** Q in (H16), with the derived
single-face joint flux included. The required output must be proved, not
added to admissibility:

```text
OPEN, OWNED BY #75: CurvedJointCornerLimit(h,f,delta,chi,phi)
  same original class, q, actual action, fixed cutoff and endpoint weights
  Q_chi,phi = -C*rho^(3/2)*J_chi,phi - T_chi,phi exactly as above
  independently identify the curved joint measure and positive-normal angle
  prove the actual weighted tangent-comparison estimate used
  prove Q_chi,phi -> integral_joint chi*phi*coth(theta) dA_g
    OR identify a genuine surviving correction and revise this target
  retain all cross-chart partners and make finite weighted summation explicit
```

No claim that this open target follows from pointwise conformal angle
invariance, area scaling, or the flat global action theorem is made here.
#75 must include the nonzero-curvature unequal-axis example and all its
original geometric and signed-comparison obligations. In particular the
existence, boundedness and value of the general normalized corner limit are
**not inferred** just from its support in a fixed regular collar.

#76 consumes (H18) plus that named #75 producer, and only then applies #93's
separate curved finite-density expectation equality. If #75 finds a correction,
(H18) carries it unchanged into the assembly. Closing #74 on these producer
results neither closes #75/#76 nor proves a complete curved expectation limit.

## 8. Complete #74 acceptance map

- **Frozen class and exact contract:** (H1)–(H4), the two written consumer
  signatures, original `AdmissibleTwoFace`, fixed polynomial density and one
  common fixed cutoff. No desired asymptotic is geometric input.
- **Uniform interval/measure control and independent bulk coefficient:** exact
  interval law (S2), both densities in (H2), the uniform compact full-cone
  estimate (H5), original C, and the independently defined (C4)/(S16) scalar.
  The collar bulk is included in (H18), not left in an error term.
- **Signed local and long remainders for the actual observable:** the full-cone
  signed remainder from (S8)–(S14) with its exact correction (H3); the actual
  single-face remainder (H6)–(H12), including moving contacts; and the consumed
  #121 long result. Equations (H16)/(H18) leave only the named #75 corner
  functional, not an unnamed short remainder or an assumed joint estimate.
- **Derivative/cutoff accounting and summable output:** the full face jet
  (H13), nonzero single-face/joint flux (H14)/(H15), exact finite partition
  sums, both boundary fluxes (H17), and the explicit #75/#76 handoff (H18).
- **Written/checked boundaries and surviving contributions:** the proof above
  supplies #74's deterministic bulk and non-joint collar producer. The
  surviving joint functional and its ownership are explicit; its target is
  left open under #75. Executable checks below are distinct from universal
  proofs; no new Lean or independent human-review claim is made.

These discharge the **#74-owned** obligations. The still-open joint limit is
not a reason to duplicate #75 inside this issue, nor permission for #76 to
assume that limit. Independent human mathematical review remains outstanding.

## 9. Verification and regression scope

`curved_boundary_collar.py` checks the interval identity for arbitrary time
weights, the total phase Jacobian, the complete angular face jet, signed basis
responses, and the flux rearrangement. `test_curved_boundary_collar.py` adds
actual original-coordinate and phase-pushed quadrature, nonconstant endpoint
weights, measure/phase negative controls, both-face flux accounting, fixed
cutoffs, and exact finite-density restoration at joint contacts. A planar-
future unequal-axis calibration has nonzero spacetime curvature and varying
joint angle; its actual signed corner term is not negligible. This is a
regression, not #75's general joint comparison proof.

No Lean source, checker, dependency or build input changes. A future formal
port must run the full local `formal/check.sh` source/transitive-axiom gate.
No new integrated Lean audit is claimed here. No convergence rate, arbitrary
conformal-factor extension, singular-angle limit or sample-wise convergence
is asserted.

```sh
.venv/bin/python -m unittest -v test_curved_boundary_collar
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
.venv/bin/python reproduce.py
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
