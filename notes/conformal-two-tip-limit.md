# Regular curved two-tip crease: producer and complete assembly (#178)

**Written theorem, not a Lean theorem or independent mathematical acceptance.**
This resolves one required #156 subentry: regular two-tip SN/crease contacts
in conformally Minkowski **4D**, for every floor and factor specified below.
It is not a universal crease-cancellation theorem. The original required and
deferred matrix in [the #156 ledger](null-mixed-required-coverage.md#2-exact-required-matrix-versus-explicitly-deferred-work)
is unchanged. Human scrutiny/provenance/formalization remain #94/#86.

Base: `d2cbbc12dbfee6376140a2137013f3d409adfdbf`, current integration when work
started. The actual integrated inputs are [CC1–CC14](conformal-cone-limit.md),
[TT1–TT11](two-tip-null-feasibility.md), [LA1–LA10](two-tip-lens-limit.md),
[LB1–LB4](two-tip-null-limit.md), and [#90](general-contract.md). Historical
receipts in those sources are not rewritten. #175/PR #176 and #177 own curved
2D/3D **spacelike** work; their unaccepted claims are not used. Shared action,
measure, order, law, target, cutoff interfaces and formal sources are unchanged.

## 1. Smallest new contact regime and exact quantifiers

Fix any a>0 and tips v_i=(0,c_i), c_+=(a,0,0), c_-=(-a,0,0). Write x=(z,w),
w in R2. Any spacelike-separated pair of tips admits this frame. Let H be
**any** smooth globally lambda-Lipschitz function on R3, lambda<1, with
H(0)>a. Let Omega be **any** fixed smooth positive function on a neighborhood
of the compact causal enclosure below; set g=Omega² eta, A=Omega⁴. The letter
A here denotes the volume density, not the action. Require the geometric
regular-contact condition

```math
\begin{aligned}
h_C(w)&=H(0,w)-\sqrt{a^2+|w|^2},&
\nabla_w h_C&\ne0\quad\hbox{on }h_C=0,\\
F&=\{t+H(x)>0\},& P_i&=I^-(v_i),\\
M_i&=F\cap P_i,& P_L&=P_+\cap P_-,& P_U&=P_+\cup P_-,\\
L&=F\cap P_L,& U&=F\cap P_U.
\end{aligned}\tag{CT1}
```

All components of h_C=0 are retained; no axial symmetry, concavity or
polynomial condition is imposed. This selects the **regular** floor/crease
contact already present in #90/#156, not a restriction on their full matrix.
Tangential contacts are an explicit residual, not called impossible. H(0)>a
ensures central overlap and H(c_i)>0. The fixed TT1 floor satisfies CT1.
A small nonzero transverse sine perturbation of it also does, so the class
is not the axial calibration in different notation.

The lower epigraph is a future set; P_i, their intersection and their union
are past sets. Thus every **closed ambient interval** between endpoints of
any of these four regions is contained in that region. Straight causal
segments also identify the intrinsic order. Positive conformal rescaling
preserves these sets/order, not their volume. The selected isolated restricted
interval is the entire physical diamond with its actual interior density,
counted once. A source in the common part of U has the **union** of its two
source-to-tip partner domains, not their sum. This distinction will be used
before applying the nonlinear kernel.

The regions are open, nonempty and bounded: H(x)<=H(0)+lambda|x| and
r_i(x)>=|x|-a give |x|<(H(0)+a)/(1-lambda) wherever a cap has positive height.
Time is bounded by the same estimates. Their closures are compact, and their
Lipschitz graph frontiers have zero volume. This last fact is not a normalized
contact estimate.

The two smooth null sheets meet at
C={z=0,t=-sqrt(a²+|w|²),h_C(w)>0}; its boundary is Gamma={h_C=0} in this
crease. C is spacelike with metric I-ww^T/(a²+|w|²), hence area density
 a/sqrt(a²+|w|²). Gamma is a compact smooth one-manifold by CT1, possibly
with several components. U has the two tips; L has none. The center of C
is a regular crease point, not a third tip. There are no extra strata.
Compact smooth regular Gamma has a finite atlas; the argument does not
assume one circle. Null/floor transversality follows from |grad H|<1.

For each tip, let R_i(omega) be the unique positive root
R_i=H(c_i+R_i omega), with derivative margin 1-lambda. On the joint,
-g(d(-R_i,c_i+R_i omega))=Omega² R_i² d omega². Let E_i^U be directions
whose joint point has i*z>0, and E_i^L those with i*z<0 (i=+1,-1).
Their interfaces are the actual Gamma. Independently of the action set

```math
\begin{aligned}
J_V&=\sum_{i=+,-}\int_{E_i^V}
 R_i(\omega)^2\Omega(-R_i,c_i+R_i\omega)^2\,d\omega,\\
T_V&=3\int_V\Omega\Box_\eta\Omega\,dt\,dx+J_V
       \qquad(V=L,U),\\
T_U+T_L&=T_{M_+}+T_{M_-}.
\end{aligned}\tag{CT2}
```

These are half scalar curvature in #90's sign convention and the induced
SN area. The last identity is geometric inclusion–exclusion for bulk and
complementary screen pieces. It does **not** set a crease coefficient to zero.

**Theorem CT.** For every fixed CT1 member, the complete canonical deterministic
actions on L and U tend to T_L and T_U. Separately, their original-law Poisson
expectations have the same limits. Only density varies. The proof below
computes the potential extra-stratum response rather than assuming its absence.

Why this task: two is the smallest multiplicity beyond one future tip. TT-A
uses its fixed flat axial overlap; CC requires a single cone and has no crease.
Neither supplies the moving-floor response on P_L. Resolving this missing
producer addresses the original same-side-crease/multiple-tip row and its
curved regular SN interfaces, not another example within an established class.

## 2. Exact physical pair domain and interval phase

Use K(z)=(1-9z+8z²-4z³/3)exp(-z), c=pi/24, C4=4/sqrt(6). For smooth
endpoint fields chi,phi on a neighborhood of the closure, keep

```math
\begin{aligned}
P_{\chi,\phi}(\rho)&=\int_{L\times L}\mathbf1_{p\preceq q}
 \chi(p)\phi(q)K(\rho V_g(p,q))\,d\mu_g(p)d\mu_g(q),\\
B_{\chi,\phi}(\rho)&=C_4\sqrt\rho
 \left[\int_L\chi\phi\,d\mu_g-\rho P_{\chi,\phi}(\rho)\right],\\
u&=(1,\sqrt{1-\xi}\,n),\qquad p=q-\ell u,\\
dq\,dp&=\tfrac12\ell^3\sqrt{1-\xi}\,dq\,d\ell\,d\xi\,dn,\\
P_{\chi,\phi}(\rho)&=\frac12\int_{P_L}\int_{S^2}\int_0^\infty\int_0^1
 \ell^3\sqrt{1-\xi}\, A(q)\phi(q) A(p)\chi(p)\mathbf1_{F}(p)
 K(c\rho\ell^4\xi^2 h)\,d\xi\,d\ell\,dn\,dq.
\end{aligned}\tag{CT3}
```

Here h is the **actual** normalized rest-diamond integral CC4:
 h=c^(-1) integral_D0 A(X), using its affine boosted map with endpoints p,q.
Its determinant is ell⁴ xi², so V_g=c ell⁴ xi² h. Both measures and the
interior density appear in CT3. If q is in P_L and p precedes q, then p is
in P_L. If p is in F, its successor q is in F. These two implications prove
the exact domain, without any null-generator rank assumption. There is no
source-to-common-tip identity on L.

CC4's interval-map hypotheses are discharged: the entire diamond is in the
compact enclosure, the density extends smoothly and positively around it,
and its positive bounds give positive bounds on h. Reflection in the two
transverse rest coordinates makes h smooth in xi near zero with uniformly
bounded derivatives of every fixed order, down to ell=0 and both interval
tips. Near xi=1 we need bounded ell derivatives only. No G-SS boundary theorem
or flat weighted Gaussian formula is reused.

## 3. Long producer: straighten the source floor, not the crease

A naive copy of CC3 fails: no one cone-ball parameterization has P_L as its
full domain. Integrating a moving spatial lens at each fixed ell can create
closing floor/crease tangencies even when CT1 holds at ell=0. We instead
integrate **ell as a variable** when straightening the floor. This handles
those translated contacts rather than asserting they stay transverse.

Choose a fixed sufficiently small delta>0, and a smooth function psi(ell)
which is one for ell<=delta/2 and zero for ell>=delta. Short has weight psi;
long has 1-psi. The point belongs only to short. This is a fixed temporal-gap
split, not a new action or density-dependent regulator. Insert smooth compact
support cutoffs in q and ell equal to one on the complete physical support;
boundedness above guarantees they exist. They are identically one on an open
neighborhood of that support and therefore remove no pairs.

For fixed q,n introduce the floor coordinate r and physical phase coordinate w:

```math
\begin{aligned}
r&=q_t-\ell+H(q_x-\ell\sqrt{1-\xi}\,n),&
w&=\ell^2\xi\sqrt{h(q,\ell,\xi,n)},\\
\partial_\ell r\big|_{\xi=0}&=-1-\nabla H(q_x-\ell n)\cdot n
 \le-(1-\lambda),\\
\det\frac{\partial(r,w)}{\partial(\ell,\xi)}\bigg|_{\xi=0}
 &=\partial_\ell r\,\ell^2\sqrt{h(q,\ell,0,n)}\ne0
       \quad(\ell\ge\delta/2).
\end{aligned}\tag{CT4}
```

At xi=0, ell is uniquely determined by r, because the first derivative has
one strict sign for all real ell. On the compact long support the inverse
function theorem consequently gives a common w collar and a smooth inverse
(ell,xi)(q,n,r,w), with bounded derivatives of every required finite order.
More explicitly: cover the compact support by uniform inverse neighborhoods;
uniqueness at w=0 and compact separation outside those neighborhoods exclude
a second preimage for small w. Patches can use a smooth partition; all its
terms sum exactly. The inverse needs no differentiation of q's membership
in P_L.

The floor mask is now the **fixed** r>0 mask, while q remains in the **fixed**
P_L. Long weights vanish on a neighborhood of ell=0; their smooth zero
extension removes the artificial inverse-domain endpoints. With a fixed
compact r interval larger than their support, the density of the w integral
is an integral over a fixed bounded q,n,r domain of a smooth function J.
Explicitly, J is the CT3 amplitude
`ell^3*sqrt(1-xi)*A(p)*chi(p)*A(q)*phi(q)*(1-psi(ell))/2`,
multiplied by the retained smooth support/phase-collar weights and divided by
`abs(det(d(r,w)/d(ell,xi)))`, all evaluated at the actual inverse. The collar
weight is one near w=0; its complement is retained below. This proves,
including the crease and all translated closing contacts,

```math
\begin{aligned}
D(w)&=D_0+D_1w+D_2w^2+O(w^3),&
D_j&=\frac1{j!}\int\partial_w^j J(q,n,r,0)\,dq\,dn\,dr,\\
\int_0^\infty w^j K(c\rho w^2)\,dw&=0\quad(j=0,1,2),&
\rho^{3/2}P^{\mathrm{long}}_{\chi,\phi}(\rho)&\longrightarrow0.
\end{aligned}\tag{CT5}
```

The O(w³) constant is finite by the proved inverse derivative bounds and
finite domain measure. Its normalized absolute response is O(rho^(-1/2)).
The remaining fixed-phase complement, including xi away from zero, is
exponentially small because ell>=delta/2 and h has a positive lower bound.
Polynomial tails outside the collar are kept in applying the signed moments.
Thus CT5 is an actual producer, not a desired density jet. In particular it
does not require a translated floor to meet C transversely at every long gap.

A sharp cutoff at delta is also legitimate without changing a conclusion:
write its short piece as the psi-short piece plus the signed band
(1_{ell<delta}-psi)P, and its long piece as the complementary difference.
Those band integrals cancel **exactly at finite density**. We do not assert
that either sharp band separately vanishes or omit its closing contacts.
The complete action uses one fixed delta throughout.

## 4. Short producer: actual corner transversality and critical remainder

We must now justify the short amplitude, not import CC's cone-ball proof.
On compact support the two defining functions of P_L are smooth with
independent differentials wherever both vanish. Their radii are at least a
on C, and L has no cone apex. At the floor, its differential is independent
of either null conormal. At Gamma its differential together with the two
null conormals is independent **exactly by CT1**. Interior floor points need
only its nonzero time derivative.

Here is an explicit local transport argument for the needed parameter
smoothness. Near a floor point choose corner coordinates consisting of the
active cone defining functions, F=t+H(x), and remaining smooth coordinates.
The ranks just checked make these coordinates invertible. In them the vector
field partial_F is tangent to every active cone face and has dF(partial_F)=1.
A finite smooth partition gives a field X tangent to each face near the floor
with dF(X)=1. For F_ell(q)=F(q-ell*u), this persists uniformly for small
signed ell, n in S2 and b=sqrt(1-xi) in [0,1]. The field
 -partial_ell(F_ell) X/dF_ell(X), supported near F_ell=0, transports that
level surface while preserving P_L and its crease. Its flow maps the two
sides of the floor to the corresponding sides. Outside the floor collar
there is no changing indicator. Compactness supplies a single delta for
all these parameters. This proves smooth moving-domain integrals with all
mixed ell/xi derivatives near xi=0; it also proves bounded ell derivatives
uniformly on the entire xi interval. It does not move a null face toward a
spacelike one, smooth the physical crease, or delete Gamma.

Let f=1_F, U0=A chi f and V0=A phi (these names are unrelated to region U).
For 0<Re(s)<1/2, direct Mellin inversion of CT3's short part gives

```math
\begin{aligned}
\widehat K(s)&=\Gamma(s)(1-2s)(1-s)(1-2s/3),\\
Z_\psi(s)&=\frac{c^{-s}}2\int_0^\infty
 \psi(\ell)\ell^{3-4s}\int_0^1\xi^{-2s}F_s(\ell,\xi)\,d\xi\,d\ell,\\
F_s(\ell,\xi)&=\sqrt{1-\xi}\int_{S^2}\int_{P_L}
 V_0(q)U_0(q-\ell u)h(q,\ell,\xi,n)^{-s}\,dq\,dn.
\end{aligned}\tag{CT6}
```

The transport just proved resolves the only moving indicator. Taylor in ell
through degree two, then subtract the xi Taylor polynomials through degree
two of those coefficients **and of the ell³ remainder**, in a fixed xi
collar. The latter remaining double integrand is bounded by a polynomial
in |s| times ell^(6-4 Re(s)) xi^(3-2 Re(s)); it is integrable for Re(s)<7/4.
Away from xi=0, sqrt(1-xi) is integrable and ell derivatives are bounded.
This continues Z_psi meromorphically to that strip. Its possible geometric
poles are the simple null poles 1/2,1,3/2 and diagonal poles 1,5/4,3/2,
with double poles at coincidences. The cutoff's transition annulus is away
from ell=0 and has only the simple null poles. No boundary constant is set
to zero before the kernel acts.

All continued expressions have polynomial vertical growth on closed substrips
away from poles: differentiating h^(-s) costs polynomials in s; h stays
positive and bounded; the finite Taylor denominators have the same bounds.
Gamma decay permits a contour shift to any fixed 3/2<s1<7/4. The retained
inverse integral is O(rho^(-s1)), hence o(rho^(-3/2)). This is the critical
**signed** remainder after matching, not a nonsummable fixed-ell expansion
integrated to the diagonal. No density-dependent cutoff enters this argument.

## 5. Derive the contact coefficient from physical interval moments

The rest-diamond means in CC7 are mean t²=1/60 and mean x_i x_j=delta_ij/30.
They apply to our identical physical affine diamond map, not to a flat
weighted-volume identity. Put D=u^alpha partial_alpha. They give
 h=A-ell DA/2+ell²(3 D²A/20-xi Box A/60)+O(ell³).
Multiplying U0(q-ell*u) and h^(-s), then averaging n, gives

```math
\begin{aligned}
F_s&=4\pi\sqrt{1-\xi}\left[T_0+\ell T_1+
 \ell^2\{X+(1-\xi)Y/3+\xi Z\}\right]+\ell^3 E_s,\\
T_0&=\int_{P_L}V_0 A^{-s}U_0,\\
T_1&=\int_{P_L}V_0 A^{-s}[-\partial_t U_0+sU_0\partial_t A/(2A)],\\
X-Y&=\int_{P_L}V_0 A^{-s}\left[
 \tfrac12\Box U_0-\frac{s}{2A}\partial U_0\cdot\partial A
 -\frac{3sU_0}{20A}\Box A
 +\frac{s(s+1)U_0}{8A^2}\partial A\cdot\partial A\right],\\
Z&=\frac{s}{60}\int_{P_L}V_0 A^{-s}\frac{U_0}{A}\Box A.
\end{aligned}\tag{CT7}
```

X and Y individually are obtained by replacing each Lorentzian contraction
in X-Y by, respectively, its time term and spatial Euclidean term. Derivatives
of f denote the actual moving-floor derivatives from §4. They are well-defined
on the corner domain because the floor is transverse to **every** stratum it
meets. The preceding transport, rather than a formal product of distributions,
justifies the differentiation and the remainder E_s.

The xi integral of the ell^0 and ell^1 coefficients is
B(1-2s,3/2). Its analytic continuation has a zero at s=5/4, cancelling the
candidate single-face divergence. Its simple null poles are killed by the
three actual kernel zeros. The coincident diagonal/null poles at 1 and 3/2
remain double in Z_psi. Since psi=1 near zero, their leading coefficients
are unchanged by its transition annulus. Directly, the xi coefficient of
order one in sqrt(1-xi) is -1/2; the order-two coefficient of the quadratic
bracket is Q2=(-X+Y-4Z)/8 at s=3/2. Consequently

```math
\begin{aligned}
Q_0&=\int_L\chi\phi\,d\mu_g,&
[(s-1)^{-2}]Z_\psi&=-\frac{\pi}{8c}Q_0,&\widehat K'(1)&=1/3,\\
[(s-3/2)^{-2}]Z_\psi&=\frac{\pi}{4c^{3/2}}Q_2,
 &\widehat K'(3/2)&=-\sqrt\pi/3,\\
P^{\mathrm{short}}_{\chi,\phi}(\rho)
 &=\frac{Q_0}{\rho}+\frac{\pi^{3/2}Q_2}{12c^{3/2}\rho^{3/2}}
       +o(\rho^{-3/2}),\\
\lim B_{\chi,\phi}&=-16Q_2=2(X-Y+4Z)\big|_{s=3/2}.
\end{aligned}\tag{CT8}
```

Rightward contour shifting subtracts residues. The double denominator
factors are 1/8, exactly as in CC9; C4*pi^(3/2)/(12*c^(3/2))=16.
The first term cancels the physical point **once**, not once per cone or
chart. CT5 supplies the long complement before the last line is concluded.
The matched remainder is the proved §4 remainder. This calculation retains
floor/crease contacts; the coefficient is not inferred from CC's limit.

## 6. Independent target, weighted generators and actual crease accounting

For phi=1 the substitution A=Omega⁴ in CT7–CT8 cancels the gradient-square
bulk terms and yields

```math
\begin{aligned}
\lim B_{\chi,1}
 &=3\int_L\chi\Omega\Box\Omega\,dq
   +\int_{P_L}\partial_\alpha
        \left(\Omega^2\partial^\alpha(\chi f)\right)dq,\\
\lim B_{1,1}
 &=3\int_L\Omega\Box\Omega\,dq
 +\sum_i\int_{i z<0}\Omega(-r_i,x)^2
   \delta(H(x)-r_i)(1-\nabla H\cdot\omega_i)\,dx
 =T_L.
\end{aligned}\tag{CT9}
```

Here omega_i=(x-c_i)/r_i. The divergence identity is Lorentzian. On each
smooth cone sheet the outward coordinate conormal is (1,omega_i), and its
contraction with df is precisely the displayed delta coefficient. In radial
coordinates around c_i, the simple root R_i has Jacobian
1-partial_r H>0; it cancels that factor and leaves CT2's independent induced
area, including its actual exposed angular domain.

There is no hidden edge mass in this use of Gauss. P_L is a Lipschitz domain
with a transverse two-face corner, so its distributional first boundary
derivative is the sum of its two hypersurface measures. It has no independent
codimension-two measure. Pairing with df is legitimate by the floor/stratum
ranks in §4. In local Gamma coordinates the delta pairing leaves a bounded
smooth density on each two-dimensional SN half-sheet; its mass within a
coordinate width epsilon of Gamma is O(epsilon). This justifies the flux
formula even at Gamma. It is an estimate on the **derived full coefficient**,
not a claim that a raw normalized action neighborhood is negligible. The
complete Mellin remainder already included that neighborhood. An auxiliary
smooth approximation to the step f can verify the distributional Gauss
identity in these same coordinates; it changes neither the physical region
nor any density limit and is not a spacelike-to-null argument.

For explicit generator accounting put mu=omega_z. On the i sheet of L,
 i*mu<0 and r_C=a/(-i*mu), and its retained generators have r_C<r<R_i when
that interval is nonempty. The source-weight formula is

```math
\begin{aligned}
\lim B_{\chi,1}
 &=3\int_L\chi\Omega\Box\Omega\,dq
 +\sum_i\int_{E_i^L}R_i^2\Omega_i(R_i)^2\chi_i(R_i)\,d\omega\\
 &\quad-\sum_i\int_{E_i^L}\int_{r_C}^{R_i}
                r^2\Omega_i(r)^2\chi_i'(r)\,dr\,d\omega,\\
-\int_{r_C}^{R_i}W_i\chi_i'\,dr
 &=-W_i(R_i)\chi_i(R_i)+W_i(r_C)\chi_i(r_C)
       +\int_{r_C}^{R_i}W_i'\chi_i\,dr,\\
\Omega_i(r)&=\Omega(-r,c_i+r\omega),\qquad W_i(r)=r^2\Omega_i(r)^2,\\
\chi_i'(r)&=(-\partial_t+\omega\cdot\nabla_x)\chi(-r,c_i+r\omega).
\end{aligned}\tag{CT10}
```

The lower endpoints are the actual crease, not a fictitious tip. Their
individual W_i(r_C) terms are generally nonzero, as are W_i' and weighted
floor endpoints. They must all be kept. For chi=1 the unsplit derivative
integral is zero; its integrated form cancels by the fundamental theorem
with both endpoints retained. Thus CT9 derives **no extra net C/Gamma term
for this class**. It neither assumes nor proves universal crease cancellation.
Smooth partitions have nonzero generator responses; their derivatives cancel
only in the full sum. The union's sheets have complementary radial intervals,
from their real tips to min(R_i,r_C), with r_C absent when i*mu>=0.

## 7. Complete union, both tips, ordered partitions and cutoffs

For p in E_+=M_+ minus M_- and q in E_-=M_- minus M_+, no causal relation
is possible in either direction: the later point's past cone would contain
the earlier point. For every other causal pair the common ambient interval
has the **same weighted physical volume** in each region that contains its
endpoints, by CT1's containment. Therefore the actual weighted point/pair
indicator identities, not a bilocal-additivity axiom, give

```math
\begin{aligned}
\mathcal A_\rho(U)&=\mathcal A_\rho(M_+)+\mathcal A_\rho(M_-)
                         -\mathcal A_\rho(L),\\
\lim_{\rho\to\infty}\mathcal A_\rho(U)
 &=T_{M_+}+T_{M_-}-T_L=T_U,\\
\sum_{j,k}P_{\chi_j,\phi_k}&=P_{1,1},&
\sum_{j,k}\int\chi_j\phi_k\,d\mu_g&=\mu_g(V),\\
S_\psi+N_\psi&=C_4\sqrt\rho\left[\mu_g(V)-\rho P_{1,1}\right].
\end{aligned}\tag{CT11}
```

For caps, the consumed CC theorem applies to H_i(y)=H(c_i+y): it is smooth,
globally lambda-Lipschitz, and H(c_i)>=H(0)-lambda*a>0; the translated Omega
is smooth positive on its full enclosure. These are the actual hypotheses,
not an issue-state inference. Both tips and their weighted generator fluxes
are retained by that complete CC proof; no old **flat** tip bound is asserted
in curvature. The lens has no tips. Common-to-exclusive pairs occur in the
cap terms and are not deleted. The same valuation holds for restrictions of
one finite configuration because interval containment preserves every layer
index, not for independent random configurations by fiat.

For any finite smooth endpoint partitions summing to one, every ordered
label pair occurs in CT11, including off-diagonal pairs. CT7 is bilinear in
U0,V0, so summing their actual coefficients restores CT9 and cancels all
partition derivatives. Point allocation is chi_j*phi_k on the diagonal,
whose **full** sum is one. S_psi contains that point once; N_psi contains only
the complementary pair integral. Sharp temporal masks use the exact band
conversion in §3, including both signs. A further artificial source or
radial cutoff must keep its complement and CT10's endpoint terms. None is
dropped by measure-zero, a shrinking cutoff, or a presumed local crease law.

## 8. Only afterward: original Poisson expectation

Each V=L,U is nonempty bounded Borel with finite positive atomless measure
A dq. The conformal ambient closed order is closed and the three-point
exclusive interval relation is Borel. The whole-diamond integral CT3 gives
the actual restricted interval rate by containment. Singletons, null cones
and boundary graphs have zero smooth volume without changing the discrete
closed order. Construct N with Poisson mean rho*mu_g(V), then N independent
positions with normalized restricted geometric measure; forget labels.
This is the original law and is almost surely simple.

The unchanged discrete bracket is N-L0+9L1-16L2+8L3, multiplied by
C4/sqrt(rho). Its absolute value is bounded by that constant times
N+16N(N-1). The finite second factorial moment proves integrability.
Reduced two-point Mecke and the **actual** exclusive interval count give

```math
\begin{aligned}
\mathbb E L_k&=\rho^2\int_{V\times V}\mathbf1_{p\preceq q,\ p\ne q}
 e^{-\rho V_g(p,q)}\frac{(\rho V_g(p,q))^k}{k!}
                    \,d\mu_g(p)d\mu_g(q),\\
\mathbb E A^{\mathrm{disc}}_{\rho,4}(V)
 &=\mathcal A_{\rho,4}(V)\longrightarrow T_V\qquad(V=L,U).
\end{aligned}\tag{CT12}
```

Both intensity factors, ordered endpoints and layer factorials yield precisely
K. The arrow applies CT9/CT11, already proved deterministically. It is not an
exchange with a sample-wise limit. #93/#137 supply checked generic foundations;
this geometric specialization and the new asymptotics are written only.

## 9. Acceptance, diagnostics and remaining scope

| #178 item | Delivery |
| --- | --- |
| Exact class, action, intervals, both measures, independent target | CT1–CT3, no axial restriction or flat weighted-volume substitution |
| Characteristic/closing producer and critical remainder | CT4–CT8; long uses floor/phase coordinates, short uses the actual regular corner ranks and matched subtraction |
| Complete L and U assembly, every stratum | CT9–CT11; derived flux, nonzero crease endpoints retained, actual CC hypotheses and weighted pair valuation |
| Expectation only after deterministic conclusion | CT12, actual law/order/volume/interval/integrability discharge |
| Adversarial regressions and precise parent ledger | `conformal_two_tip.py`, `test_conformal_two_tip.py`, and the #156 coverage ledger |

The diagnostic family has a floor varying in axial **and transverse** directions
and a density varying in space and time. Independent future-endpoint and
source/physical-partner-domain cubatures test complete finite-density actions;
interval-volume tests integrate the interior independently. Moving-floor
coefficient and generator/crease tests compare with independent geometry.
Finite cubature, symbolic identities and refinement are diagnostics, not
certified asymptotic remainder bounds. The proof of those bounds is §§3–5.

**Exact gain:** the whole regular two-tip conformal 4D class CT1, not only
TT1 and not all of #156. General regular SN/NN fronts, tangential floor/crease
contacts, three or more future tips, other curved dimensions/metrics,
generator cut/caustic contacts and other required higher intersections remain
#156. Noncompact/degenerating/rate/sample-wise and timelike work retains its
original deferred/separate status. #81/#24 and #94/#86 remain open.

No Lean-affecting input changes; no new compiled theorem or fresh Lean audit
is claimed. Local repository checks, live GitHub math rendering, exact-head
CI and one bounded feedback pass are delivery evidence, not independent human
acceptance. No agent launch, merge, deployment, issue closure or changed
observable, target, order, law or parent contract.
