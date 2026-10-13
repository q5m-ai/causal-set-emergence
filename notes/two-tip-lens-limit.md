# Actual intersection-lens producer TT-A (#154)

**Written deterministic proof for the selected fixed flat 4D lens.** The full
canonical action tends to its independently defined SN screen area. This is
not a new Lean theorem, independent human review, or a theorem for arbitrary
null boundaries. Refs #154, #134, #81, #24; #155 owns the union/expectation
consumer and #156 owns the required wider coverage.

Source receipt: integration base
`41cf2c35378cf91c1c2d3651f8dd689370662bdf`; the actual inputs are
[#134 TT1–TT11](two-tip-null-feasibility.md),
[#83 NM1–NM12](null-mixed-estimates.md), and
[#84 MA1–MA15](null-mixed-assembly.md). Their verification levels are unchanged.
No spacelike theorem is applied to a null face; no smoothing or geometric
limit is used. The reduction exploits the **actual axial floor**, not a flat
replacement for it.

## 1. Statement, geometry and unchanged normalization

Keep exactly TT1: signature (+---), ordinary four-volume, ambient closed
causal order, the isolated restricted intervals, and

```math
\begin{aligned}
a&=1/2,& b&=1/10,& H(z)&=1+b\sin z,& d(z)&=a+|z|,\\
L&=\{(t,z,w):-H(z)\lt t\lt-\sqrt{d(z)^2+|w|^2}\},\\
c&=\pi/24,& C_4&=4/\sqrt6,&
K(v)&=(1-9v+8v^2-4v^3/3)e^{-v},\\
\mathcal A_\rho(L)&=C_4\sqrt\rho\left[|L|-\rho
 \int_L\int_{L\cap J^+(p)}K(c\rho\sigma(p,q)^2)\,dq\,dp\right],\\
\sigma(p,q)&=(q_t-p_t)^2-|q_x-p_x|^2.
\end{aligned}
\tag{LA1}
```

TT1's future-set/past-set proof establishes closed ambient interval
containment, so the actual interval volume is the flat value in (LA1). L is
nonempty, open, bounded and has compact closure. Its boundary consists of the
smooth spacelike floor, two complementary null-cone sheets, their SN pieces,
the same-side null crease C and its boundary circle Gamma. **L has no tips.**
U has the two tips, handled by TT-B and TT5's cap identity. C is a spacelike
disk, not a past–future NN joint; its center is not a third tip. These are
required null/mixed strata of #90 §4, not members of the smooth G-SS core.

Let Z be the open interval where H(z)>d(z). Its endpoints are nonzero,
unique, and transverse because |H'| is at most b<1. The independent SN area
in TT2 can equivalently be written

```math
\begin{aligned}
J_L&=2\pi\int_Z [H(z)-d(z)d'(z)H'(z)]\,dz,\\
\lim_{\rho\to\infty}\mathcal A_\rho(L)&=J_L.
\end{aligned}
\tag{LA2}
```

The second line is the theorem to be proved, not admissibility. In the first
line d' is used only away from zero. On each sheet, parameterize the joint by
z and azimuth with transverse radius r satisfying r²=H²-d². Its positive
Gram determinant has square root H-dd'H', strictly positive since H>d and
|H'|<1. The two endpoints and Gamma have zero area for **this geometric
integral**. Section 5 proves the complete action conclusion without deleting
any of their normalized neighborhoods. This identifies (LA2) with TT2, not an
action-defined target.

## 2. Exact overlap: both measures and every partner

Write a future displacement as k=(tau,xi,eta), with eta in two transverse
spatial dimensions. Put F={t+H(z)>0} and P=I⁻(v+) intersect I⁻(v-). For a
causal k, the future-set and past-set properties give the exact equivalence

```math
\begin{aligned}
p\in L,\ p+k\in L
 &\quad\Longleftrightarrow\quad p\in F,\ p+k\in P,\\
f(\tau,\xi)&=|L\cap(L-k)|
 =\int_{\mathbb R}\Phi(H(y-\xi)-\tau,d(y))\,dy,\\
\Phi(B,d)&=\frac\pi3(B-d)_+^2(B+2d).
\end{aligned}
\tag{LA3}
```

The formula for Phi is used with d>0 and is zero when B<=d. To prove it,
translate the source spatial coordinates to y=z+xi and v=w+eta. The allowed
time interval has length
`(H(y-xi)-tau-sqrt(d(y)^2+|v|^2))_+`. Integrating it with the **source**
measure `2*pi*r dr dy` gives Phi. This change of variables has Jacobian one;
`dp dq = dp dk` retains both endpoint measures. There is no transverse
translation in H, which is why f is independent of eta. The nonconstant
H(y-xi) is retained, not replaced by H(y), H(0), or a density-dependent floor.
Every source-dependent floor cutoff in TT7 is present in this integration.

The active y interval exists exactly when H(-xi)-tau>a. On y>0 and y<0
its two endpoints solve H(y-xi)-tau=a+|y|; the y derivatives have absolute
value at least 1-b. This is the moving **floor/crease contact**, with closing
height h=H(-xi)-tau-a. The crease stays at y=0 in these translated coordinates;
its contact with the floor is the translated Gamma condition h=0. Nothing
has been omitted because a boundary has zero four-volume.

At each fixed positive density, compact domination justifies all changes of
variables and Fubini, including signed integrands. Transverse displacement
integration and then null coordinates give

```math
\begin{aligned}
I_\rho&=\int_L\int_{L\cap J^+(p)}K(c\rho\sigma^2)\,dq\,dp\\
 &=\pi\int_0^\infty\int_{-\tau}^{\tau} f(\tau,\xi)
       \int_0^{\tau^2-\xi^2}K(c\rho s^2)\,ds\,d\xi\,d\tau\\
 &=\int_0^\infty K(c\rho s^2)D(s)\,ds,\\
F_0(\alpha,\beta)&=f((\alpha+\beta)/2,(\alpha-\beta)/2),\\
D(s)&=\frac\pi2\int_{\alpha,\beta\ge0,\ \alpha\beta\ge s}
                      F_0(\alpha,\beta)\,d\alpha\,d\beta.
\end{aligned}
\tag{LA4}
```

Here s is the actual proper-time squared of the displacement, not its spatial
or time length. Macroscopic nearly-null partners are included along both
axes of the quadrant. No assertion that a long sector separately vanishes
is needed or made. The numerical displacement parameterization xi=tau*mu
has its actual upper time endpoint determined by
`tau+a=H(-tau*mu)`, independently for every mu; it must not be flattened.

## 3. Derived regularity, including closing contacts

We need a property of the actual overlap, not an assumed transverse jet.
For tau>=0 and |xi|<=tau, f is supported in tau<=1+b-a. Thus F0 has compact
support in a fixed square [0,B]²; choose B strictly larger than 2(1+b-a).
The same formula defines f near this causal quadrant.

Where h>0, split the integral in (LA3) at y=0. Both roots are smooth by the
implicit function theorem, and the integrands are smooth on each half.
Consequently f is smooth there, in particular on a neighborhood of (0,0).
At h=0 the interval closes at the crease. The root distances are at most
h/(1-b). On it, B-d is at most h and B,d and their parameter derivatives are
bounded on the fixed compact support. Phi vanishes quadratically and its
first derivative in B vanishes at B=d. Differentiating the integral twice
therefore introduces **no dropped endpoint term**: the first boundary term
has Phi=0 and the second has Phi_B=0. Its remaining second derivative is an
integral over an interval of length O(h). Uniformly on the compact parameter
set, derivatives of total order j<=2 are O(h^(3-j)). They extend continuously
by zero to h<=0. Hence F0 is C² on the quadrant, smooth near its origin.
Third derivatives can jump at closing contacts; none is presumed continuous.

This proof treats all translated Gamma contacts and the same-side crease.
It does not infer C² from smoothness of the individual null sheets, nor
assume a positive lower bound for their shrinking overlap width.

## 4. Quadrant pushforward lemma, with its full boundary terms

**Lemma.** If F is C² on a fixed square [0,B]², smooth near (0,0), and zero
near its outer edges, define D as in (LA4). Then finite constants A1,A2 exist
such that, as s decreases to zero,

```math
\begin{aligned}
D(s)&=D(0)+A_1s+\frac\pi2F(0,0)s\log s
       +A_2s^2+\frac\pi4F_{\alpha\beta}(0,0)s^2\log s+o(s^2).
\end{aligned}
\tag{LA5}
```

All constants and remainders refer to the full square, not just an origin
sector. Here is a direct proof. For positive alpha,beta write

```math
\begin{aligned}
G(\alpha,\beta)&=
 \frac{F(\alpha,\beta)-F(\alpha,0)-F(0,\beta)+F(0,0)}{\alpha\beta}
 =\int_0^1\int_0^1F_{\alpha\beta}(u\alpha,v\beta)\,du\,dv,\\
H_F(s)&=\int_{s/B}^B F(\alpha,s/\alpha)\,\frac{d\alpha}{\alpha},
 &D'(s)&=-\frac\pi2 H_F(s),\\
H_F(s)&=\int_{s/B}^B\frac{F(\alpha,0)}\alpha\,d\alpha
 +\int_{s/B}^B\frac{F(0,\beta)}\beta\,d\beta
 -F(0,0)\log(B^2/s)+sH_G(s).
\end{aligned}
\tag{LA6}
```

G extends continuously to the axes and is smooth near the origin. For any
such function G,

```math
\begin{aligned}
H_G(s)&=G(0,0)\log(B^2/s)+B_G+o(1),\\
B_G&=\int_0^B\frac{G(\alpha,0)-G(0,0)}\alpha\,d\alpha
 +\int_0^B\frac{G(0,\beta)-G(0,0)}\beta\,d\beta.
\end{aligned}
\tag{LA7}
```

To verify the error, split the hyperbola into alpha>=delta, beta>=delta,
and the remaining square, with fixed positive delta inside the smooth
neighborhood. On the first two pieces uniform continuity and dominated
convergence give the corresponding axis integrals. Inside the square the
bound `|G(alpha,beta)-G(0,0)| <= C*(alpha+beta)` makes both the hyperbola and
axis errors at most a constant times delta. First take s to zero, then delta
to zero. This establishes (LA7); it is not a density-dependent cutoff.

Expand each axis integral in (LA6) at its **lower moving endpoint s/B**.
Their exact retained terms give
`H_F(s)=-F(0,0)*log(s)+A+s*(-F_ab(0,0)*log(s)+B1)+o(s)`.
The finite constants A and B1 contain both axis integrals, outer-edge terms,
and the linear Taylor terms at s/B. Integrating D' from zero to s proves
(LA5). In particular D(0), A1 and A2 are not set to zero; they encode the
long partners and closing contacts. They disappear only under the actual
signed moments in the next section. This also proves existence of the
little-o remainder rather than putting it in the lens hypotheses.

## 5. Complete action, point-once cancellation and target identification

For real q>-1, elementary Gaussian integration gives the Mellin identity
and its two required derivatives:

```math
\begin{aligned}
M(q)&=\int_0^\infty u^qK(u^2)\,du
 =-\frac{q(q-1)(q-2)}{12}\Gamma((q+1)/2),\\
M(0)&=M(1)=M(2)=0,& M'(1)&=1/12,&M'(2)&=-\sqrt\pi/12.
\end{aligned}
\tag{LA8}
```

Differentiation is justified by Gaussian domination with a logarithm, both
at zero and infinity. These are signed identities for the unchanged kernel.
With lambda=sqrt(c*rho), the s log(s) integral is 1/(12 lambda²), and the
s² log(s) integral is -sqrt(pi)/(12 lambda³). Substitution of the **derived**
(LA5) into the entire (LA4) therefore gives

```math
\begin{aligned}
I_\rho&=\frac{F_0(0,0)}\rho
 -\frac{\pi\sqrt\pi}{48(c\rho)^{3/2}}
                  (F_0)_{\alpha\beta}(0,0)+o(\rho^{-3/2}),\\
\mathcal A_\rho(L)&\longrightarrow
 4(F_0)_{\alpha\beta}(0,0)
 =f_{\tau\tau}(0,0)-f_{\xi\xi}(0,0).
\end{aligned}
\tag{LA9}
```

For completeness, the remainder step uses a **fixed** s0>0: on (0,s0),
its absolute value is at most epsilon*s² once s0 is sufficiently small.
The normalized integral is bounded by epsilon times the finite absolute
second Gaussian moment. On s>=s0 the actual compactly supported D, and the
polynomial/log comparison terms extended to infinity, have exponentially
small normalized integrals. Take density to infinity first, then epsilon
to zero. No shrinking-cutoff hypothesis, raw bilocal absolute estimate or
uncontrolled asymptotic differentiation is used.

Since F0(0,0)=f(0,0)=|L|, the first term of (LA9) cancels exactly the physical
point term in (LA1), **once**. The factors pi/2, pi/4 and C4 are essential:
`C4*pi*sqrt(pi)/(48*c^(3/2))=4`. Losing a measure, taking unordered pairs, or
using a single cap in place of the lens changes this computation.

Differentiating the actual (LA3), using the proved vanishing endpoint terms,
now gives

```math
\begin{aligned}
f_{\tau\tau}(0,0)-f_{\xi\xi}(0,0)
 &=\int_Z\left[2\pi H(1-(H')^2)-\pi(H^2-d^2)H''\right]dz\\
 &=2\pi\int_Z[H-dd'H']\,dz
   -\int_Z\frac{d}{dz}\left[\pi(H^2-d^2)H'\right]dz
 =J_L.
\end{aligned}
\tag{LA10}
```

At each outer endpoint H=d, so its flux is zero. Splitting Z at the crease
z=0 retains **both** one-sided fluxes; their values agree since H²-d² and H'
are continuous, and their signs are opposite. They cancel, not vanish
separately (H'(0)=b is nonzero). Equations (LA3)–(LA10) evaluated the complete
lens action, including every closing contact. Thus no extra **net** C/Gamma
coefficient is needed for this selected target. We do not assert that each
arbitrarily source-localized crease/corner observable tends to zero: #83
already shows why such attribution can be false.

This proves (LA2). It is a positive result, not an obstruction inferred from
a failed bound or an isolated sector. No additional coefficient has been
fitted to the target.

## 6. Exact partitions and usable TT-B signature

For bounded source weights with a finite sum equal to one, the original
point and bilocal integrals sum exactly. A partner partition must retain
all ordered index pairs, with partners in the **original** lens. At any
positive density and for any measurable cutoff chi(p,q) between zero and
one, including source-dependent cutoffs, TT9 gives exactly S+N=A. The point
term belongs to S only. Our proof evaluates this sum without estimating N
separately. A translated weighted overlap would still integrate the actual
source weight at p, not at p+k; no weighted limit is claimed from (LA9).

For artificial radial, source or displacement boundaries, apply the identity
before any limit; retain both complements. The fixed square boundary and
moving hyperbola endpoints used analytically above are explicitly in
(LA6)–(LA7). The floor-Hessian flux in (LA10), including its crease values,
is likewise indispensable. There is no hidden limit taking a or b to zero,
turning a spacelike face null, or shrinking a partner cutoff with density.

**TT-B input (now proved in writing):** for exactly TT1's fixed L, with TT3's
original all-partner action and independent TT2 target, at every positive
density the identities (LA3)–(LA4) hold, and
`A_rho(L)-J_L -> 0`. No jet, long estimate or expectation premise is added.
Combine this with the accepted translated #84 theorems
`A_rho(M_i)-S_i -> 0`, and the exact TT2/TT5/TT11 identities, retaining the
point allocation, both tips and every ordered partner. This is sufficient
to prove the deterministic U conclusion. Only **afterward** specialize the
original-law finite-density Poisson equality; that is the separate #155 task.
The source must be pinned to the delivered TT-A commit, not an issue state.

## 7. Acceptance and verification crosswalk

| #154 requirement | Evidence / boundary |
| --- | --- |
| Actual selected geometry, action, order, both measures, independent target | TT1–TT3 unchanged; (LA1)–(LA4) and induced-area calculation |
| All long partners, moving floor/crease/Gamma contacts | Exact full overlap (LA3)–(LA4), C² closing-contact proof in §3; no boundary neighborhood deleted |
| Derived jets/cancellations, every endpoint | Proved pushforward (LA5)–(LA7), signed moments (LA8), point restoration (LA9), two-sided flux (LA10) |
| Complete deterministic conclusion | (LA2), proved by (LA9)–(LA10); no extra net coefficient; no sector-based counterexample |
| Asymmetric/nonplanar and finite-density regressions | `two_tip_lens.py`, `test_two_tip_lens.py`; selected b=1/10 retained, independent area/volume and partition negative controls |
| Precise TT-B handoff | §6; expectation and U assembly remain separate; wider quantified coverage remains #156 |

Run the focused tests, `check_symbolic.py`, full Python suite, `reproduce.py`,
Markdown lint and its regression tests. Executable quadratures and finite
samples diagnose formulas, not quantified error bounds. No Lean, checker,
dependency or build inputs change: no new Lean audit or compiled analytic
producer is claimed. Existing checked interval/probability results keep their
original scope. Independent mathematical/physical scrutiny remains #94/#86;
GitHub CI and one bounded feedback snapshot are separate delivery evidence.
