# Curved sharp-cutoff contacts: a signed domination obstruction (#74)

**Partial delivery; #74 stays open.** On the fixed polynomial-density pilot,
this note gives the actual phase-straightened short/long amplitudes, the active
moving-contact coefficients, and a conventional proof that a density-uniform
integrable **first-endpoint** bound for the uncorrected signed long sector is
impossible. The obstruction already occurs with a planar future face. It is
not a counterexample to the complete action limit, nor a proof that a nonlocal
term survives after integration. It requires changing the proposed order of
averaging and domination, not changing geometric admissibility.

The corrected successor contracts below are **open**. In particular, neither
the actual short remainder nor the independently identified half-curvature
bulk theorem is proved here. Symbolic certificates and numerical regressions
are separate from the written arguments. No new Lean theorem or independent
human mathematical review is claimed.

## 1. Fixed class, canonical API and conventions

Start from integrated `main` at
`f5bea9bf756cdc3ab1136dc4204e2960b0e9db74`. The #93 API files
`ConformalAction.lean`, `ConformalGeometry.lean`, and `FiniteMeasureBDG.lean`
are unchanged from its audited candidate
`9aed02c70f01c9fd4c5d14e5e4b1024d94f8367f`. [PR #101](https://github.com/q5m-ai/causal-set-emergence/pull/101)
records the full 187-source and aggregate audit of that candidate. This is an
API/source comparison, **not a new audit of all current Lean sources**.

Use exactly the original `AdmissibleTwoFace h f` region, with its C³ germs,
compact positive-height closure, joint nondegeneracy and strict slope budget.
The lower causal envelope is `f - max 0 h`; the upper is `f`. Fix
`Omega(t) = (1+t^2)^(1/4)`, not an arbitrary smooth factor. All geometry,
weights and positive cutoffs are independent of density. On a fixed compact
time slab containing the region and its causal intervals, put:

```math
q(t)=1+t^2,\qquad 1\leq q\leq Q=1+T_*^2,\qquad d\mu_g=q(t)\,d^4x.
\tag{R1}
```

The factor is globally smooth, positive and measurable, and bounded on an
open neighborhood of the compact closure. Thus it meets #93's unchanged
`ControlledConformalFactor` contract. The bounds on its density derivatives
are explicit: the first is at most twice the slab radius, the second is two,
and all higher derivatives vanish. The density is not a curvature expansion.

The observable is `BoundaryDraft.conformalAction`, expanded by
`conformalAction_eq_integral`. Causal convexity and
`ControlledConformalFactor.intervalVolume_ambient` identify the actual
restricted volume with the ambient interval integral for region endpoints.
The closed causal order, null partners, and exclusive selected endpoints are
unchanged; atomlessness permits endpoint removal only in the volume integral.
The signature is `(+---)` and time increases toward the future. The curvature
convention is exactly [#73, (C4)](curved-bulk-pilot.md#2-curvature-convention-fixed-before-the-coefficient-calculation),
opposite to #93's independent example convention:

```math
R=\frac{3(1-t^2/2)}{(1+t^2)^{5/2}},\qquad
R_{93}=-R,\qquad C=\frac4{\sqrt6},\qquad c=\frac\pi{24}.
\tag{R2}
```

The candidate bulk integral remains one half of this independently calculated
scalar curvature against metric volume. It is not defined by the action.
The finite-density probability bridge belongs to #93 and is not rederived or
used to prove any estimate below.

## 2. Exact amplitudes, not a translated-overlap substitution

Write the first endpoint as $`x=(t,z)`$, and the second as
$`y=(t+(u+v)/2,z+(v-u)n/2)`$, with $`n\in S^2`$ and
$`0\leq u\leq v`$. Sphere measure has total mass $`4\pi`$; the coordinate
Jacobian is $`(v-u)^2/8`$. The exact interval identity (C9) gives

```math
\begin{aligned}
V(x,y)&=c u^2v^2H(t,u,v),\\
H&=1+t^2+\tfrac12t(u+v)+\tfrac3{40}(u+v)^2-\tfrac1{30}uv,\\
H&=1+\left(t+\tfrac{u+v}{4}\right)^2
       +\frac{3u^2-2uv+3v^2}{240},\\
2H+uH_u&=2+2\left(t+\tfrac{3u}{8}+\tfrac v4\right)^2
       +\frac{3u^2-4uv+4v^2}{160}.
\end{aligned}\tag{R3}
```

Both final quadratic forms are nonnegative: their numerators are respectively
$`2u^2+2v^2+(u-v)^2`$ and $`u^2+2(u-v)^2+2v^2`$.
Consequently the following phase change is globally increasing in nonnegative
$`u`$ for every positive $`v`$, not just in a formal null jet:

```math
\begin{aligned}
w=F(t,u,v)&=uv\sqrt H,\qquad \rho V=c\rho w^2,\\
F_u&=\frac{v(2H+uH_u)}{2\sqrt H}\geq\frac v{\sqrt H}>0.
\end{aligned}\tag{R4}
```

It starts at zero and tends to infinity. Its inverse $`u=U(t,v,w)`$ is smooth
up to zero by the inverse function theorem, locally extending across zero.
On actual region pairs, $`1\leq H\leq Q`$ because it is the average of the
actual density on a contained interval. For the long sector this gives
$`F_u\geq\delta/\sqrt Q`$. We never freeze the phase at $`q(t)`$.

The lower envelope is a future epigraph, as proved in
`StrictGraphLipschitz.epigraph_future`. For a first endpoint in the region,
the lower condition for every causal partner is automatic. Hence, with

```math
\begin{aligned}
G(x,n,v,w)&=f\left(z+\tfrac{v-U(t,v,w)}2n\right)
                 -t-\tfrac{v+U(t,v,w)}2,\\
A_\phi(x,n,v,w)&=
 \frac{q(t+(U+v)/2)\,\phi(y)\,(v-U)^2}{8F_u(t,U,v)},\\
B_x^\geq(w;\phi)&=\int_{S^2}\int_\delta^D
 \mathbf1_{\{U\leq v\}}\mathbf1_{\{G>0\}}A_\phi\,dv\,dS(n),\\
B_x^<(w;\phi)&=\int_{S^2}\int_0^\delta
 \mathbf1_{\{U\leq v\}}\mathbf1_{\{G>0\}}A_\phi\,dv\,dS(n).
\end{aligned}\tag{R5}
```

Here $`D>\delta`$ is a fixed upper bound for all possible null exit parameters
and causal pairs of the bounded region. Strict upper slope makes the null
exit finite, uniformly on its compact closure. Values at $`v=0`$ may be set
to zero; they are measure-null coordinate values, not removed discrete
partners. There is no second-endpoint chart restriction. Take $`\phi=1`$ for
the production action; a smooth endpoint field is diagnostic notation only.

The first endpoint measure is **outside** this amplitude. For a bounded
first-endpoint weight $`\chi`$ define

```math
\begin{aligned}
P_\chi^\bullet(\rho;\phi)
 &=\int_M\chi(x)\int_0^\infty K(c\rho w^2)B_x^\bullet(w;\phi)\,dw\,d\mu_g(x),\\
S_{\chi,\phi}&=C\sqrt\rho\int_M\chi\phi\,d\mu_g
                    -C\rho^{3/2}P_\chi^<(\rho;\phi),\\
L_{\chi,\phi}&=-C\rho^{3/2}P_\chi^\geq(\rho;\phi).
\end{aligned}\tag{R6}
```

These are components of the existing integral, not new production actions.
At every positive density, its proved signed integrability, followed by polar
coordinates and (R4), justifies Fubini and this change of variables. For bounded
fields the same compact domination applies. On the active domain,
$`|A_\phi|\leq Q^{3/2}\|\phi\|_\infty v/8`$; amplitudes are bounded and
have common compact phase support. This is a **finite-density** bound, not a
bound after multiplying by the growing normalization.

For any finite smooth first-endpoint partition with sum one on the region,
including overlapping or signed weights,

```math
A_g(\rho,M)=\sum_i(S_{\chi_i,1}+L_{\chi_i,1}).\tag{R7}
```

The point term occurs exactly once, in the short part. Equality at the sharp
cutoff belongs to the long part; changing a measure-null integration endpoint
does not change this convention. This is the same (C19) decomposition for
#74, #75 and #76, and it retains every causal partner and both metric measures.

## 3. Moving contacts of the actual long amplitude

At zero phase the upper exit $`r_0(x,n)`$ is the unique root of
$`f(z+vn/2)-t-v/2=0`$. If it exceeds the cutoff, the original null segment
has a strictly active interval. Its exit lies in the positive-height interior
of the spatial region: the strict lower slope and positive separation give
positive clearance above the lower face even at the upper exit. Thus the
original C³ germs apply there, without any exterior regularity assumption.

For each strictly active fibre and sufficiently small phase, the exit is a
C³ function $`r(w)>\delta`$. The inverse satisfies $`U\leq w/v`$; on
$`w<\delta^2/2`$ the causal constraint $`U\leq v`$ is automatic in the long
integral. Write $`G`$ as in (R5) and evaluate root derivatives at
$`(w,v)=(0,r_0)`$:

```math
\begin{aligned}
G_v&=\tfrac12(Df[n]-1)<0,\qquad
G_w=-\tfrac12(1+Df[n])U_w<0,\\
r_1&=-G_w/G_v,\\
r_2&=-\bigl(G_{ww}+2G_{wv}r_1+G_{vv}r_1^2\bigr)/G_v.
\end{aligned}\tag{R8}
```

In particular the exit moves toward the cutoff. Increasing $`u`$ decreases
the gap even without differentiability, by the strict global Lipschitz bound
on the upper envelope. Hence negative and exact-cutoff contacts never open on
the right: their amplitude and all right coefficients are zero.

For a strictly active fibre, put $`A=A_\phi`$ and integrate only in $`v`$.
Leibniz' rule gives its actual right Taylor coefficients:

```math
\begin{aligned}
b_0&=\int_\delta^{r_0}A(0,v)\,dv,\\
b_1&=\int_\delta^{r_0}A_w(0,v)\,dv+A(0,r_0)r_1,\\
b_2&=\frac12\left[\int_\delta^{r_0}A_{ww}(0,v)\,dv
 +2A_w(0,r_0)r_1+A_v(0,r_0)r_1^2+A(0,r_0)r_2\right].
\end{aligned}\tag{R9}
```

The last line is a **coefficient**, not the second derivative. All Jacobian,
phase, field and boundary-velocity derivatives remain. The boundary amplitude
does not vanish: integrating only the smooth interior would already miss a
first-order term. Formula (R9) must not be applied at exact cutoff contact.
Its neighbourhood can shrink as the active exit approaches the cutoff.

This differs from the flat *time-integrated hinge* in `LONG_NULL_GAP.md`, whose
integrand vanishes at its moving root. The flat proof's integrable remainder
bound is after that extra integration, not on the raw first-spacetime-endpoint
fibres (R5). The next example shows why that distinction is essential.

## 4. Two obstructions on the actual fixed curved pilot

Use the original nonvacuous example (C2):

```math
f=\tfrac18,\qquad h(z)=\tfrac14(1-|z|^2),\qquad
M=\{(t,z): |z|^2/4-1/8\lt t\lt1/8\},\qquad
\delta=\tfrac1{32}.
\tag{R10}
```

Its original slope, face and joint margins are unchanged. Its scalar curvature
is nonzero throughout the closure. Put
$`t_*=f-\delta/2=7/64`$ and $`a=2(f-t)-\delta`$.
Take $`0<a\leq\delta/2`$ and any $`|z|<1/4`$. These first endpoints are
strictly in the original region. Their **entire** long future is exactly

```math
n\in S^2,\qquad \delta\leq v<\delta+a,\qquad
0\leq u<\delta+a-v.\tag{R11}
```

Indeed the future plane imposes $`u+v<2(f-t)`$, the lower condition is
automatic by the causal epigraph, and $`u<v`$ follows from $`a<\delta`$.
This is not a selected positive sub-sector of an otherwise signed integral.
It contains all long partners of each such first endpoint.

### 4.1 No integrable quadratic-remainder dominator before endpoint averaging

For the complete sphere-integrated amplitude with $`\phi=1`$, define

```math
k_*=\delta\sqrt{H(t_*,0,\delta)},\qquad
A_*=\frac{\pi\delta q(f)}{2\sqrt{H(t_*,0,\delta)}}>0.
\tag{R12}
```

Smooth inverse/exit Taylor expansion on a fixed neighbourhood of this planar
contact, including its moving endpoint, gives for each bounded nonnegative
$`\lambda`$ as $`a\downarrow0`$:

```math
\begin{aligned}
B_t^\geq(k_*a\lambda;1)&=A_*a(1-\lambda)_++O(a^2),\\
b_0(t)&=A_*a+O(a^2),\qquad
b_1(t)=-A_*/k_*+O(a),\qquad b_2(t)=O(1).
\end{aligned}\tag{R13}
```

For completeness, along the upper plane solve
$`F(t,\delta+a-v,v)=w`$. At the contact its derivative in $`v`$ is
$`-k_*`$, so its smooth root is
$`\delta+a-w/k_*+O((a+w)^2)`$. The angularly integrated smooth amplitude
is $`A_*+O(a+w+|v-\delta|)`$. Integrate over the positive length between the
cutoff and this root to obtain the first line. Applying (R9) on the active
side yields the remaining lines; the root and amplitude derivatives are
bounded on this fixed neighbourhood. No uniform active root-to-cutoff
distance has been assumed.

At $`w=2k_*a`$ the actual fibre is closed for sufficiently small positive
$`a`$, while the polynomial extrapolation is not. Thus

```math
\frac{B_t^\geq(w;1)-b_0(t)-b_1(t)w-b_2(t)w^2}{w^2}
 =\frac{A_*}{4k_*^2a}+O(1).\tag{R14}
```

Any bound on the absolute normalized quadratic remainder, valid on a common
positive phase interval and before first-endpoint integration, must dominate
a positive multiple of $`1/a`$ on a positive spatial ball. Metric volume is
bounded below by Lebesgue volume, and $`|dt|=da/2`$, so such a bound is not
integrable. Almost-everywhere qualifications do not remove a whole interval
of approaching contacts. This disproves a **particular dominated-jet route**,
not the existence of an averaged right quadratic jet.

### 4.2 Even the normalized signed long sector has no such dominator

A more direct obstruction does not subtract any jet. Let
$`\epsilon=1/100`$, use the valid slab bound $`Q=2`$, and for the endpoints
in (R11) probe the density

```math
\rho_a=\frac{\epsilon}{cQ a^2(\delta+a)^2}.\tag{R15}
```

Every one of their long partners then has $`0\leq\rho_a V\leq\epsilon`$,
because $`u\leq a`$, $`v\leq\delta+a`$, and $`H\leq Q`$. The **original
signed kernel** is at least one half throughout that band: its polynomial is
at least $`1-9z-4z^3/3`$, and $`e^{-z}\geq1-z`$ there. The product of
these decreasing positive lower bounds at one hundredth exceeds one half.
There are no other long partners on which negative kernel values could cancel.

Direct integration of the coordinate Jacobian over the full triangle gives

```math
\begin{aligned}
\int_{S^2}\int_\delta^{\delta+a}\int_0^{\delta+a-v}
 \frac{(v-u)^2}{8}\,du\,dv\,dS
 &=\frac{\pi a^2(a^2+6\delta^2)}{24}
 \geq\frac{\pi\delta^2a^2}{4},\\
I_\geq(\rho_a,x)
 :=\int_{M\cap J^+(x),\ v\geq\delta}K(\rho_a V)\,d\mu_g(y)
 &\geq\frac{\pi\delta^2a^2}{8},\\
C\rho_a^{3/2}I_\geq(\rho_a,x)&\geq\frac{\Gamma}{a},\qquad
\Gamma=\frac{C\pi\epsilon^{3/2}}{27c^{3/2}Q^{3/2}\delta}>0.
\end{aligned}\tag{R16}
```

The last inequality uses $`\delta+a\leq3\delta/2`$. Both density factors
are respected: the inner one is at least one; the outer measure is still
$`d\mu_g(x)`$. Multiplying by its density cannot cure the divergence.

It follows that for **every** fixed lower density threshold there is no
$`E\in L^1(M,\mu_g)`$ dominating the absolute value of the normalized signed
long fibre for all larger densities. The parameter $`a`$ ranges over first
endpoints of a single fixed geometry; (R15) tests a supremum over density,
not a family of density-dependent regions or cutoffs. If domination is stated
a.e. separately for each density, continuity of the finite-density integral
in density and a countable dense set give the same contradiction.

The sign of the long action is negative by (R6). This result concerns the
magnitude of that **signed integral**, not an integral of the absolute kernel.
It is stronger than the earlier (C23) obstruction to absolute domination.
It still says nothing about the limiting *outer integral*: cancellation can
occur between approaching-contact first endpoints. In particular, (R16) is
not a lower bound for the full long integral or complete normalized action.
A first-endpoint weight bounded below on this contact layer inherits the
obstruction; a partition does not automatically remove it.

## 5. Corrected common output and still-open short obligation

### Average the contacts, or subtract and explicitly restore their layer

The raw first-endpoint dominated-convergence contract must be replaced. A
possible corrected route is to integrate in first-endpoint time (or a proved
contact/coarea coordinate) **before** applying a quadratic-jet domination
lemma. Equivalently, isolate the actual contact layer, prove its signed
contribution, and restore it in the common short/long accounting. No boundary
term is to be declared zero by hypothesis. The positive-part toy identity

```math
\int_0^A(a-\beta w)_+\,da
 =\frac{A^2}{2}-A\beta w+\frac{\beta^2w^2}{2},
 \qquad 0\leq\beta w\leq A,
\tag{R17}
```

shows the mechanism and its nonzero quadratic contact coefficient. Its three
polynomial terms cancel only **after** integration against the original
kernel's zero moments. It is not an identification of the actual weighted
curved amplitude. Dropping that contact term before averaging is invalid.

The following are theorem-contract examples, **not Lean declarations or
proved geometric premises**:

```text
OPEN CurvedAveragedLongJet(h, f, delta, chi, phi):
  inputs: original AdmissibleTwoFace h f; Omega(t)^4 = 1+t^2;
          one fixed delta > 0; fixed bounded smooth endpoint weights
  B(w) := integral_{x in M} chi(x) B_x^>=(w; phi) dmu_g(x)
  derive from geometry, after averaging the moving contacts:
    B(w) = b0 + b1*w + b2*w^2 + o(w^2) as w -> 0+
  prove coefficient integrability and any domination on the remaining
  variables; retain contact, cutoff and endpoint-field derivative terms
  output: -C*rho^(3/2) P_chi^>=(rho; phi) -> 0
  alternative: identify a surviving term and revise this output explicitly
```

The analytic implication in this contract is conventional and proved: a
bounded compactly supported amplitude with a right quadratic jet has zero
normalized signed limit. Subtract its polynomial on the **whole half-line**;
the three signed moments (C13) vanish. Its remainder divided by the square of
phase is bounded, including away from zero, and tends to zero at zero. With
$`s=\sqrt{c\rho}`$, the normalized remainder integral is

```math
\frac{C}{c^{3/2}}\int_0^\infty z^2K(z^2)
 \frac{B(z/s)-b_0-b_1z/s-b_2(z/s)^2}{(z/s)^2}\,dz\longrightarrow0.
\tag{R18}
```

The dominating function is a constant times $`z^2|K(z^2)|`$, which is
integrable. This domination is **after averaging**, and does not contradict
(R14) or (R16). The corresponding abstract flat kernel component already
exists in `NullTransverseCancellation`; no curved producer is inferred from it.

### The actual short remainder needed for a supported bulk theorem

For an interior source support, choose one fixed positive cutoff small enough
that its entire short future cone, including its closure, lies in the region.
Let $`I_<^{\mathrm{actual}}(\rho,x;\phi)`$ be the inner integral from (R5),
and let $`I_<^{\mathrm{jet}}`$ be the integral of the **entire** (C11) angular
jet over that same cone, with the same phase expansion and radial cutoff.
The second-order kernel derivative term and all field derivatives remain.
The unresolved input is precisely:

```text
OPEN CurvedInteriorShortRemainder(h, f, delta, chi, phi):
  inputs: original geometry and polynomial density as above;
          chi smooth with compact interior support, independent of rho;
          a common delta > 0 with every closed short future cone over
          supp(chi) contained in M; phi smooth near these cones
  derive, without assuming an action limit:
    C*rho^(3/2) * integral_M chi(x) *
      [I_<^actual(rho,x;phi) - I_<^jet(rho,x;phi)] dmu_g(x) -> 0
```

The cutoff also satisfies the uniform compact Taylor-domain bound stated
before (C15). Its existence follows by shrinking a **fixed** cutoff once,
using compact interior support, not by varying it with density. C³ bounds
alone, or the absolute estimate (C17), do not prove this signed remainder.
The contact obstruction above does not disprove this interior contract.
A finite collection of compact interior supports does **not** cover the
whole open region up to its boundary; a boundary collar cannot be discarded.

If this short input and the compatible averaged long input are proved, (C14)
would yield the supported response $`\int\chi(\Box_g\phi+R\phi/2)d\mu_g`$.
For the unweighted second endpoint, this is the independently defined
half-curvature integral against the source weight. It is still conditional,
not a completed bulk theorem here. To extend to the complete action, #74/#75
must also derive compatible estimates for the boundary-truncated short
amplitude, keeping single-face and joint terms rather than substituting the
full-cone model where that cone leaves the region.

For compact interior weights the derivative identity (C18) remains:

```math
\int_M\chi\Box_g\phi\,d\mu_g
 =-\int_M g^{\mu\nu}\partial_\mu\chi\,\partial_\nu\phi\,d\mu_g.
\tag{R19}
```

There are boundary fluxes without that support condition. A first-endpoint
partition alone supplies no new field derivatives and its contributions sum
by (R7). If auxiliary second-endpoint fields form a partition of unity, their
differential terms sum to zero only after the complete partition is restored;
local pairwise chart restrictions are not the original observable. Any
artificial contact-layer subtraction must likewise be added back exactly.

**Consumer gate:** #75 must use this same decomposition, not solve a competing
raw-first-endpoint domination problem. #76 needs proved summable short bulk,
boundary/joint and averaged long outputs at one common fixed cutoff before
using #93's separate expectation equality. An obstruction report does not
satisfy those inputs. #74 retains ownership of the unproved supported bulk
coefficient and short remainder; an averaged-contact follow-up is only a
prerequisite, not permission to close #74 or unblock #75 automatically.
The unequal-axis example in #73 remains a required variable-angle regression
for the eventual joint/assembly work; the planar-future obstruction does not
replace that coverage.

## 6. Verification ledger

- **Conventional arguments:** exact phase/inverse and actual signed
  disintegration (R3)–(R7); per-active-fibre moving contacts (R8)–(R9);
  no integrable raw-fibre jet dominator (R14); no integrable normalized signed
  long-fibre dominator (R16); the conditional averaged kernel implication
  (R18). These are not an end-to-end curved action theorem.
- **Symbolic certificates:** `curved_remainders.py` checks the two positive
  quadratic decompositions, Jacobian, endpoint-density accounting, full
  triangle volume and density probe. `check_symbolic.py` includes them.
- **Numerical/regression evidence:** `test_curved_remainders.py` independently
  uses midpoint interval coordinates, checks inverse transport and all moving
  endpoint terms, exact contact versus approaching active contacts, the
  nonintegrable scaling and the actual signed finite-density obstruction.
  Direct time/radius integration independently checks the short/long split
  and single point allocation. These are regressions, not proofs by fitting
  large-density values to a conjectured full-action limit.
- **Lean:** no sources, checker, dependencies or build inputs changed; no new
  full audit or Lean verification is claimed. Later formalization must pass
  the repository's full integrated `formal/check.sh` gate after its final
  validation-affecting change.
- **Independent human mathematical review:** outstanding. The supported bulk
  theorem, actual short remainder, curved averaged-contact producer, joint
  comparison and complete deterministic/expected limit remain open. No
  arbitrary conformal-factor extension, shrinking-cutoff uniformity,
  full-action rate, or individual-sprinkling convergence follows.

Reproduce with the pinned Python environment in the root README:

```sh
.venv/bin/python check_symbolic.py
.venv/bin/python -m unittest -v
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
```
