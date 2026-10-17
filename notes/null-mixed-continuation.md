# Continuation after the general-front theorem: exact blockers (#156)

**Subsequent continuation:** [TC1–TC8](null-tangency-matching.md) now prove the
joint signed correction and complete deterministic/expected theorem for the
arbitrary **two-sheet** tangencies below, with a derived extra area at persistent
union coincidences. [The closure audit, NA1–NA3](null-closure-audit.md) records
two distinct further NN attempts and NP's stronger local-repair obstruction.
The earlier attempts and stopping point below are preserved; they no longer
assert that TC's two-sheet estimate is missing. Higher nonregular contacts,
general NN and corrected intrinsic coverage remain open. The current short
reading guide is the [two-page proof spine](null-proof-spine.md).

**Do not close #156.** [NF-d](regular-null-front-limit.md#7-continue-through-the-dimensional-producer-and-complete-assembly)
is a complete all-dimensional conformally Minkowski regular-SN front theorem,
including arbitrary finite tip multiplicity with its proved geometric contact
condition. [NP1–NP9](null-product-focusing-obstruction.md) is a complete admitted
all-null focusing counterexample, not a failed estimate. Neither resolves the
original remaining tangential/NN/nonconformal quantifiers or supplies their
corrected general theorem. This note records the substantive attempts after
NF, and a specialist-readable next inference rather than a new pilot queue.

## 1. Tangential floor/crease contact: replace transport by a ramp

The floor-transverse field in NF cannot exist when dF annihilates the common
stratum tangent. That is a geometric obstruction to **that method**, not to
the limit. A second method integrates the normal wedge before differentiating.
It already gives a stronger producer than a failed inverse bound.

For a two-cone intersection, centers at ±a in the z direction, write
r(w)=sqrt(a^2+|w|^2) and take H independent of z locally. For fixed w, put
h=H(w)-r(w). Directly integrate t and z in the actual lens:

```math
\begin{aligned}
V_w(h)&=2\int_0^{h_+}(h-y)
 \frac{r(w)+y}{\sqrt{(r(w)+y)^2-|w|^2}}\,dy\\
 &=\frac{r(w)}a h_+^2+O(h_+^3).
\end{aligned}\tag{NT1}
```

The substitution is y=sqrt((a+|z|)^2+|w|^2)-r(w); its derivative is uniformly
nonzero on a fixed compact crease patch. Thus NT1 is an actual geometric
normal integration, not an assumed fractional contact law. With any smooth
density the same change produces a smooth coefficient of h_+^2 and higher
integral-remainder terms. For a source displaced by ell*u, the floor height
becomes H(w-ell*b*n_w)-ell, so the new gap is
h-ell*a(w,n,b)+O(ell^2), with a=1+b*n_w dot grad H>=1-lambda>0.
This retains all sides of the closing contact.

The relevant general ramp estimate needs no finite contact order. For a
finite measure nu, bounded positive a, and any measurable h, define R(epsilon)
by subtracting the actual right quadratic polynomial from
integral (h-epsilon*a)_+^2 dnu. Pointwise expansion gives

```math
\begin{aligned}
R(\varepsilon)&=\int\left[(h-\varepsilon a)_+^2-h_+^2
             +2\varepsilon a h_+-\varepsilon^2a^2\mathbf1_{h>0}\right]d\nu,\\
|R(\varepsilon)|&\le\varepsilon^2\|a\|_\infty^2
 \nu\{0\lt h\le\varepsilon\|a\|_\infty\}=o(\varepsilon^2).
\end{aligned}\tag{NT2}
```

Indeed the integrand vanishes for h<=0 and h>epsilon*a; on the remaining
strip it is -(h-epsilon*a)^2. Continuity from above of finite measure makes
the strip mass tend to zero, even with a positive-measure zero level. This
is a count-free, one-sided contact producer. Smooth coefficients can be
Taylor expanded separately. It does not delete the zero set by assertion.

**Why this is not yet NF's matched estimate.** In a smooth finite-order local
gap h(y)=y^(2m), with the other crease coordinate integrated against a fixed
weight, the scalar leading model is exactly

```math
\begin{aligned}
\int_{-1}^1(y^{2m}-\varepsilon)_+^2dy
 &=\frac2{4m+1}-\frac{4\varepsilon}{2m+1}+2\varepsilon^2
 -\frac{16m^2}{(2m+1)(4m+1)}\varepsilon^{2+1/(2m)}.
\end{aligned}\tag{NT3}
```

Its third derivative need not be bounded. For a flat smooth gap
h(y)=exp(-1/y^2), h(0)=0, the same remainder has size comparable to
epsilon^2/sqrt(log(1/epsilon)); no fixed positive additional power follows.
The upper bound is NT2. For the lower bound use
|y|<1/sqrt(2 log(1/epsilon)), where 0<h<=epsilon^2 and the negative
integrand has magnitude at least epsilon^2(1-epsilon)^2. These gap germs
are realizable on a fixed crease patch: set H=r+h there. Its slope is
strictly below one on a sufficiently small bounded patch, since |grad r|<1;
scale h if necessary. A smooth strict-Lipschitz extension can be made by
first flattening r radially outside a larger compact patch and placing the
small perturbation inside its positive slope margin. Positive height at the
tips is preserved. No density-dependent geometry is involved.

The scalar ramp does **not** include the interval phase, endpoint factors
and angular integration. It disproves a uniform positive-power remainder
shortcut, not a complete-action target. NF's Mellin proof differentiates in
xi after ell subtraction and needs control at the simultaneous ell=xi=0
corner. NT2 gives no such mixed control. At accumulated critical height
levels, differentiating a third time in a phase-dependent displacement can
produce singular level measures; bounded smooth H alone does not give the
uniform third derivative used in NF4. Repeating that majorant is not a next
step.

**Exact next inference T:** push the *complete* normal-integrated physical
amplitude (including h_d, both endpoint densities and the angular measure)
through the joint short/null scaling, retaining the NT2 strip and its two
subtraction tails. Prove the normalized signed remainder tends to zero, or
derive a surviving stratum coefficient. A unit-observable signed estimate
suffices; a meromorphic strip, arbitrary-weight Taylor theorem or a finite
order contact classification is not a new acceptance requirement. NT2 alone
cannot be used as that estimate.

## 2. Past–future NN: the missing direction is characteristic, not multiplicity

The exact NF2 pair identity still holds for a future set with a null lower
face. The strict floor determinant need not. For the local lower null plane
F=t-x1, the actual long coordinates give

```math
\begin{aligned}
\partial_\ell F(q-\ell(1,\sqrt{1-\xi}\,n))
 &=-1+\sqrt{1-\xi}\,n_1,\\
\left.\partial_\ell F\right|_{\xi=0,n_1=1}&=0,\qquad
1-n_1=\tfrac12|n_\perp|^2+O(|n_\perp|^4).
\end{aligned}\tag{NT4}
```

The inverse used by NF3 loses its bound on a generator direction. Simply
excluding that direction is invalid: its entire angular neighborhood remains
at the fully normalized order. Blowing up the angle gives a denominator
comparable to xi+|n_perp|^2. In 4D the naive angular inverse majorant is
integral theta dtheta/(xi+theta^2), logarithmically unbounded as xi decreases.
The calculation identifies the **joint angular/phase corner** to match; it
is not evidence of divergence of the signed complete action. In higher or
lower dimensions the angular power changes, and so do the critical moments.

Trying the short transport instead helps only at an actual regular
floor/upper-front contact: their independent conormals can be straightened.
It does not resolve macroscopic source-generator contacts with a translated
upper crease, simultaneous lower seams/tips, or the angular corner NT4.
A global smooth approximation with slopes below one would require precisely
the uniform estimate that is missing; it cannot supply a null-limit interchange.

**Exact next inference N:** resolve the physical phase and characteristic
angular corner together, with every actual lower-face generator endpoint and
upper-front contact, and match to the diagonal at one fixed cutoff. For a
piecewise-null lower front, retain simultaneous face masks before applying
one kernel. ND's complete fibre proof covers its exact flat cone-ending class,
and NP computes one full nonconformal all-null family, but neither gives this
general NN producer. A regular NN joint coefficient alone is not the answer.

## 3. Dimensions and nonconformal metrics: what really transferred

The dimensional attempt did not stop at a 4D lemma. NF10–NF13 derive the actual
rest-diamond moments, parity-dependent Mellin products, critical remainder,
curvature/screen target, complete assembly and subsequent original-law
expectation for every d>=2 in NF-d's geometric class. The beta-mixture and
2D logarithmic results ND1–ND9 remain valid and distinct; no d>2 tip bound is
used in d=2. Thus “other dimensions” is no longer an undifferentiated blocker.
The remaining dimensional problems are **T/N and nonconformal whole intervals**,
with the actual K_d critical exponent 1+2/d, not a missing normalization table.

A general nonconformal metric changes the physical interval and its null
directions. The affine rest-diamond map in NF2 is no longer an actual map,
even if a single null geodesic has a regular optical chart. Integrating a
quadratic approximation along one route fails to count the physical union.
The read [PW](nonconformal-plane-wave-limit.md) and
[HO](hadamard-optical-limit.md) sources supply genuine whole intervals in
their classes, but their complete contact arguments consume **spacelike**
face ranks. Substituting those ranks into NT4 is not a proof. NF's static
past-set trick alone cannot restore the missing actual phase inverse.

The different method was to retain a solvable **whole nonconformal interval**
and derive its new null-region endpoint measure exactly. NP3 does this,
rather than restrict the old spacelike action to an interior sector.
NP4–NP8 compute both null-face endpoint contacts, the genuine 7D kernel,
point cancellation, independent short bulk/NN target, matched focusing
coefficient and every complement. NP9 transfers the original law afterward.
This succeeds as a complete null/mixed obstruction. It is not a universal
correction and does not turn other dimensions or metrics into FAILS.

The stronger quartic-focus 4D CO obstruction was also checked as a possible
input. Its full source weight is specifically the compact-Cauchy slab's
positive part in CO2/CO11. Cutting that slab by a characteristic face changes
that weight and its closing/focusing intersections. The published CO13
transfer does not prove uniformity for those new masks. Retaining only an
interior cusp gives no control over the full complement. Accordingly **no
4D null/mixed obstruction is claimed from CO**. NP replaces that stalled
transfer with an actual computed null geometry, not another attempt at the
same unproved weighted estimate.

## 4. Corrected-statement gap and bounded specialist handoff

The new evidence rules out “prove the old finite target for every original
null/mixed member” as a viable route: NP is an admitted complete-action
counterexample. A corrected general theorem is therefore necessary. NF-d is
a genuine sufficient geometric theorem covering whole regular fronts and
finite multiplicity, not a necessary-and-sufficient classification. NP's
positive focal divergence is an explicit correction on its whole stated
product family, not a universal local crease action or renormalization.

The precise unresolved parent inference is: **state and prove a non-vacuous
corrected general null/mixed assertion that retains the original T/N/contact
and intrinsic-metric obligations, or obtain approval for a precise smaller
endpoint.** No scope proposal is silently accepted here. In particular,
closing on “NF-d plus NP, with every other original entry assigned an owner”
would drop the unresolved T/N/nonconformal clauses. That proposal is not
recommended as original-contract closure. Nor is classification of every
individual spacetime being added as a new requirement.

For the next specialist, the useful minimum reading order is:

1. NF2–NF5 and NF10–NF13: the count-independent producer is complete; do not
   redo three/four/five tips or replace the dimensional kernels.
2. NF8–NF9: arbitrary dependent finite-tip arrangements and exact causal-pair/
   layer inclusion–exclusion. No intersection truncation or bilocal axiom.
3. NT1–NT3: normal integration repairs the first tangency failure, but only
   yields a scalar one-sided remainder. Try a signed joint scaling estimate,
   not the already failed classical third-derivative bound.
4. NT4: for NN the lost variable is angular/characteristic. Match this corner
   directly; do not take a spacelike-to-null limit.
5. NP3–NP8, then O6–O13: independently inspect the new whole endpoint weight,
   full sign matching, fixed-cutoff short coefficient and physical point.
   The old rational certificate covers I only; it does not certify geometry.

The single original-item crosswalk is in the required-coverage ledger, not
repeated as competing acceptance tables here. No new child, agent, scope
change, issue closure, merge or deployment accompanies this handoff.
Written arguments, diagnostics, generic Lean foundations and human acceptance
remain distinct. #94/#86 retain intended-statement, physical, provenance and
justified-verification scrutiny.
