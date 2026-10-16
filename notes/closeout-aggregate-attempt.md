# One bounded attempt at the missing curved-3D producer

**STOP: #177 remains unresolved.** This is an additive analytic comparison
and a precise failure to finish the geometric estimate, not another positive
spacetime class, a complete-action obstruction, or a replacement acceptance
criterion. The [closure decision](issue-24-finite-closeout.md) separates this
research result from administrative reconciliation.

Integrated base: `9e0068f91c219fe61984d20fdb3f6939eab907c4`.
The separately inspected, **unmerged** #180 head is
`47e268c44bb1ba0083b4cf3509bc07c088da3f0a`:
[UP3](https://github.com/q5m-ai/causal-set-emergence/blob/47e268c44bb1ba0083b4cf3509bc07c088da3f0a/notes/curved-three-d-union.md)
and [CR3](https://github.com/q5m-ai/causal-set-emergence/blob/47e268c44bb1ba0083b4cf3509bc07c088da3f0a/notes/curved-three-d-critical.md).
They are research inputs, not integrated or independently accepted premises.
No source from that PR is copied into the integration branch here.

**Final live-source reconciliation:** #180 advanced during this task to
`a8fcb2465430c9d169cca67d942209c663bb7c74`. Its new
[phase freeze / PF3-L](https://github.com/q5m-ai/causal-set-emergence/blob/a8fcb2465430c9d169cca67d942209c663bb7c74/notes/curved-three-d-phase-freeze.md)
was read in full; the UP3/CR3 inputs above are unchanged. PF3-L isolates a
weaker complete **unit-weight** signed-increment estimate and leaves it
unproved. The arbitrary-weight aggregate route attempted here is sufficient,
not logically necessary. The new freeze's collective allocation attempt also
stops; no ordinary-pair or vertex budget is mistaken for the full numerator.
This source reconciliation starts no second research attempt.

## 1. Target and the single attempted inference

The highest-leverage missing producer is the complete curved-3D physical
long response, not another calibration. CR3.2 states the exact remaining
signed integral for the actual ramp Q, with both endpoint measures and every
physical partner. The sufficient ramp remainder has order little-o of seven
halves after both legitimate polynomial subtractions. UP3 only obtains
little-o of three for its opening ramp. Its integrable ordinary two-state
budget does not dominate the aggregate numerator.

**Attempt:** extend that two-state analysis to the whole leading aggregate
by bounding all omitted opening states at once, without a branch-count
constant or a kernel per route. Then try to integrate that bound with the
actual geometric pair measure. The algebraic step below succeeds. The
required uniform geometric integration does not follow from the available
budget; the attempt stops there. No further examples are commissioned.

## 2. Count-free inverse comparison (proved here in writing)

Fix finitely many positive amplitudes A_i and nonnegative gaps d_i, with
primary gap d_0=0. At a fixed endpoint label these are the **leading model**
data of UP3.8, not a new definition of physical interval volume. Put p=3/2.
For any retained subset I containing 0, define the unique positive roots

```math
\begin{aligned}
S(h)&=\sum_i A_i(h-d_i)_+^p,& S_I(h)&=\sum_{i\in I}A_i(h-d_i)_+^p,\\
S(T)&=v,&S_I(T_I)&=v,\\
B_I&=\frac1v\sum_{i\notin I}A_i(T_I-d_i)_+^p,&v&>0.
\end{aligned}\tag{CA1}
```

Existence and uniqueness follow from continuity, strict increase supplied by
the zero-gap primary, and divergence at infinity. There is no differentiating
through an opening, lower bound on a secondary stiffness, or uniform bound
on the number of states. The following comparison holds:

```math
\begin{aligned}
T_I(1+B_I)^{-2/3}&\le T\le T_I,\\
0\le T_I-T&\le T_I\{1-(1+B_I)^{-2/3}\}\\
 &\le T_I\min\{1,\tfrac23 B_I\}.
\end{aligned}\tag{CA2}
```

**Proof.** Nonnegativity gives S >= S_I and hence T <= T_I. For any
0 <= lambda <= 1 and d_i >= 0, the positive part of lambda*T_I-d_i is
at most lambda times the positive part of T_I-d_i. Thus
S(lambda*T_I) <= lambda^p S(T_I). Choose
lambda=(1+B_I)^(-1/p). The right side is exactly v; strict monotonicity gives
the lower bound in CA2. Finally the function 1-(1+B)^(-2/3) vanishes at zero,
has derivative at most 2/3 for B >= 0, and is at most one. This proves the
last inequality. All constants are independent of multiplicity and gaps.

The estimate is sharp: if all gaps vanish, the first bound is equality.
With equal amplitudes, retaining only two out of n states leaves a difference
proportional to the phase w, not a pointwise higher-order error. This is an
algebraic sharpness check, **not** a new spacetime construction or failure
claim. It agrees with, rather than evades, CR3.19's warning about three arrivals.

## 3. What survives masks and an actual cap

The comparison can retain arbitrary bounded signed clock weights and a
common cap. Let b(label,h) include both density factors, fields and physical
indicators in the same coordinate integral, and let its absolute value be
bounded by M(label). For any common clock cap H >= 0,

```math
\begin{aligned}
\left|\int_0^H b(\lambda,h)
 \left(\mathbf1_{\{h\le T_I\}}-\mathbf1_{\{h\le T\}}\right)dh\right|
 &\le M(\lambda)(T_I-T)\\
 &\le M(\lambda)T_I\min\{1,\tfrac23B_I\}.
\end{aligned}\tag{CA3}
```

Indeed the integrand is supported in the intersection of [T,T_I] and [0,H].
This uses no differentiation or factorization of physical masks. In
particular it does not extend the aggregate model past the actual good-clock
cap. Here lambda denotes the endpoint label, not the scalar used in CA2's
proof. The estimate also works with arbitrary additional measurable masks.

In a primary-coordinate patch, use the positive label measure from CL3.3 /
CR3.4, retaining its stiffness Jacobian and both endpoint densities (either
in that measure or in b, **not twice**). A chart partition must count physical
pairs once; this is not a sum over all tied primary labels. Put
v=c_3*w^(3/2), and take I to be the primary and a secondary giving the smallest
pair inverse. A measurable choice exists for a finite list, with index-order
tie breaking. The bound works for any choice and does not require uniqueness.
For the volume-dependent finite active lists of UP3, it remains pointwise;
a uniform finite list or measurable global decomposition is not inferred.
The primary root bounds T_I by a_0*w. Thus a **sufficient** geometric estimate
for removing the third-and-higher aggregate correction is

```math
\begin{aligned}
a_0(\lambda)&=(c_3/A_0(\lambda))^{2/3},\\
\mathcal H(w)&=\int M(\lambda)a_0(\lambda)
       \min\{1,\tfrac23B_I(w,\lambda)\}\,d\nu(\lambda),\\
|\Delta N(w)|&\le w\mathcal H(w),\\
\mathcal H(w)&=o(w^{3/2})
 \quad\Longrightarrow\quad
 \left|\int_0^w\Delta N(s)\,ds\right|=o(w^{7/2}).
\end{aligned}\tag{CA4}
```

The implication follows by integrating the bound: an eventual epsilon bound
on H(s)/s^(3/2) gives 2*epsilon*w^(7/2)/7. A corresponding bounded ratio
provides critical domination. For a global use, the measurable physical-label
allocation, actual caps and all patches must first be justified. CA4 is an
explicit possible **output of geometry**, not an admissibility assumption,
a necessary criterion, or a complete new proof of CR3.2.

## 4. The precise failed geometric inference

On a compact patch with a fixed finite number of uniformly nondegenerate,
uniformly separated states and bounded coordinate inverses, the omitted
aggregate is zero unless two secondary gaps are O(w). Two gap coordinates
and bounded coarea density give H(w)=O(w^2), which suffices. This is a local
estimate, **not** an additional spacetime theorem or permission to impose
these conditions on #177.

The general case does not have those uniform constants. At a triple tie in
normalized terminal directions the actual two-gap determinant contains

```math
\begin{aligned}
\left|\det(n_j-n_0,n_k-n_0)\right|
 &=\tfrac12|n_j-n_0|\,|n_k-n_0|\,|n_k-n_j|.
\end{aligned}\tag{CA5}
```

This is the elementary unit-circle determinant already used in CR3.19.
Proper-coordinate factors do not remove its vanishing. CR3.7 controls an
ordinary **two-state cut measure** after exchanging its stiff/soft
parametrizations. It does not control the third chord in CA5, nor the
weighted measure of the two simultaneous gap bands in CA4. CA2 bounds the
numerator without a count constant, but does not supply that missing measure
bound. Pointwise almost-everywhere ordinary cuts plus finite budget still
cannot justify dominated convergence. The geometrically realized singular
cut curvature in CR3 is retained, not excluded by a smoothness assertion.

**Exact stopping statement:** no proof of CA4's geometric little-o bound
(or of a weaker sufficient signed aggregate bound) has been obtained on the
original class with coalescing states and arbitrarily soft competing minima.
Even such a bound would still have to be combined with the actual linear
S1 correction, simultaneous contact transport and **both** subtraction tails;
those are not estimated by CA2. UP3's normalized kernel comparison is not
promoted to a stronger ramp comparison. The common physical cutoff, positive
phase complement and linear continuation of the full ramp remain unchanged.

Accordingly the complete CR3.2 signed conclusion, deterministic assembly and
subsequent expected limit are **not established**. No target adjustment,
renormalization, no-caustics condition, finite-type assumption or sample-wise
claim is justified. The existing C3/F3 restricted results are not re-proved
or presented as completion.

## 5. Falsifiability, verification and decision

The six checks in `test_closeout_aggregate.py` test CA2's actual aggregate
root, sharpness, inactive states, amplitude splitting without count growth,
a common cap with a signed mask, and the nonzero best-pair discrepancy.
They introduce **no spacetime examples** and cannot certify CA4. CA1--CA3
have the elementary proof above; CA4's physical geometric premise is missing.
All are conventional writing/finite diagnostics, not Lean or expert review.

The falsifiable next mathematical milestone is the complete unit-observable
PF3-L estimate or a fully assembled admitted obstruction. An original-class
bound on the complete weighted aggregate numerator would suffice (CA4 is only
a candidate third-state subestimate), with contacts and coefficient tails
retained; it is **not** a mandatory stronger replacement for PF3-L. Another
scalar budget, isolated contact, or finite optimization is a stop, not success.
This session stops now rather than opening another chain of examples or
claiming the existing critical budget has finished the proof.

**User decision:** retain the current #177 obligation and authorize a future
bounded producer effort only if desired, or authorize a bounded-paper release
while leaving #177/#81/#24 open. Dropping curved 3D from epic acceptance is a
separate explicit scope change; neither this failure nor higher-dimensional
counterexamples authorizes it. No new issue or review request is created.
