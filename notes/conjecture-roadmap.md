# Roadmap toward the general BDG continuum conjecture

**Status:** research plan, not a proof or a claim that the conjecture is true as
currently phrased.

## Strategic objective

The restricted four-dimensional results are a foundation, not the endpoint of
Program 1. The minimum near-term milestone is to close
[issue #1](https://github.com/q5m-ai/causal-set-emergence/issues/1) without
weakening its existing contracts. The follow-on objective in
[issue #24](https://github.com/q5m-ai/causal-set-emergence/issues/24) is a
precise proof—or, if necessary, a counterexample and corrected theorem—for
Conjecture 1′ of Dowker–Liu–Lloyd-Jones:

```math
\lim_{\rho\to\infty}\frac{1}{\hbar}
\left\langle \mathbf{S}^{(d)}_\rho(M)\right\rangle
=
\frac{1}{l_p^{d-2}}\int_M d^d x\,\sqrt{-g}\,\frac{R}{2}
+
\frac{1}{l_p^{d-2}}\int_J
\coth\!\bigl(\theta(\lambda)\bigr)\,d\mu(\lambda).
```

Special geometries remain useful as regression tests and sources of analytic
structure. Accumulating additional examples is not, by itself, completion of
the general-theorem program.

## Why the theorem contract comes first

The published conjecture is a physics-level statement whose exact mathematical
scope must be fixed before a proof can close it. The general program must state:

- the class of globally hyperbolic Lorentzian regions;
- the regularity and compactness of the boundary faces and their joint;
- the action regime and normalization in dimension $`d`$;
- the treatment of spacelike, null, mixed, and degenerate joints;
- the hypotheses needed for the bulk and joint integrals to exist;
- whether additional corners or boundary strata are excluded;
- whether the conclusion concerns the expectation only or a stronger random
  mode of convergence.

Sharpening these hypotheses is part of the result. It must not be accomplished
by defining the action or an intermediate continuum functional to equal the
claimed limit.

## Staged proof program

### Stage 0 — finish the checked base case

Close issue #1, including the general admissible graph-cap limit and the
Poisson-expectation bridge. Preserve the distinction between the deterministic
integral, the expected discrete action, and individual random sprinklings.

### Stage 1 — general flat localization in four dimensions

Remove the planar-future-boundary restriction. For two sufficiently regular
spacelike faces in Minkowski space, prove that the shrinking boundary layer
localizes covariantly to the tangent wedge at each joint point and produces the
pointwise `coth θ` weight. The proof must uniformly control nearly null pairs,
the complement of the joint collar, and coordinate-chart remainders before
passing to the density limit.

This is the first qualitative generalization: it targets arbitrary admissible
faces rather than another explicit profile.

### Stage 2 — arbitrary dimension

Identify the dimension-dependent kernel and normalization, prove the required
uniform estimates, and recover the same geometric joint formula. Known causal
diamonds and constant-angle regions should become consequences or regression
cases rather than separate arguments.

### Stage 3 — curved spacetime

Control the local causal-interval volume and action-density expansions in
curved geometry. Recover the Einstein–Hilbert bulk term and prove that the
joint layer yields the conjectured weight, including all uniform remainder and
globalization estimates.

### Stage 4 — null, mixed, and limiting configurations

State and prove separate theorems where the ordinary spacelike angle becomes
degenerate. Determine whether arbitrary null boundaries satisfy the proposed
limiting convention or require additional geometric data or correction terms.
Timelike-boundary divergences associated with Conjecture 2 remain a distinct
problem.

## Verification and publication threshold

Each stage must keep these layers explicit:

1. symbolic or numerical evidence;
2. a written analytic argument;
3. machine-checked theorem contracts and proved components;
4. the Poisson expectation bridge;
5. independent mathematical and physical review.

Issue #24 closes only for a precise general theorem containing both the bulk
and joint terms, or for a rigorous counterexample accompanied by the corrected
general statement. Intermediate results may be circulated for scrutiny and
priority, but must be described as cases or prerequisites rather than as a proof
of unrestricted Conjecture 1′.
