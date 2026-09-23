# Emergence and dynamics — learnings and research roadmap

**Status:** conceptual synthesis and planning document. It separates established
causal-set definitions, results proved in this repository, interpretations that
need source verification, and speculative research directions.

## 1. Working picture

A causal set is a locally finite partially ordered set. Its elements represent
discrete events and its order represents possible causal precedence. Local
finiteness means that the order interval between any fixed related pair contains
only finitely many elements; it does not require the universe as a whole to be
finite.

The motivating continuum correspondence is often summarized as **order +
number = geometry**:

- causal order supplies the continuum conformal or light-cone structure;
- element counting approximates spacetime volume;
- together, under appropriate manifold-likeness conditions, they can encode a
  Lorentzian metric.

A smooth manifold, its topology, dimension, and metric are therefore candidates
for emergent rather than fundamental structures. Because the metric is the
gravitational field in general relativity, spacetime geometry and gravity would
co-emerge in this picture.

## 2. What “continuum limit” means in Program 1

The existing proof program does not begin with arbitrary causal-set dynamics and
derive our universe. It fixes a continuum Lorentzian region, considers causal
sets obtained by increasingly dense Poisson sprinklings, and asks whether a
discrete observable approaches the corresponding continuum quantity.

For the normalized expected four-dimensional BDG action, the target flat-space
joint term is

```math
\lim_{\rho\to\infty}\mathcal A_\rho(M)
=\int_J\coth\theta\,dA.
```

Increasing the density $`\rho`$ sends the characteristic discreteness scale
toward zero relative to the fixed macroscopic region. The limit establishes an
effective smooth description; it need not assert that physical spacetime is
fundamentally infinitely divisible.

### What has been learned technically

1. **Coordinate locality is unsafe near a light cone.** Nearly null pairs can
   be far apart in a chosen frame while having small proper-time separation and
   small interval volume. The complete future-point integral must be controlled
   before taking the density limit.
2. **The effective kernel is signed.** Its negative tail cannot simply be
   discarded. Normalization, absolute integrability, and tail control are
   separate obligations.
3. **Exact reductions matter.** For ellipsoidal graph caps, the formal proof
   connects the original four-dimensional deterministic action to a
   one-dimensional kernel integral at every positive density rather than
   assuming the reduction.
4. **A nonconstant joint angle is tractable in a restricted family.** The
   unequal-axis ellipsoid gives one connected joint with varying Lorentzian
   angle and an explicit deterministic limit.
5. **Verification layers must remain distinct.** Symbolic checks, numerical
   convergence, analytic proofs, Lean proofs, the Poisson expectation bridge,
   and independent peer review establish different things.

The exact checked boundary and remaining obligations are maintained in
[`../formal/README.md`](../formal/README.md) and
[issue #1](https://github.com/q5m-ai/causal-set-emergence/issues/1).

## 3. Causal diamonds, links, and nonlocality

For related events $`A\prec B`$, their causal interval or diamond is

```math
J^+(A)\cap J^-(B),
```

the possible locations of an intermediate event $`C`$ with
$`A\prec C\prec B`$. The pair is a **link** exactly when this interval contains
no causal-set element. If an intermediate element exists, the pair remains
causally related but is not linked; its order relation follows transitively.

Under Poisson sprinkling, an interval of spacetime volume $`V`$ is empty with
probability $`e^{-\rho V}`$. A pair can consequently appear far apart in a
coordinate diagram and still be linked when it lies close to the light cone and
its Lorentzian interval volume is small.

This is a form of long-range Lorentzian nonlocality, not automatically acausal
or faster-than-light propagation. The order states where influence is possible;
a dynamical law is required to say what actually propagates.

## 4. Why an ordinary cellular automaton is not enough

The Game of Life provides a productive intuition: simple microscopic rules can
produce structures and behavior at scales not obvious from the rules. A direct
identification with causal sets fails, however, because an ordinary cellular
automaton assumes:

- a fixed spatial lattice;
- a preferred external clock;
- simultaneous global update steps;
- a fixed finite spatial neighborhood;
- usually deterministic classical states.

Those assumptions build in spatial and temporal structure that a causal-set
theory is intended to explain. A closer analogue would be an **asynchronous,
label-independent causal growth or graph-rewriting system**. Elements would be
update events, order relations would record causal dependencies, and different
birth labelings of the same partial order would not represent different physics.
Classical sequential growth models are an established comparison point; a
quantum dynamics requires more than replacing one deterministic rule with
another.

## 5. Two meanings of “action”

Automaton discussions must distinguish:

1. an **action as an update**—a legal local transition or rewrite; and
2. a **physical action functional** $`S[C]`$—a number assigned to a complete
   causal set or history and used in dynamics.

Three broad approaches could be investigated:

### Rule first

Specify covariant legal transitions
$`C_0\rightarrow C_1\rightarrow\cdots`$, sample or enumerate their histories,
and test whether manifold-like dimension, locality, geometry, and fields emerge.

### Action first

Define a sum over causal sets or growth histories with amplitudes schematically
of the form

```math
\mathcal A[C]\sim e^{iS[C]}.
```

The BDG action is a candidate object to investigate, but the mathematical
existence, convergence, measure, and physical interpretation of such a sum are
not supplied by the current continuum-limit proof.

### Hybrid

Associate each legal rewrite with an action difference $`\Delta S`$, then ask
whether local transition amplitudes compose into a covariant global history
amplitude. Label independence and interference between histories are central
obligations.

## 6. Quantum formulation remains open

Canonical quantization, path-integral quantization, and stochastic quantization
are not universally interchangeable recipes. Their agreement requires
hypotheses and is often formal in interacting quantum field theory. Infinite
degrees of freedom, gauge constraints, anomalies, boundary conditions,
topology, and regularization can matter.

A state-vector description on spatial slices may also be nonfundamental when
spacetime and causal structure fluctuate. Histories, decoherence functionals,
or quantum measures may be more natural starting points. This does not by
itself prove that Hilbert spaces disappear; an ordinary state-space description
could emerge in an appropriate regime.

A separate lesson plan should cover:

- Hilbert spaces, rays, operators, and Fock space;
- canonical versus path-integral formulations in ordinary quantum mechanics;
- inequivalent representations in QFT;
- Euclidean and stochastic quantization;
- quantum measure and decoherence-functional approaches;
- the problem of time and reconstruction of emergent states.

## 7. Research questions for Program 2

1. Can a label-independent causal growth or rewriting rule be stated without a
   background lattice, global time, or preferred foliation?
2. Which rule classes preserve partial order, local finiteness, and an
   appropriate discrete covariance?
3. What observables diagnose manifold-likeness, effective dimension, topology,
   locality, and Lorentzian geometry?
4. Can manifold-like causal sets become typical rather than entropically rare?
5. Can classical sequential growth be generalized to a consistent quantum
   measure or decoherence functional?
6. Can the BDG action weight histories, and can its global value be represented
   through composable local action differences?
7. Does the checked continuum behavior constrain candidate microscopic rules or
   only test configurations already known to approximate a manifold?
8. What empirical or mathematical result would distinguish this program from a
   broad emergence analogy?

The public discussion thread for references and criticism is
[Discussion #12](https://github.com/q5m-ai/causal-set-emergence/discussions/12).

## 8. Proposed staged investigation

### Stage A — literature and definitions

- Review classical and quantum sequential growth, causal-set path integrals,
  quantum measure theory, and known entropy/manifold-likeness obstructions.
- Define “automaton,” “rewrite,” “history,” “covariance,” and “locality” before
  proposing rules.
- Identify what is already established and avoid renaming known constructions.

### Stage B — finite computational laboratory

- Implement small finite causal sets with canonical isomorphism handling.
- Test simple label-independent growth/rewrite proposals.
- Measure interval abundance, ordering fraction, estimated dimension, link
  structure, and small-action behavior.
- Treat simulations as diagnostics, not evidence of a continuum theory.

### Stage C — connect dynamics to action

- Calculate BDG action changes under elementary legal growth steps.
- Determine whether those increments depend only on covariantly available
  information.
- Compare rule-first ensembles with action-weighted ensembles.

### Stage D — continuum and quantum questions

- Seek scaling limits or universality classes rather than tuning one finite
  simulation to resemble a spacetime diagram.
- State a mathematically controlled histories measure or amplitude framework.
- Test whether the continuum-limit results from Program 1 survive in ensembles
  generated by the candidate dynamics.

## 9. Guardrails for future claims

- Do not call a graph or lattice a causal set unless the partial-order and local
  finiteness conditions are explicit.
- Do not equate a causal relation with actual dynamical influence.
- Do not call long-range timelike links faster-than-light propagation.
- Do not infer Lorentz invariance from visual isotropy on a finite diagram.
- Do not describe a deterministic classical automaton as quantum dynamics.
- Do not claim emergence merely because a continuum target was used to generate
  the discrete sample.
- Keep exploratory dynamics separate from the checked boundary-limit theorem.
- Record source versions, assumptions, failed approaches, and negative results.
