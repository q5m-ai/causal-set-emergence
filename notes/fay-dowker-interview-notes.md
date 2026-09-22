# Video notes — Fay Dowker with Curt Jaimungal

**Topic:** causal set theory and its relationship to general relativity
**Status:** provisional viewing notes; terminology and interpretations should be
verified against the original conversation before citation. These notes record a
learning process, not claims by the repository or a transcript of Dowker's words.

For the synthesized project-level conclusions and research boundaries, see
[Emergence and dynamics — learnings and research roadmap](emergence-roadmap.md).

## Deep theory versus continuum approximation

- **Deep/fundamental theory:** causal set theory.
- **Emergent theory:** general relativity (GR), described as a continuum approximation to the deeper discrete theory.
- The causal structure is meant to carry through from the causal set into the GR approximation. This does **not necessarily mean that the two theories contain literally the same mathematical object**; rather, a causal set that admits a good continuum approximation should reproduce the continuum spacetime's causal relations.
- Structures used in GR that may not be fundamental in the deep theory include:
  - the **manifold**;
  - **topology**;
  - the **metric**.
- Point to clarify: these structures presumably **emerge in the continuum approximation**, rather than being fundamental ingredients of the causal set.

## Three pillars of causal set theory

### 1. Discreteness

- Fundamental spacetime consists of discrete spacetime elements or events rather than a continuum of infinitely many points.
- More precisely, a causal set is **locally finite**: between any two causally related elements, there are only finitely many intermediate elements.
- This does not necessarily mean the entire universe contains only finitely many elements. Rather, a bounded finite-volume region—such as the spacetime region occupied by a finite-duration podcast—would correspond to finitely many causal-set elements.
- Four-dimensionality is expected to emerge for a causal set that approximates our spacetime; it is not built into the bare definition of every causal set.

### 2. Causal partial order

- The elements are related by a partial order, conventionally written \(A\prec B\), representing that \(A\) is in the causal past of \(B\).
- If \(A\prec B\) and \(B\prec C\), transitivity requires \(A\prec C\).
- Not every pair must be comparable. Unrelated elements correspond, in a continuum approximation, to spacelike-separated events—outside one another's light cones.
- “Precedes” means that causal influence is possible; it need not mean that \(A\) actually produced or directly caused \(B\).

### 3. Quantum dynamics / sum over histories

- The third pillar is the quantum-mechanical treatment of causal sets, commonly envisioned as a **sum over causal-set histories** analogous to a path integral.
- Instead of selecting one classical spacetime history in advance, the theory assigns quantum amplitudes to possible causal sets or growth histories and combines them.
- “Sum over worlds” is a useful first intuition, but **sum over possible histories/configurations** is more precise. The amplitudes can interfere, so this is not an ordinary probability-weighted list of universes.
- Point to verify against the interview: exactly which path-integral or quantum-measure formulation Dowker names, and whether she presents this as an established pillar or as the still-incomplete dynamics of the theory.

## Checkpoint: state vectors and Hilbert space

Dowker raises the possibility that the familiar description of a quantum state as a vector in Hilbert space may not survive unchanged in the deep theory. This needs a deeper review.

### Brief orientation

- A **Hilbert space** is a vector space with an inner product and suitable completeness properties. The inner product allows quantum amplitudes, probabilities, and notions such as orthogonality to be defined.
- A **state vector**, written \(|\psi\rangle\), represents the physical state of a quantum system. Strictly, vectors differing only by an overall nonzero phase represent the same pure physical state; the state is therefore a **ray** in Hilbert space.
- **Observables** are represented by operators acting on the Hilbert space. The state vector encodes the amplitudes for their possible measurement outcomes.
- In quantum field theory, states can describe the vacuum, particle excitations, or superpositions of field configurations. A Fock space is a common Hilbert-space construction when a particle description is available.

### Why it might not be fundamental

The Hilbert-space/state-at-an-instant framework may depend on concepts—such as a fixed background time or a division into spatial slices—that become problematic when spacetime itself is quantum and fundamental causal structure fluctuates. A histories-based formulation may instead take entire causal histories, amplitudes, a decoherence functional, or a quantum measure as primary. Ordinary Hilbert-space states could then emerge only in an appropriate approximation.

This is a possibility, not a conclusion that Hilbert spaces have already been eliminated from causal set theory. Clarify from the interview whether Dowker means:

1. Hilbert space is definitely absent from the deep theory;
2. it is not assumed to be fundamental; or
3. the histories/quantum-measure framework is simply more natural for causal sets.

### Deep-dive questions

- What distinguishes a Hilbert-space state formulation from a path-integral or sum-over-histories formulation?
- How can the two formulations reproduce one another in ordinary quantum mechanics and QFT?
- What is a **quantum measure**, and how does it differ from an ordinary probability measure?
- What is a **decoherence functional**, and can a Hilbert space be reconstructed from one?
- Why does quantum gravity create a “problem of time” for states defined on spatial slices?
- What would it mean for state vectors and Hilbert space to emerge from deeper causal-set dynamics?

## Checkpoint: different methods of quantization

Jaimungal asks whether the various methods of quantization—including **stochastic quantization** and **path-integral quantization**—all lead to the same quantum theory, and whether that equivalence has been proved.

### Initial answer

**No universal theorem says that every quantization method always produces the same theory.** Different formulations often agree when they are mathematically well defined and the required assumptions hold, but equivalence must be established case by case. In difficult quantum field theories, some constructions remain formal rather than rigorously defined.

Common approaches include:

- **Canonical quantization:** promotes classical variables to operators satisfying commutation relations on a Hilbert space.
- **Path-integral / sum-over-histories quantization:** combines amplitudes over possible classical configurations or histories.
- **Stochastic quantization:** introduces an auxiliary stochastic time and seeks a probability distribution whose equilibrium reproduces a Euclidean quantum field theory.
- Other possibilities include geometric, deformation, algebraic, and loop quantization, depending on the system under study.

### Important qualifications

- In ordinary quantum mechanics, canonical and path-integral formulations frequently reproduce the same predictions under suitable conditions.
- Even there, a path integral may first be a formal expression and require careful definition.
- For systems with infinitely many degrees of freedom, as in QFT, unitarily inequivalent Hilbert-space representations can occur. The uniqueness familiar from finite-dimensional quantum mechanics does not automatically extend to fields.
- Gauge constraints, anomalies, regularization, boundary conditions, topology, and choices of variables can affect whether two quantizations agree—or whether a proposed quantization exists at all.
- Stochastic quantization is closely related to Euclidean path integrals under appropriate convergence and equilibrium assumptions, but that is not an unconditional equivalence for every theory.
- Classically equivalent descriptions need not remain equivalent after quantization. This possibility is sometimes summarized as **quantization ambiguity** or as the fact that “quantization is not a functor” without additional structure and restrictions.

### Questions for a deeper review

- What other quantization methods, beyond stochastic and path-integral quantization, does Jaimungal list in the interview?
- What equivalence results exist between canonical and path-integral quantization?
- What does the Stone–von Neumann theorem establish for finite degrees of freedom, and why does it fail to provide uniqueness in QFT?
- Under what assumptions does stochastic quantization reproduce a Euclidean path integral?
- How do Wick rotation and the Osterwalder–Schrader reconstruction connect Euclidean field theory to Lorentzian QFT?
- Which of these methods could apply when causal structure itself is dynamical?

### Follow-up requested

Prepare a deeper-dive lesson plan on quantization methods after finishing the video notes. It should build from the necessary foundations and compare canonical, path-integral, and stochastic quantization; explain when they agree; and cover why no universal equivalence theorem applies.

## Checkpoint: locality and nonlocality

Dowker's perspective appears to be that causal-set nonlocality remains compatible with causal structure: influence does not propagate outside the light cone, but the discrete structure does not reproduce the continuum notion of a small, fixed set of nearest spacetime neighbors.

### Working interpretation

- **Causal locality is preserved:** two spacelike-related elements—outside one another's light cones—are incomparable in the causal order. The order does not introduce ordinary faster-than-light causal influence.
- **A form of nonlocality exists within the light cone:** causal-set links or dynamics can connect causally related elements that appear arbitrarily far apart spatially in a chosen reference frame.
- Thus, “nonlocal” here need not mean “acausal” or “outside the light cone.” It can mean **long-range but still causally ordered**.

### Important refinement

For a fixed pair \(x\prec y\), local finiteness says that the interval between them contains only finitely many elements. However, in an unbounded sprinkled Lorentzian spacetime of dimension greater than one, an element can have infinitely many immediate causal-set neighbors or **links**. These can lie arbitrarily far away in a chosen frame while remaining close to the light cone. This occurs because surfaces of fixed proper time are noncompact in Lorentzian geometry.

A link \(x\prec y\) means there is no causal-set element \(z\) with \(x\prec z\prec y\). It is the order-theoretic analogue of a nearest-neighbor relation. Saying linked elements “can affect each other” may be intuitive, but the order relation alone specifies possible causal relation, not a complete law of physical influence; that depends on the dynamics.

### Questions to revisit

- Is Dowker referring specifically to infinitely many causal links, to nonlocal causal-set field operators, or to both?
- How can an element have infinitely many links without violating local finiteness?
- How are causal-set versions of the d'Alembertian made nonlocal yet approximately local in a continuum limit?
- Does this nonlocality produce observable effects, and at what scale?
- How does Lorentz invariance prevent the selection of a finite, frame-independent set of nearest neighbors?

## Wild-card connection: automata and causal sets

There is a plausible connection if the automaton is treated as a rule for **growing or rewriting causal structure**, rather than as an ordinary cellular automaton on a fixed spatial grid.

A tentative correspondence is:

- causal-set elements ↔ discrete events or update occurrences;
- order relations/links ↔ allowed causal dependencies;
- an update rule ↔ a law for adding elements and selecting their causal past;
- repeated growth or rewriting ↔ a complete causal-set history;
- large-scale patterns ↔ emergent spacetime dimension, geometry, fields, or other physics.

This resembles the Game of Life in the broad sense that simple microscopic rules can generate complex macroscopic behavior. Important differences prevent a direct identification:

- The Game of Life begins with a fixed regular spatial lattice; causal set theory aims to make spacetime itself emergent.
- The Game of Life has an external global clock and simultaneous update steps; a causal set should not require a physically preferred foliation or labeling.
- Life's interactions use a fixed finite spatial neighborhood; Lorentz-invariant causal sets do not naturally have that same notion of nearest spatial neighbors and can exhibit long-range causal links.
- Standard causal sets are locally finite partial orders, not arbitrary cell-state grids.
- A deterministic classical automaton is not yet a quantum dynamics. A fundamental causal-set theory may require stochastic or quantum amplitudes over growth histories.

A closer established analogy is **classical sequential growth**: causal-set elements are born one at a time according to transition probabilities, while the birth labels are not supposed to be physically meaningful. Quantum sequential growth and sum-over-histories approaches ask how to replace classical probabilities with quantum dynamics.

Questions to investigate:

- Can an order-invariant graph-rewriting or asynchronous automaton generate manifold-like causal sets?
- What conditions on a growth rule preserve discrete general covariance and causal consistency?
- Can dimension, locality, and approximately Lorentzian geometry emerge without building in a lattice or preferred frame?
- Can the rule be quantum—assigning amplitudes or a quantum measure to histories—rather than merely deterministic or stochastic?
- Could the BDG action studied in this repository supply weights for causal-set histories, analogous to \(e^{iS}\) in a path integral?

## Terms to circle back to

### Manifold

A manifold is a continuum of points that locally resembles ordinary coordinate space, such as \(\mathbb{R}^4\). In GR, spacetime is modeled as a four-dimensional manifold. The manifold provides the underlying set of spacetime points and the framework in which coordinates and smooth fields can be defined.

### Topology

Topology describes continuity and connectedness: which regions are neighborhoods, which points or regions are connected, and whether a space contains features such as holes. It does not by itself assign lengths or durations. A manifold comes equipped with a topology, but topology is less detailed than geometry.

Questions to revisit:

- How, and under what conditions, can a causal set recover continuum topology?
- Can distinct continuum topologies correspond approximately to the same causal set?
- Are there causal sets that have no good manifold/topological approximation?

### Metric

In GR, the **metric** \(g_{\mu\nu}\) is the field that supplies spacetime's geometry. It determines:

- proper time along timelike paths;
- spatial distance along spacelike directions;
- whether a separation is timelike, null, or spacelike;
- light-cone structure;
- angles, volumes, and curvature.

A useful distinction:

- **Causal order** tells us which events can causally precede which others.
- **Volume information** tells us how much spacetime lies in a region.
- In a sufficiently well-behaved Lorentzian spacetime, causal structure plus volume information is enough to recover the spacetime metric. In causal set theory, order supplies the causal structure and counting elements supplies volume, roughly summarized as **“order + number = geometry.”**

Questions to revisit:

- Precisely how do causal order and element counting reconstruct the continuum metric?
- Which parts of the metric are fixed by causal order alone, and which require volume/counting information?
- What does it mean mathematically for a causal set to approximate, or be faithfully embedded into, a Lorentzian manifold?
- In what sense is causality “the same” between the deep theory and emergent GR?

## Initial conceptual picture

Causal set theory replaces a smooth spacetime continuum with a locally finite partially ordered set. The order relation represents causal precedence, while local finiteness gives discreteness and allows element counts to represent spacetime volume. A smooth manifold, its topology, and its metric are then expected to appear only when the causal set has an appropriate large-scale continuum approximation.
