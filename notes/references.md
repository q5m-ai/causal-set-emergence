# Sources and attribution

## Primary sources inspected

1. **Fay Dowker, Roger Liu, Daniel Lloyd-Jones.**
   *Timelike boundary and corner terms in the causal set action.*
   [arXiv:2501.00139v2](https://arxiv.org/html/2501.00139v2), 25 April 2025.
   Published as *Classical and Quantum Gravity* **42**, 205006 (2025),
   [doi:10.1088/1361-6382/ae0be5](https://doi.org/10.1088/1361-6382/ae0be5).
   - Section 2.3, equations (7)–(8): the Poisson mean action.
   - Section 2.5, **Conjecture 1′, equation (11)**: the precise modified
     conjecture used here, with the `coth θ` joint weight.
   - Section 7.2: Lorentzian angle convention.
   - Section 7.4: higher-dimensional constant-angle evidence and the
     variable-angle conjecture. Its cone examples and results are prior work,
     not discoveries of this draft.
   - Appendix A, equation (78): four-dimensional BDG normalization.

2. **Fay Dowker.** *Boundary contributions in the causal set action.*
   [arXiv:2007.13206v2](https://arxiv.org/html/2007.13206v2), 28 July 2020.
   [doi:10.1088/1361-6382/abc2fd](https://doi.org/10.1088/1361-6382/abc2fd).
   - Sections 1–2: original conjecture and the danger of interchanging a
     pointwise continuum limit with the outer integral.
   - Section 4, equations (4.8)–(4.13), specifically the flat term in (4.9):
     setting the curvature parameter to zero gives the exponential action
     density used for our one-tip regions.
   - The proof draft also derives that flat identity directly by interval
     moments, so it does not rely on a truncated curvature expansion.

## Related prior work and the later general-contract audit

- **Michel Buck, Fay Dowker, Ian Jubb, Sumati Surya.**
  *Boundary terms for causal sets*, *Class. Quantum Grav.* **32**, 205004 (2015).
  [doi:10.1088/0264-9381/32/20/205004](https://doi.org/10.1088/0264-9381/32/20/205004).
  Flat causal-diamond boundary results are prior work. The later
  [passage audit](general-contract-literature.md) checked §4 of
  [1502.05388v2](https://arxiv.org/html/1502.05388v2): the explicit asymptotic
  evaluations run through dimensions 2–16. An all-dimension proof is not
  established by that passage; the previous unqualified attribution was too
  broad. Reproducing the inspected cases is not a new theorem.
- **Ludovico Machet, Jinzhao Wang.**
  *On the continuum limit of Benincasa–Dowker–Glaser causal set action.*
  [arXiv:2007.13192](https://arxiv.org/abs/2007.13192),
  [doi:10.1088/1361-6382/abc274](https://doi.org/10.1088/1361-6382/abc274).
  Relevant curved-small-diamond evidence, outside the original flat-space
  attempt. The later audit checked the first-order-curvature qualification,
  the 2D calculation and the explicit 3D/4D/5D comparisons; these are not
  controlled all-orders limits for arbitrary fixed curved regions.

## Focused two-face contract review

The [#49 contract review](two-face-contract.md#5-source-review-and-attribution)
records a reading of the pinned 2025 source's §§2.4–2.7 and all of §7, including
isolated/embedded regimes, the prior weighted-overlap method, smearing limits,
lozenge/triangle evidence, and constant-angle cones checked through dimension
11. It distinguishes those calculations from general curved-face localization
and lists literature not reviewed in this task. This does not upgrade the
related-work inventory above to an exhaustive novelty search.

The subsequent [#90 literature audit](general-contract-literature.md) expands
that reading to the 2020 boundary/bulk calculations, flat and curved diamonds,
marked-null angle conventions and selected later work. It records exact
passages, normalization differences, snapshot hashes and a bounded search.
Chevalier's 2023 primary overlap-method text was not retrieved; only the
attribution and exposition in the 2025 source were checked. That provenance
question and an exhaustive novelty search remain open.

## Attribution and claim boundary

The conjecture, action coefficients, interval-volume formula, and known
constant-angle examples are not new. This draft develops a direct extension
of the flat interval density to one-tip regions, an explicit null truncation,
and a signed-kernel/coarea argument for arbitrary admissible graph caps with a
planar future boundary. A full novelty search and independent proof review
remain to be done. Do not describe this as a proof of the unrestricted
conjecture or a peer-reviewed result.

Source versions are pinned above. For audit of the local reading, the fetched
HTML snapshots had SHA-256 values:

```text
2501.00139v2.html  7d334942d771d5b80454758732a31b9069e5a68b0750eb1f1490a837678fcbaf
2007.13206v2.html  ef666f93cd321416f1bce7d8ff74a16f0b7a46a02af12dafbab34095de4ac806
```

The article bodies are retained only in the ignored local `sources/` cache,
not redistributed as part of the Git repository. HTML snapshot hashes can
change if arXiv regenerates its presentation; the pinned paper versions are
the mathematical references.
