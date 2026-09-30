# Passage audit for the general contract (#90)

Reading date: **2026-09-30**. Companion to the
[scope matrix and decisions](general-contract.md). This is a bounded primary
source audit plus a limited forward search, **not** an exhaustive novelty
search, independent verification of the articles' calculations, or peer review.
Downloaded article bodies remain in ignored `sources/`, not in Git.

## 1. What was actually checked

| Source and checked passages | Result / convention actually supported | Consequence and remaining uncertainty |
| --- | --- | --- |
| Dowker–Liu–Lloyd-Jones (DLL), [2501.00139v2](https://arxiv.org/html/2501.00139v2), §§2.3–2.7, §7, Appendix A; [published DOI](https://doi.org/10.1088/1361-6382/ae0be5) | (7)–(8) give the mean action; §2.4 distinguishes isolated/embedded counts; (11) is the **conjecture** with angle weight; §2.6 (14) uses volume of realisation; §2.7 changes the observable with smearing. §7 derives 2D lozenge/triangle evidence and tests cones through 11D with an integration-domain approximation | Do not turn local joint attribution or the cone approximation into a general localization theorem. Timelike divergences in (12) belong to #26. Signature is opposite to the repository's |
| Dowker, [2007.13206v2](https://arxiv.org/html/2007.13206v2), §§1–2, §3.1–3.3, §4 and §5 | (1.1), (1.8), (2.1)–(2.3) fix minimal layers and point/pair powers. §1 explicitly warns that the density limit and outer integral do not commute. Uses conformal factor `1 + b t²`; §2.1 drops higher curvature terms and **assumes** they do not cause divergences. (3.18), (3.25), (3.26), (4.14) recover bulk plus the appropriate joint term **to the retained curvature order** | It is not an exact general boundary/bulk theorem at fixed nonzero curvature. §5 explicitly requests bounds on omitted terms. The exact flat part of (4.9) is useful and separately proved in the repository. The slab has no joint; the 2D triangle is mixed. These are important topology/stratum calibrations, not all-boundary coverage |
| Buck–Dowker–Jubb–Surya (BDJS), [1502.05388v2](https://arxiv.org/html/1502.05388v2), §4 (49)–(76), with §2 and §5 for the distinction from added boundary actions | Flat Alexandrov interval, **fixed proper height**, unsmeared action. (57) gives `2(1-exp(-N))` in 2D; (63), (67) give 3D/4D joint volume. General-d series (68)–(72); immediately before (74) the text explicitly says Mathematica gives the limit for **d = 2,…,16**. (70)–(72) were suggested by computations through 20. The paragraph after (74) says a closed general-d asymptotic expression was difficult | Correct the earlier inventory's unqualified “arbitrary-dimensional result” attribution. This is substantial dimensional diamond evidence, not an inspected proof for every integer d. Need a later all-d proof or a proof of the general series asymptotic before claiming that coverage. Its separate GHY-like boundary observable is **not** an extra term to insert into our unchanged BDG action |
| Machet–Wang (MW), [2007.13192v2](https://arxiv.org/html/2007.13192v2), §1, §2 including (26), §3 (41)–(67), §4; Appendix A opening coordinate-transport discussion | Small causal diamonds in Riemann normal neighborhoods, curvature radius much larger than interval and discreteness scales. First-order curvature expansion of interval counts. §3.1 obtains the 2D limit; §3.2 explicitly focuses on **3, 4, 5**, evaluating asymptotic curvature coefficients with Mathematica, matching bulk plus perturbed joint area in (64)–(67). §4 retains the first-order qualification | Arbitrary-curvature tensor **components in a small-diamond expansion** are not arbitrary fixed curved geometry with all remainders controlled. Their §3 (46) also describes BDJS's range as 2–16. §4 explicitly proposes a null-plane-truncated diamond for future work, so do not claim priority for proposing that geometry |
| Joshua Chevalier, *The Discrete Causal Action and Holes in Spacetime* (2023), DLL reference [25] | DLL §2.6 attributes the weighted/overlap integration method to this source. DLL's bibliography gives author, title and year but no retrievable identifier/link | **Primary text not obtained, hence not reviewed.** The accessible description in DLL §2.6 and its Appendix B cross-region example was checked, not represented as a reading of Chevalier. Exact provenance/coverage remains open. No priority claim for overlap or the truncated-cap idea is permitted |
| Rafael Sorkin, [1908.10022v1](https://arxiv.org/pdf/1908.10022v1), introduction and §§5–6, especially (15)–(20) and the two-null-edge discussion | A null **ray** does not carry a finite additive angle without marking/rescaling data. The non-null/null formula introduces a reference length and an additive convention; two-null angles inherit markings. This paper concerns additive Lorentzian angles/continuum action conventions | The BDG `coth` weight must not be replaced by a logarithmic continuum corner term. The normal-ray rescaling calculation in the contract is explicit and separate from importing Sorkin's tangent-vector conventions/signatures |

### Normalization checks that prevent false agreement

1. In BDJS/MW the symbol for the null-coordinate interval constant is
   $`\widetilde c_d=2^{d/2}c_d`$, where our
   $`c_d=S_{d-2}/[2^{d-1}d(d-1)]`$ multiplies proper time to the power $`d`$.
   This follows from their $`1/\sqrt2`$-normalized radial null coordinates.
   Constants in their coefficient tables cannot be copied with our $`c_d`$
   without conversion. The [dimension ledger](dimension-kernels.md#1-sources-conventions-and-normalization-table)
   supplies the calibrated constants.
2. Inclusive interval cardinality `i + 1` in BDJS is our exclusive layer
   `k = i - 1`. MW labels by the number of strictly interior elements starting
   at zero. Polynomial coefficients include a factorial; discrete layer
   coefficients do not. Calibrate against explicit 2D and 4D actions, not just
   a generic printed index range (BDJS (49) and subsequent ranges differ).
3. MW writes a positive `alpha` in (42), unlike the negative Glaser/Dowker
   convention. Its explicit actions (48), (53)–(55), not a blind sign copy of
   (41), calibrate our positive point coefficient and negative pair bracket.
   The present action has no new GHY term, smearing length or subtraction.
4. The Planck-power-normalized action is used throughout the contract. The
   2D dimensionless observable is specified directly; do not extrapolate the
   Planck-length exponent formula through dimension two. The scalar-curvature
   convention must also be converted explicitly; the contract gives an exact
   conformal sign calibration matching Dowker's (2.8) at the origin.
5. Causal diamonds are ambient-causally-convex, so isolated and embedded
   interval counts agree there. That agreement says nothing about the hole,
   timelike-wall and non-convex examples in DLL. The same symbols for an action
   need not denote the same interval regime.

## 2. Relevant later work inspected, not an all-literature certification

The search used the arXiv version histories of the above papers, the INSPIRE
record for DLL (`2864359`), its `refersto:recid:2864359` query, and the bounded
INSPIRE query `title:"causal set" and date>2025` (first page, size 100;
seven records returned at this reading). The citing query returned two
records, both listed below. Index completeness and unpublished work were not
verified. Exact-title web attempts for Chevalier yielded search interstitials;
an arXiv author/topic search and an INSPIRE title/author search did not locate
the text. Search failure is an access limitation, not evidence of absence.

- **Karen Yeats**, *Combinatorial interpretation of the coefficients of the
  causal set d'Alembertian*, [2412.14036v3](https://arxiv.org/html/2412.14036v3).
  Checked §1's order/layer conventions and action formula, §3's even-dimensional
  simplification and §4's discussion. The contribution concerns combinatorial
  interpretations of the **known coefficients**, not a new global boundary
  theorem. The introductory action suppresses gravitational constants (its
  footnote says so). Do not treat an introductory summary of continuum limits
  as stronger than the cited primary hypotheses. Its revised version cites DLL;
  its original submission predates DLL.
- **Boguñá and Krioukov**, *Local d'Alembertian for causal sets*,
  [2506.18745v1](https://arxiv.org/html/2506.18745v1). Checked introduction and
  §III, especially (18)–(28) and the following limit-order discussion. Their
  noncompact-field examples and comparison of removing a spatial cutoff before
  or after the density limit are directly relevant warnings. They do **not**
  exhibit a counterexample to the complete normalized BDG action on an
  admissible fixed compact region. No endorsement of unrestricted Fubini for
  their noncompact integrals is needed here. Their replacement local operator
  is a different observable, not a repair silently imported into this project.
- **Sean A. Adamson and Petros Wallden**, *Benincasa–Dowker–Glaser causal set
  actions by quantum counting*, [2505.22217v2](https://arxiv.org/pdf/2505.22217v2),
  revised 21 May 2026. Checked abstract and §1 including §1.1's Algorithm 1
  and stated contribution. This estimates finite-order interval abundances and
  hence BDG actions; its computational complexity/error guarantee is not a
  continuum boundary theorem. The rest of its quantum-algorithm proof was not
  audited for this contract.

Other returned propagator, graph-observable and AQFT records were only title
screened, not full-text reviewed. No claim that these searches find all later
work, dissertations, corrections or related results under different terminology
is justified. In particular, the all-dimension diamond proof provenance and
Chevalier primary text remain unresolved research-library tasks for #81/#86.

## 3. Attribution decisions and novelty uncertainty

- The conjecture, coefficients, overlap method, finite-Poisson count identity,
  diamond calibrations and local curvature mechanism are prior work. The
  present contract makes no claim to discovering them.
- The inspected sources do not supply the particular general curved,
  variable-angle, fixed-geometry theorem in G-SS with a full normalized
  nonlocal remainder proof. **Not finding such a theorem in this bounded
  reading is not evidence that it is novel.**
- The repository's exact null-cap and restricted graph/two-face Lean results
  have their encoded scope. An implementation-agent audit does not establish
  first proof, independent correctness of the intended physical statement, or
  peer review. #94 and #86 retain those responsibilities.
- The first mixed pilot is selected for a usable all-partner interval geometry,
  not asserted to be a new physical result. Its actual asymptotic estimates
  remain #83/#84's work.
- **NARROW attribution now:** qualify the older literature inventory and
  dimensional diamond references using the explicit passage evidence above.
  Leave historical issue/PR reports intact. **STOP priority claims** pending
  primary-source access and a wider expert-assisted search. No proof gap is
  discharged by closing the contract issue.

## 4. Reproducible reading evidence

Pinned versions above are the mathematical references. Local snapshot hashes
are recorded only to identify this reading; regenerated arXiv HTML can change.
The articles are not redistributed. Failed unversioned/incorrect-version HTML
requests were replaced by the successful pinned HTML or PDF versions listed
here; no failed request counts as a reviewed source.

```text
2501.00139v2.html  7d334942d771d5b80454758732a31b9069e5a68b0750eb1f1490a837678fcbaf
2007.13206v2.html  ef666f93cd321416f1bce7d8ff74a16f0b7a46a02af12dafbab34095de4ac806
1502.05388v2.html  43321abe37ad061c2de821bc73b48865fcbb199dc7c090873c397f7224efb080
2007.13192v2.html  03158f61b9803a28c25faff3ab7ad76ef18310bc60fdca3cc25d7f3eaea57000
1908.10022v1.pdf   6ce1fddabd84afc0e270476b5c920b96463042b951007f37d351409136221ed6
2412.14036v3.html  96d8ff74ccd87206960d593f886159a2f57fa5b4d7021e09c548ccb35adede43
2506.18745v1.html  566103f639200a00b3642d65f9f37acff2df22dea809c424d3bae5b42babda79
2505.22217v2.pdf   94e729ba816989be91110fef0746c60069e6a7929fafb9b84c131e27da5b3b7c
```
