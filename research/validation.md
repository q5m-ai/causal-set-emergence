# Validation receipt — preparation only

**16 October 2026.** Mathematics is pinned to
`9e0068f91c219fe61984d20fdb3f6939eab907c4` (**S**). A final fetch confirmed
that `origin/issue-81-general-coverage` still named S. This package does not
change mathematical sources, certificates, Lean, dependencies or workflows.
Read `git rev-parse HEAD` for the presentation revision; this is not a release tag.

## Checks actually completed locally

| Check | Observed result | What it does not establish |
| --- | --- | --- |
| `python3 check_markdown.py` and `python3 -m unittest -v test_check_markdown` | 106 Markdown documents, zero reported problems; 20 guard tests pass | Browser rendering or mathematical correctness |
| `python3 -m unittest -v test_research_release` | 11 tests pass, including all 42 pinned mathematical-source hashes, packet links, manifest boundaries, static HTML and feasibility arithmetic | Proof validity, human acceptance or empirical support |
| Six focused mathematical diagnostic modules listed in `artifact.md` | 83 tests pass in about 9 seconds, including selected model-certificate nodes | Uniform physical transfer, complete-action certification or the full repository test suite |
| `check_symbolic.py` | All symbolic checks pass | The global geometric remainder arguments |
| `reproduce.py`, compared with `RESULTS.md` | Byte-for-byte identical output | CO's complete asymptotic; these are older finite-density consistency examples |
| `curved4_focal_certificate.py --head-checks` and saved-certificate `--replay` | 25 exact rational checks pass; arithmetic replay gives the stated positive model enclosure | Full 2,527-node regeneration or model-to-physical transfer |
| `test_proof_spine` and `node scripts/test-proof-spine.mjs` | Six Python and six JavaScript tests pass | Extension of the old teaching snapshot's theorem scope |
| Syntax checks for `site/home-3d.js`, `site/order-fraction-worker.js` and `scripts/check-research-browser.mjs`; `git diff --check` | Pass | Runtime accessibility or proof acceptance |
| `python3 research/estimate_signals.py --firas /tmp/cse-literature/firas-spectrum` | DHS upper scale 8.94×10⁻¹³; 43 FIRAS bins, 68.05–639.46 GHz, peak-bin error 46.94 ppm | A measured causal-set signal, covariance-aware fit or new bound |

The Python environment was 3.12.3 with the exact five versions in
`requirements.txt`; Node was 22.22.0. The 120 Python tests above are a
**focused subset**, not a fresh full repository run. No new full Lean audit
or full model-certificate regeneration was performed or is implied.

## Browser and print inspection

- `scripts/check-research-browser.mjs` passed at 1280px desktop and 390px mobile,
  light and dark, with JavaScript disabled and reduced motion requested.
  The page made only its three local HTML/CSS requests; no external resources
  were needed. There was no document-width overflow or failed response.
- The first keyboard focus is the skip link; activating it focuses `main`.
  Navigation on all three existing teaching pages still exposes the review
  entry at mobile width. Status is expressed in text, not just color.
- Desktop/mobile claim cards, the illustration and its non-proof caption,
  dark presentation, navigation and print account were visually inspected.
  The A4 account measures about 906 CSS pixels against 1,001 available and
  is followed by an explicit page break. A local PDF was generated; no PDF
  was uploaded or submitted. This is not a comprehensive assistive-technology
  or accessibility-conformance audit.
- All **21 new Markdown math fragments** (20 manuscript, one experimental)
  were rendered in a live GitHub browser context using GitHub's client-side
  renderer, then visually inspected in contact sheets. No macro error,
  literal TeX, missing expression or clipped display remained. The Markdown
  API and MathML/error counts alone were not used as a success criterion.
  Preview HTML was inserted only into the local browser DOM; nothing was
  posted to the discussion page used to load the renderer.
- Initial browser startup failed because this minimal host lacked shared
  libraries. Existing local Chromium libraries supplied them. The first math
  preview then exposed missing Greek glyphs; enabling the existing math-font
  configuration fixed that environment issue. The initial print account was
  too tall; the print stylesheet was compacted and the checks rerun. These
  failed preliminary previews are not passed off as successful validation.

Browser screenshots, the PDF and machine receipts are local temporary outputs;
run the committed browser script to regenerate the site evidence. The final
Markdown equation source is unchanged since the successful visual preview.

## Scope and current-source reconciliation

The final issue metadata check found #24/#81/#94/#86 unchanged and still open.
The separately inspected, **unmerged** #180 advanced during preparation from
`47e268c44bb1ba0083b4cf3509bc07c088da3f0a` to
`a8fcb2465430c9d169cca67d942209c663bb7c74`. Its new phase-freeze source was read
and recorded separately: PF3-L remains unproved and arbitrary smooth curved
3D remains UNKNOWN. Its older PR-body test receipt is not attributed to its
new head or to this package. No part of #180 was merged or cherry-picked.

This is presentation and evidence preparation, **not independent human review**.
No launch, deployment, manuscript submission, outreach, collaborator contact,
agent launch, paid compute, bulk science download, issue closure or merge was
performed. Any later CI result belongs to its recorded exact head and is not
substituted for the local checks above. Image publication and production
promotion remain guarded to `main`; this work targets integration only.
