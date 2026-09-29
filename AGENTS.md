# Repository instructions

## Mathematics and verification status

- Preserve mathematical statements, hypotheses, equation numbers, and the
  distinction between draft arguments, checked deterministic results, the
  separately proved Poisson-expectation bridge, and unproved sample-wise
  convergence. Formatting changes must not change claims.
- Keep Lean declarations and theorem-contract examples as code, not rendered
  LaTeX. Do not rewrite historical issue/PR status as part of a formatting pass.

## Lean proof-check workflow

- Read [the Lean setup and measured checker workflow](formal/README.md#reproduce)
  before working on formal proofs. After fetching the intended base, use
  `cd formal && ./check.sh --incremental --base origin/main` for edit-loop
  feedback. The base must be an ancestor of the branch; do not mistake this
  changed-source check for a full audit.
- Before handing off a mathematical result, run `cd formal && ./check.sh` on
  the final integrated commit. It builds, audits every local Lean source with
  warnings as errors and the transitive-axiom rule, then runs the aggregate
  audit. The default is two workers; adjust with `--workers N` only after
  checking memory/swap headroom. GitHub CI does not replace this local gate.

## GitHub-compatible mathematics

Follow [the GitHub math authoring and validation guide](notes/github-math.md)
for **all Markdown files, issue/PR bodies, comments, and reviews**.

- Use fenced `math` blocks for display equations and dollar/backtick spans for
  inline math. Do not use raw `\[...\]`, `\(...\)`, or double-dollar displays.
- Use portable built-ins such as `\mathrm{continuumMean}`. GitHub rejects
  `\operatorname` and other macros even when a local MathJax preview accepts them.
- Run `python3 check_markdown.py` and `python3 -m unittest -v test_check_markdown`
  before committing Markdown changes. For a remote audit, run
  `python3 check_markdown.py --github q5m-ai/causal-set-emergence` (read-only).
- Preview changed equations on GitHub. A successful Markdown API response or a
  `math-renderer` element **does not prove** that browser-side math rendering
  succeeded. Check for macro errors, literal TeX, missing equations, and layout.
- Use body files when publishing with `gh`; avoid shell interpolation of dollar
  signs and backslashes. Preserve code samples and edit only broken prose/math.
