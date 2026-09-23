# Repository instructions

## Mathematics and verification status

- Preserve mathematical statements, hypotheses, equation numbers, and the
  distinction between draft arguments, checked deterministic results, and the
  still-open probability bridge. Formatting changes must not change claims.
- Keep Lean declarations and theorem-contract examples as code, not rendered
  LaTeX. Do not rewrite historical issue/PR status as part of a formatting pass.

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
