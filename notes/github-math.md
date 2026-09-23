# Keeping mathematics readable on GitHub

These conventions apply to repository Markdown, READMEs, issues, pull requests,
comments, and reviews. GitHub uses **two stages**: Markdown parsing, then a
restricted browser-side math renderer. Working in a local LaTeX/MathJax viewer
or passing the Markdown API alone is not sufficient.

## Authoring conventions

### Inline equations

Prefer GitHub's dollar/backtick syntax. The backticks protect TeX from Markdown
emphasis and escaping rules:

```markdown
The width is $`\varepsilon=\rho^{-1/4}`$ and $`0<\lVert\nabla h\rVert<1`$.
```

The width is $`\varepsilon=\rho^{-1/4}`$ and $`0<\lVert\nabla h\rVert<1`$.

Ordinary `$...$` inline math is also supported, but do not mix the two delimiter
styles within an expression. Escape literal currency dollars outside math as
`\$`. Keep an inline expression in one paragraph. Avoid putting complicated
math (especially expressions containing `|`) in Markdown tables; move it to a
separate display rather than relying on competing table/TeX escaping rules.

### Display equations

Use a fenced `math` block, **without additional math delimiters inside it**:

````markdown
```math
\mathrm{Area}(J) = \int_J 1\,dA.
```
````

```math
\mathrm{Area}(J) = \int_J 1\,dA.
```

Within a list, indent the entire fence and its contents to the list item's
content column. Use blank lines around the block for readability. Equation
numbers such as `\tag{19}` may stay inside the math fence; preserve existing
numbers and references. For multiline alignment use an `aligned` environment
inside the fence, not Markdown line breaks.

Do **not** use `\[...\]` or `\(...\)` in Markdown prose. Do not use `$$`
display delimiters in this repository, even though GitHub documents them:
Markdown can consume their contents first. In issue #19, a standalone `=` line
became a Setext heading underline, turning half the equation into a heading.
Fenced math prevents that failure.

### Commands and literal code

- Use portable built-ins: `\mathrm{Area}(J)`, `\mathrm{continuumMean}`,
  `\frac`, `\sqrt`, `\lVert`, `\rVert`, and standard named functions such as
  `\log`, `\cosh`, and `\coth`.
- Do not use `\operatorname` or `\DeclareMathOperator`. GitHub's browser
  renderer rejects them, even when the Markdown API emits a valid-looking
  `math-renderer` element. Use `\mathrm{...}` for the upright names above;
  check spacing/limits explicitly when replacing other kinds of operators.
- Do not define custom macros or load TeX packages. Commands such as
  `\phantom`, `\colorbox`, `\definecolor`, and `\unicode` are also rejected.
  The focused known-bad list lives in `check_markdown.py`; it is not a complete
  specification of GitHub's changing renderer.
- Keep Lean statements, identifiers, shell commands, and intentional plaintext
  formulae in code spans or `lean`/`text` fences. Code notation is not broken
  LaTeX and should not be mechanically translated.
- Preserve the actual mathematics: hypotheses, signs, integration domains,
  normalization constants, equation labels, and verification status.

## Validation before publishing

From the repository root (Python 3.11+, standard library only):

```sh
python3 check_markdown.py
python3 -m unittest -v test_check_markdown
# Check a draft issue/PR body before sending it:
python3 check_markdown.py /tmp/pr-body.md
# Optional authenticated, read-only remote audit (requires gh):
python3 check_markdown.py --github q5m-ai/causal-set-emergence
```

The default scan includes tracked and new, nonignored `.md`/`.markdown` files.
It skips literal code fences, code spans, and HTML comments; math fences are
checked. It catches legacy/double-dollar delimiters, known rejected/custom
macros, unclosed fences, and common malformed inline delimiters. It is a
focused authoring lint, **not a full Markdown or TeX parser**, and cannot certify
all commands, layout, or mathematical correctness. CI runs the offline lint
and its regression tests; it does not claim a browser-rendering check.

The remote audit paginates all open **and closed** issues and PRs, conversation
comments, inline review comments, and review bodies. It never edits anything.
Preserve existing content and authorship when fixing remote formatting; do not
replace other contributors' comments or use the audit as a reason to rewrite
historical mathematical claims. Discussions are a separate GitHub API and are
not included in this issue/PR audit.

### Check both rendering stages

1. Inspect the source diff. Confirm that only delimiters/presentation changed
   unless a mathematical correction was separately intended.
2. Check Markdown parsing with GitHub's **Preview** tab, a rendered branch file,
   or the authenticated Markdown API. For example:

   ```sh
   python3 - README.md <<'PY' | gh api markdown --input - > /tmp/github-preview.html
   import json, pathlib, sys
   print(json.dumps({
       "text": pathlib.Path(sys.argv[1]).read_text(),
       "mode": "gfm",
       "context": "q5m-ai/causal-set-emergence",
   }))
   PY
   ```

   Count the `math-renderer` elements against the intended inline/display
   expressions; ensure equations did not become headings, ordinary code, or
   literal prose. A raw saved HTML fragment alone lacks GitHub's renderer JS.
3. **Let the browser finish rendering on GitHub.** Inspect every changed
   equation for red error boxes, literal TeX, missing expressions, clipping,
   and incorrect grouping. Macro restrictions are enforced at this stage.
   For browser automation, require actual `math-renderer math` output (MathML
   in the current renderer), no `merror`, and no rendering-error fallback—not
   merely the presence of the outer custom element. Renderer details can
   change; recheck rather than assuming an old API response is sufficient.
4. Use `gh issue edit NUMBER --body-file /tmp/issue-body.md` or
   `gh pr edit NUMBER --body-file /tmp/pr-body.md` to publish approved changes,
   then verify the saved body. Use quoted heredocs/body files, not interpolated
   shell strings that can eat dollar signs or backslashes.

## References

- [GitHub: Writing mathematical expressions](https://docs.github.com/en/get-started/writing-on-github/working-with-advanced-formatting/writing-mathematical-expressions)
- [GitHub REST Markdown API](https://docs.github.com/en/rest/markdown/markdown)
- [Issue #19: original delimiter and macro rendering failures](https://github.com/q5m-ai/causal-set-emergence/issues/19)
