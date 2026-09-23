"""Math authoring regressions, not a substitute for GitHub's browser preview."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from check_markdown import github_documents, lint_markdown, markdown_paths


class MarkdownMathTest(unittest.TestCase):
    def test_github_inline_and_fenced_math(self):
        source = r"""The limit $`\rho\to\infty`$ and $h>0$:

```math
\mathrm{continuumMean}_\rho(M_h)
= \int_J \coth\theta\,dA. \tag{1}
```
"""
        self.assertEqual(lint_markdown(source), [])

    def test_legacy_delimiters(self):
        for source in (r"\(x\)", "\\[\nx=1\n\\]"):
            with self.subTest(source=source):
                self.assertTrue(lint_markdown(source))

    def test_issue_19_accidental_heading(self):
        source = "$$\nx\n=\ny\n$$\n"
        errors = lint_markdown(source)
        self.assertEqual([line for line, _ in errors], [1, 5])
        self.assertIn("math fence", errors[0][1])

    def test_issue_19_macro_rejected_by_client_not_markdown_api(self):
        for source in (r"$`\operatorname{Area}(J)`$", r"$\operatorname{Area}(J)$",
                       "```math\n\\operatorname{Area}(J)\n```\n"):
            with self.subTest(source=source):
                self.assertIn("unsupported macro", lint_markdown(source)[0][1])

    def test_other_rejected_and_custom_macros(self):
        for macro in ("phantom", "DeclareMathOperator", "require", "newcommand"):
            with self.subTest(macro=macro):
                self.assertTrue(lint_markdown(f"$`\\{macro}{{x}}`$"))

    def test_literal_code_and_comments_are_not_math(self):
        source = r"""Use `\(x\)`? No. Literal ``$`\operatorname{Area}`$``.
<!-- \[ $ \operatorname{x} -->
````markdown
```math
\operatorname{bad}
```
\(bad\) $$
````
~~~lean
-- \[ \operatorname{x}
~~~
"""
        self.assertEqual(lint_markdown(source), [])

    def test_list_and_blockquote_math_fences(self):
        source = "1. Item\n\n   ```math\n   x=1\n   ```\n\n> ```math\n> x=1\n> ```\n"
        self.assertEqual(lint_markdown(source), [])
        self.assertTrue(lint_markdown(source.replace("x=1", r"\operatorname{x}")))

    def test_unclosed_and_mislabeled_fences(self):
        for source in ("```math\nx", "```Math\nx\n```", "```math title\nx\n```"):
            with self.subTest(source=source):
                self.assertTrue(lint_markdown(source))

    def test_fence_closer_must_match_type_and_length(self):
        self.assertTrue(lint_markdown("````math\nx\n```\n"))
        self.assertTrue(lint_markdown("```math\nx\n~~~\n"))
        self.assertEqual(lint_markdown("```math\nx\n````\n"), [])

    def test_do_not_nest_delimiters_in_fence(self):
        for math in ("$$x$$", r"\[x\]", r"\(x\)"):
            self.assertTrue(lint_markdown(f"```math\n{math}\n```"))

    def test_malformed_inline_and_literal_dollars(self):
        for source in ("$x", "$`x$", "$x\n\ny$", "$ $"):
            with self.subTest(source=source):
                self.assertTrue(lint_markdown(source))
        self.assertEqual(lint_markdown(r"Costs \$5; $`x`$ and $y$."), [])
        self.assertTrue(lint_markdown(r"Two backslashes \\$ are not a dollar escape"))

    def test_diagnostic_line_after_code_and_comments(self):
        source = "```text\nignore $\n```\n<!--\nignore $\n-->\n$`\\operatorname{x}`$"
        self.assertEqual(lint_markdown(source)[0][0], 7)

    def test_repository_markdown(self):
        for path in markdown_paths():
            with self.subTest(path=path):
                self.assertEqual(lint_markdown(path.read_text()), [])

    def test_cli_failure_and_success(self):
        script = Path(__file__).with_name("check_markdown.py")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "issue-body.md"
            for source, status in [(r"\(x\)", 1), ("$`x`$", 0)]:
                path.write_text(source)
                result = subprocess.run([sys.executable, str(script), str(path)],
                                        capture_output=True, text=True, check=False)
                self.assertEqual(result.returncode, status, result.stderr)

    @patch("check_markdown.subprocess.check_output")
    def test_remote_inventory_all_states_pagination_and_reviews(self, call):
        # Pages deliberately split to catch first-page-only audits.
        call.side_effect = [
            json.dumps([[{"number": 1, "html_url": "issue", "body": "one"}],
                        [{"number": 2, "html_url": "pr", "body": "two", "pull_request": {}}]]),
            json.dumps([[{"html_url": "comment", "body": "three"}]]),
            json.dumps([[{"html_url": "review-comment", "body": "four"}]]),
            json.dumps([[{"html_url": "review", "body": None}]]),
        ]
        self.assertEqual(github_documents("owner/repo"), [
            ("issue", "one"), ("pr", "two"), ("comment", "three"),
            ("review-comment", "four"), ("review", ""),
        ])
        commands = [args[0][0] for args in call.call_args_list]
        self.assertIn("state=all", commands[0][-1])
        self.assertTrue(commands[-1][-1].endswith("pulls/2/reviews?per_page=100"))
        for command in commands:
            self.assertEqual(command[:4], ["gh", "api", "--paginate", "--slurp"])
            self.assertNotIn("PATCH", command)

    @patch("check_markdown.subprocess.check_output", side_effect=subprocess.CalledProcessError(1, "gh"))
    def test_remote_fetch_failure_is_not_a_clean_audit(self, _call):
        with self.assertRaises(subprocess.CalledProcessError):
            github_documents("owner/repo")


if __name__ == "__main__":
    unittest.main()
