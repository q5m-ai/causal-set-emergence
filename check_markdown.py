"""Check the repository's GitHub math authoring conventions (stdlib only).

This is a focused lint, not a Markdown/TeX renderer. GitHub's Markdown API and
browser preview are separate validation steps; see notes/github-math.md.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess


# GitHub's math-renderer rejects these even though MathJax may support them.
# Observed in GitHub's browser renderer; see notes/github-math.md.
REJECTED_MACROS = frozenset("""
DeclareMathOperator DeclarePairedDelimiters renewtagform newtagform
colorbox fcolorbox hphantom vphantom phantom operatorname Newextarrow
definecolor mathchoice unicode mmlToken boldsymbol
""".split())
# Do not depend on custom definitions or dynamically loaded TeX packages.
CUSTOM_MACROS = frozenset("newcommand renewcommand providecommand def gdef edef let require".split())
FENCE = re.compile(r"^\s*(?:>\s*)*(`{3,}|~{3,})(.*)$")
CODE_SPAN = re.compile(r"(?<!`)(`+)(?!`)[\s\S]*?(?<!`)\1(?!`)")
PROTECTED_MATH = re.compile(r"\$`([^`]*?)`\$")
LEGACY_DELIMITER = re.compile(r"\\[()\[\]]")


def blank(text):
    """Mask syntax without changing source offsets or diagnostic line numbers."""
    return re.sub(r"[^\n]", " ", text)


def escaped(text, position):
    start = position
    while start and text[start - 1] == "\\":
        start -= 1
    return (position - start) % 2 == 1


def lint_markdown(text):
    """Return (line, message) diagnostics, ignoring literal code examples.

    Recognizes fences (including indented list/blockquote fences), code spans,
    HTML comments, plain dollar math, and GitHub's dollar/backtick inline math.
    It deliberately requires math fences instead of double-dollar displays.
    """
    errors = []

    def report(offset, message):
        errors.append((text.count("\n", 0, offset) + 1, message))

    def check_math(source, offset):
        for match in re.finditer(r"\\([A-Za-z]+)", source):
            macro = match[1]
            if macro in REJECTED_MACROS | CUSTOM_MACROS:
                report(offset + match.start(), f"unsupported macro \\{macro}; use portable built-ins")
        if (any(char == "$" and not escaped(source, position)
                for position, char in enumerate(source))
                or LEGACY_DELIMITER.search(source)):
            report(offset, "do not nest math delimiters inside math")

    # HTML comments may contain literal instructions, not rendered prose.
    visible = re.sub(r"<!--[\s\S]*?-->", lambda m: blank(m[0]), text)
    prose = []
    fence = None
    offset = 0
    for line in visible.splitlines(keepends=True):
        match = FENCE.match(line)
        if fence is not None:
            marker, language, start = fence
            if (match and match[1][0] == marker[0]
                    and len(match[1]) >= len(marker) and not match[2].strip()):
                fence = None
            elif language == "math":
                check_math(line, offset)
            prose.append(blank(line))
        elif match:
            marker, info = match.groups()
            language = info.strip()
            fence = (marker, language, offset)
            if language.lower().startswith("math") and language != "math":
                report(offset, "use exactly ```math, without attributes or capitalization")
            prose.append(blank(line))
        else:
            prose.append(line)
        offset += len(line)
    if fence is not None:
        report(fence[2], "unclosed code/math fence")
    prose = "".join(prose)

    # Code spans are literal, except GitHub's $`...`$ math syntax.
    def mask_code(match):
        before, after = match.start() - 1, match.end()
        if (match[1] == "`" and before >= 0 and prose[before] == "$"
                and not escaped(prose, before) and prose[after:after + 1] == "$"):
            return match[0]
        return blank(match[0])

    prose = CODE_SPAN.sub(mask_code, prose)

    def mask_math(match):
        if escaped(prose, match.start()):
            return match[0]
        check_math(match[1], match.start() + 2)
        return blank(match[0])

    prose = PROTECTED_MATH.sub(mask_math, prose)
    for match in LEGACY_DELIMITER.finditer(prose):
        report(match.start(), "legacy math delimiter; use $`...`$ or a math fence")
    for match in re.finditer(r"\$\$", prose):
        if not escaped(prose, match.start()):
            report(match.start(), "use a math fence, not $$ (Markdown can consume equations)")
    # Mask double dollars after reporting, so they cannot pair as inline math.
    prose = re.sub(r"\$\$", "  ", prose)
    opening = None
    for match in re.finditer(r"\$", prose):
        position = match.start()
        if escaped(prose, position):
            continue
        if opening is None:
            opening = position
        else:
            source = prose[opening + 1:position]
            if not source.strip() or "\n\n" in source or "`" in source:
                report(opening, "malformed inline math; use a complete $`...`$ span")
            else:
                check_math(source, opening + 1)
            opening = None
    if opening is not None:
        report(opening, "unmatched dollar; close inline math or escape a literal dollar")
    return sorted(set(errors))


def markdown_paths():
    """Include tracked and new Markdown, but not ignored dependencies/builds."""
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        text=True,
    ).split("\0")
    return sorted({Path(name) for name in names if name
                   and Path(name).suffix.lower() in {".md", ".markdown"}
                   and Path(name).is_file()})


def github_documents(repository):
    """Read all open/closed issue and PR bodies, comments, and review bodies.

    gh handles authentication and pagination. This never edits remote content.
    Pull requests appear in the issues endpoint too; do not fetch them twice.
    """
    def fetch(endpoint):
        pages = json.loads(subprocess.check_output(
            ["gh", "api", "--paginate", "--slurp", endpoint], text=True,
        ))
        return [item for page in pages for item in page]

    base = f"repos/{repository}"
    issues = fetch(f"{base}/issues?state=all&per_page=100")
    documents = list(issues)
    documents += fetch(f"{base}/issues/comments?per_page=100")
    documents += fetch(f"{base}/pulls/comments?per_page=100")
    for issue in issues:
        if "pull_request" in issue:
            documents += fetch(f"{base}/pulls/{issue['number']}/reviews?per_page=100")
    return [(item["html_url"], item.get("body") or "") for item in documents]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--github", metavar="OWNER/REPO",
                        help="read-only audit of all issue/PR bodies, comments, and reviews via gh")
    parser.add_argument("paths", nargs="*", type=Path,
                        help="Markdown files, including saved issue/PR bodies; default: repository Markdown")
    args = parser.parse_args()
    if args.github:
        if args.paths or not re.fullmatch(r"[\w.-]+/[\w.-]+", args.github):
            parser.error("--github needs OWNER/REPO and cannot be combined with file paths")
        documents = github_documents(args.github)
    else:
        documents = [(str(path), path.read_text(encoding="utf-8"))
                     for path in args.paths or markdown_paths()]
    count = 0
    for name, body in documents:
        for line, message in lint_markdown(body):
            print(f"{name}:{line}: {message}")
            count += 1
    print(f"Checked {len(documents)} Markdown documents; {count} problem(s).")
    return bool(count)


if __name__ == "__main__":
    raise SystemExit(main())
