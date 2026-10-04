"""Static website contract checks; no Lean validation or research theorem claims."""
import pathlib
import re
import subprocess
import unittest
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit

ROOT = pathlib.Path(__file__).resolve().parent
REVISION = "8b05befffd4a24fea3724f2d5ed41d33684b9fc5"


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.links, self.ids, self.refs = [], [], []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.append(attrs["id"])
        for name in ("href", "src"):
            if name in attrs:
                self.refs.append(attrs[name])
        if tag == "a":
            self.links.append(attrs.get("href", ""))


class ProofSpineTests(unittest.TestCase):
    def test_local_links_and_unique_ids(self):
        for path in (ROOT / "site").glob("*.html"):
            page = Page(path.read_text())
            self.assertEqual(len(page.ids), len(set(page.ids)), path.name)
            for ref in page.refs:
                url = urlsplit(ref)
                if url.scheme or url.netloc:
                    continue
                target = path.parent / unquote(url.path) if url.path else path
                self.assertTrue(target.is_file(), (path.name, ref))
                if url.fragment and target.suffix == ".html":
                    self.assertIn(unquote(url.fragment), Page(target.read_text()).ids, ref)

    def test_source_references_are_pinned_and_exist_at_assessed_main(self):
        text = (ROOT / "site/proof-spine.html").read_text()
        refs = Page(text).links
        source_count = 0
        for ref in refs:
            if "/blob/" not in ref:
                continue
            match = re.fullmatch(r"https://github.com/q5m-ai/causal-set-emergence/blob/([0-9a-f]{40})/(.+?)(?:#.*)?", ref)
            self.assertIsNotNone(match, ref)
            revision, file = match.groups()
            self.assertEqual(revision, REVISION)
            result = subprocess.run(["git", "cat-file", "-e", f"{revision}:{file}"], cwd=ROOT, capture_output=True)
            self.assertEqual(result.returncode, 0, ref)
            fragment = urlsplit(ref).fragment
            if fragment and file.endswith(".md"):
                source = subprocess.check_output(["git", "show", f"{revision}:{file}"], cwd=ROOT, text=True)
                headings = re.findall(r"^#+ (.+)$", source, re.M)
                slugs = {re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-") for heading in headings}
                self.assertIn(fragment, slugs, ref)
            source_count += 1
        self.assertGreater(source_count, 35)
        self.assertIn('datetime="2026-10-03"', text)

    def test_page_contract_and_navigation(self):
        text = (ROOT / "site/proof-spine.html").read_text()
        for name in ("Conventional written proof", "Lean-checked result", "Symbolic / numerical evidence", "Conditional result", "Open obligation", "sample-wise", "independent human", "x₃ = 0", "including equality"):
            self.assertIn(name, text)
        self.assertEqual(len(re.findall(r'class="proof-step"', text)), 7)
        for name in ("index", "dimensions", "proof-spine"):
            self.assertIn('href="proof-spine.html"', (ROOT / f"site/{name}.html").read_text())

    def test_math_is_not_parsed_as_html(self):
        text = (ROOT / "site/proof-spine.html").read_text()
        expressions = re.findall(r"\\\((.*?)\\\)|\\\[(.*?)\\\]", text.split("<main")[1], re.S)
        self.assertEqual(len(expressions), 121)
        for expression in expressions:
            self.assertNotIn("<", "".join(expression), expression)

    def test_visual_math_model(self):
        subprocess.run(["node", "--test", "scripts/test-proof-spine.mjs"], cwd=ROOT, check=True, capture_output=True, text=True)


if __name__ == "__main__":
    unittest.main()
