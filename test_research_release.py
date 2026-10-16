"""Offline presentation/evidence and feasibility-arithmetic checks, not proof tests."""
import hashlib
from html.parser import HTMLParser
import json
import math
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from research.estimate_signals import (
    dhs_fractional_rms_bound, estimates, firas_summary, toy_delay, transport_strength,
)

ROOT = Path(__file__).resolve().parent
S = "9e0068f91c219fe61984d20fdb3f6939eab907c4"


class SignalScaleTests(unittest.TestCase):
    def test_dhs_formula_and_area_duration_scaling(self):
        f = dhs_fractional_rms_bound
        self.assertAlmostEqual(f(1, 1, 1, 1, 0.5)**2, 64 * math.pi + 32)
        self.assertAlmostEqual(f(1, 4, 1, 1, 0.5), f(1, 1, 1, 1, 0.5) / 2)
        self.assertLess(f(1, 1, 2, 1, 0.5), f(1, 1, 1, 1, 0.5))

    def test_dhs_source_example_is_an_upper_scale(self):
        value = estimates()["DHS_eq70_fractional_rms_upper_scale"]
        self.assertAlmostEqual(value / 1e-13, math.sqrt(80), places=12)

    def test_transport_units_and_sign(self):
        self.assertAlmostEqual(transport_strength(6.62607015e-34, 2, 4), 0.5)
        self.assertEqual(transport_strength(-6.62607015e-34, 2, 4), -0.5)
        self.assertEqual(transport_strength(1, 0, 1), 0)

    def test_toy_comparison_not_a_cosmological_prediction(self):
        self.assertAlmostEqual(toy_delay(2, 1.22089e19 / 10, 1), 0.2)
        self.assertAlmostEqual(toy_delay(2, 1.22089e19 / 10, 2), 0.02)
        result = estimates()
        self.assertIn("not predictions", result["status"])
        ratio = (result["toy_30GeV_30day_differential_linear_seconds"] /
                 result["toy_1eV_30day_differential_linear_seconds"])
        self.assertAlmostEqual(ratio / 1e10, 3)

    def test_invalid_scales_rejected(self):
        for args in ((0, 1, 1, 1, 0.1), (1, 1, 1, 1, 1)):
            with self.assertRaises(ValueError):
                dhs_fractional_rms_bound(*args)
        with self.assertRaises(ValueError):
            transport_strength(1, 1, 0)
        with self.assertRaises(ValueError):
            toy_delay(1, 1, 3)

    def test_firas_kjy_mjy_and_inverse_cm_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "table.txt"
            path.write_text("# five columns\n2 100 5 10 4\n5 200 -3 20 8\n")
            result = firas_summary(path)
            self.assertEqual(result["rows"], 2)
            self.assertEqual(result["peak_bin_one_sigma_ppm"], 100)
            self.assertAlmostEqual(result["frequency_GHz_range"][0], 59.9584916)
            for bad in ("", "2 100 5 10\n", "2 100 5 -10 4\n"):
                path.write_text(bad)
                with self.assertRaises(ValueError):
                    firas_summary(path)


class ReviewPackageTests(unittest.TestCase):
    def test_manifest_preserves_integration_and_unmerged_boundary(self):
        manifest = json.loads((ROOT / "research/evidence.json").read_text())
        self.assertEqual(manifest["mathematics_commit"], S)
        self.assertEqual(manifest["integration_branch"], "issue-81-general-coverage")
        pr = manifest["excluded_pull_request"]
        self.assertEqual(pr["number"], 180)
        self.assertEqual(pr["state"], "OPEN")
        self.assertNotEqual(pr["headRefOid"], S)
        excluded = manifest["excluded_sources"]
        self.assertEqual({item["commit"] for item in excluded},
                         {pr["headRefOid"], pr["initial_inspected_head"]})
        self.assertTrue(all(item["commit"] != S for item in excluded))
        self.assertEqual({i["number"] for i in manifest["issues"]}, {24, 81, 94, 86})
        self.assertTrue(all(i["state"] == "open" for i in manifest["issues"]))

    def test_source_hashes_at_exact_mathematics_commit(self):
        present = subprocess.run(["git", "cat-file", "-e", S + "^{commit}"],
                                 cwd=ROOT, capture_output=True).returncode == 0
        if not present:
            self.skipTest("Pinned commit not present (e.g. shallow CI); fetch S for artifact verification")
        manifest = json.loads((ROOT / "research/evidence.json").read_text())
        self.assertGreaterEqual(len(manifest["source_files"]), 30)
        for item in manifest["source_files"]:
            with self.subTest(path=item["path"]):
                data = subprocess.check_output(["git", "show", f"{S}:{item['path']}"], cwd=ROOT)
                self.assertEqual(hashlib.sha256(data).hexdigest(), item["sha256"])

    def test_local_reading_links_exist(self):
        for path in (ROOT / "research").glob("*.md"):
            for target in re.findall(r"\]\(([^\s)]+)\)", path.read_text()):
                if "://" in target or target.startswith("#"):
                    continue
                with self.subTest(document=path.name, target=target):
                    self.assertTrue((path.parent / target.split("#")[0]).exists())

    def test_pinned_links_have_real_source_paths(self):
        manifest = json.loads((ROOT / "research/evidence.json").read_text())
        paths = {item["path"] for item in manifest["source_files"]}
        for doc in (ROOT / "research").glob("*.md"):
            for path in re.findall(r"/blob/" + S + r"/([^\s)#]+)", doc.read_text()):
                with self.subTest(document=doc.name, path=path):
                    self.assertIn(path, paths)

    def test_static_review_page_does_not_require_scripts(self):
        path = ROOT / "site/research.html"
        class Page(HTMLParser):
            def __init__(self):
                super().__init__()
                self.ids, self.local_links, self.scripts = [], [], []
            def handle_starttag(self, tag, attrs):
                attrs = dict(attrs)
                if "id" in attrs:
                    self.ids.append(attrs["id"])
                if tag == "script":
                    self.scripts.append(attrs)
                if tag in ("a", "link", "img"):
                    href = attrs.get("href", attrs.get("src", ""))
                    if href and ":" not in href:
                        self.local_links.append(href)
        html = path.read_text()
        page = Page()
        page.feed(html)
        self.assertFalse(page.scripts)
        # Static-site readers must not depend on the review branch surviving.
        for revision in re.findall(r"causal-set-emergence/blob/([^/]+)/", html):
            self.assertRegex(revision, r"^[0-9a-f]{40}$")
        self.assertEqual(len(page.ids), len(set(page.ids)))
        for link in page.local_links:
            if link.startswith("#"):
                self.assertIn(link[1:], page.ids)
            else:
                self.assertTrue((path.parent / link.split("#")[0].split("?")[0]).exists(), link)
        self.assertIn('href="#main"', html)
        self.assertIn('lang="en"', html)
        self.assertIn("Illustration, not proof", html)
        self.assertIn(S, html)
        self.assertIn("UNKNOWN", html)
        self.assertIn("not launched", html)


if __name__ == "__main__":
    unittest.main()
