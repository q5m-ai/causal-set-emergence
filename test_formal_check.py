"""Regression tests for the Lean checker orchestration, not the Lean proofs.

The fake Lake records invocations and simulates failures. Actual proof and
axiom validation still requires running formal/check.sh with the pinned Lean.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class FormalCheckTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        shutil.copyfile(Path(__file__).parent / "formal" / "check.sh", self.root / "check.sh")
        self.log = self.root / "lake-log.jsonl"
        self.audit_log = self.root / "source-audits.jsonl"
        binary = self.root / "bin" / "lake"
        binary.parent.mkdir()
        binary.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, sys\n"
            "from pathlib import Path\n"
            "with open(os.environ['LAKE_LOG'], 'a') as log:\n"
            "    log.write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "source = None\n"
            "if Path(sys.argv[-1]).name == 'SourceAudit.lean':\n"
            "    content = Path(sys.argv[-1]).read_text()\n"
            "    marker = '-- fixture-source: '\n"
            "    source = next((line.removeprefix(marker) for line in content.splitlines()\n"
            "                   if line.startswith(marker)), None)\n"
            "    with open(os.environ['SOURCE_AUDIT_LOG'], 'a') as log:\n"
            "        log.write(json.dumps({'source': source, 'content': content}) + '\\n')\n"
            "target = os.environ.get('LAKE_FAIL_ON')\n"
            "failed = target and (source == target or\n"
            "    any(arg == target or Path(arg).name == target for arg in sys.argv[1:]))\n"
            "sys.exit(1 if failed else 0)\n"
        )
        binary.chmod(0o755)
        self.env = {
            **os.environ,
            "PATH": f"{binary.parent}:{os.environ['PATH']}",
            "LAKE_LOG": str(self.log),
            "SOURCE_AUDIT_LOG": str(self.audit_log),
            "LAKE_FAIL_ON": "",
        }
        for name in ("BoundaryDraft.lean", "BoundaryDraft/Existing.lean", "Audit.lean"):
            self.source(name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "check.sh", "*.lean",
                        "BoundaryDraft/Existing.lean"], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Test",
                        "-c", "user.email=test@example.org", "commit", "-qm", "baseline"],
                       check=True)

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True,
                              capture_output=True, text=True)

    def source(self, name):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"-- fixture-source: ./{name}\n")

    def run_check(self, fail_on="", *args):
        return subprocess.run(
            ["bash", str(self.root / "check.sh"), *args],
            cwd=self.root.parent,  # The script must resolve its own directory.
            env={**self.env, "LAKE_FAIL_ON": fail_on},
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def audits(self):
        return [json.loads(line) for line in self.audit_log.read_text().splitlines()]

    def test_discovers_all_local_sources_and_audits_last(self):
        for name in ("NewModule.lean", "nested/Unimported.lean", "nested/With Space.lean",
                     "nested/Audit.lean", ".lake/packages/Dependency.lean", ".tools/Tool.lean"):
            self.source(name)
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = self.calls()
        self.assertEqual(calls[0], ["build"])
        self.assertEqual(calls[-1], ["env", "lean", "-DwarningAsError=true", "Audit.lean"])
        for call in calls[1:]:
            self.assertEqual(call[:3], ["env", "lean", "-DwarningAsError=true"])
        expected_sources = {
            "./BoundaryDraft.lean", "./BoundaryDraft/Existing.lean", "./NewModule.lean",
            "./nested/Unimported.lean", "./nested/With Space.lean", "./nested/Audit.lean",
        }
        # Each isolated audit compiles the source itself with warnings as
        # errors. A second, direct per-source invocation would be redundant.
        self.assertEqual(len(calls), len(expected_sources) + 2)
        self.assertTrue(all(Path(call[-1]).name == "SourceAudit.lean" for call in calls[1:-1]))
        audits = self.audits()
        self.assertEqual(len(audits), len(expected_sources))
        self.assertEqual({audit["source"] for audit in audits}, expected_sources)
        for audit in audits:
            self.assertIn("import Lean.Util.CollectAxioms", audit["content"])
            self.assertIn("Lean.collectAxioms declaration", audit["content"])
            self.assertIn("unless allowed.contains dependency", audit["content"])

    def test_build_failure_stops_validation(self):
        self.assertNotEqual(self.run_check("build").returncode, 0)
        self.assertEqual(self.calls(), [["build"]])

    def test_discovery_failure_stops_validation(self):
        find = self.root / "bin" / "find"
        find.write_text("#!/usr/bin/env bash\nexit 1\n")
        find.chmod(0o755)
        self.assertNotEqual(self.run_check().returncode, 0)
        self.assertFalse(self.log.exists())

    def test_new_source_failure_is_not_ignored(self):
        self.source("Unimported.lean")
        self.assertNotEqual(self.run_check("./Unimported.lean").returncode, 0)
        self.assertEqual(Path(self.calls()[-1][-1]).name, "SourceAudit.lean")
        self.assertEqual(self.audits()[-1]["source"], "./Unimported.lean")

    def test_source_axiom_audit_failure_is_not_ignored(self):
        self.assertNotEqual(self.run_check("SourceAudit.lean").returncode, 0)
        self.assertEqual(Path(self.calls()[-1][-1]).name, "SourceAudit.lean")

    def test_axiom_audit_failure_is_not_ignored(self):
        self.assertNotEqual(self.run_check("Audit.lean").returncode, 0)
        self.assertEqual(self.calls()[-1][-1], "Audit.lean")

    def test_incremental_staged_unstaged_untracked_spaces_and_unimported(self):
        (self.root / "BoundaryDraft/Existing.lean").write_text(
            "-- fixture-source: ./BoundaryDraft/Existing.lean\n-- modified\n")
        self.source("New Unimported.lean")
        self.source("staged/Changed.lean")
        self.git("add", "staged/Changed.lean")
        result = self.run_check("", "--incremental", "--base", "HEAD")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual({a["source"] for a in self.audits()},
                         {"./BoundaryDraft/Existing.lean", "./New Unimported.lean", "./staged/Changed.lean"})
        self.assertFalse(any(call[-1] == "Audit.lean" for call in self.calls()))
        self.assertIn("developer check only", result.stdout)

    def test_incremental_modified_rename_deleted_and_audit(self):
        self.git("mv", "BoundaryDraft/Existing.lean", "BoundaryDraft/Renamed.lean")
        self.git("rm", "BoundaryDraft.lean")
        (self.root / "Audit.lean").write_text("-- changed aggregate\n")
        result = self.run_check("", "--incremental", "--base", "HEAD")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([a["source"] for a in self.audits()],
                         ["./BoundaryDraft/Existing.lean"])
        self.assertEqual(self.calls()[-1][-1], "Audit.lean")

    def test_incremental_failing_unimported_and_unreliable_base(self):
        self.source("Unimported.lean")
        self.assertNotEqual(self.run_check("./Unimported.lean", "--incremental",
                                       "--base", "HEAD").returncode, 0)
        self.assertFalse(any(call[-1] == "Audit.lean" for call in self.calls()))
        self.log.unlink()
        self.assertNotEqual(self.run_check("", "--incremental", "--base",
                                       "missing-ref").returncode, 0)
        self.assertFalse(self.log.exists())

    def test_parallel_failure_isolation_and_no_aggregate(self):
        self.source("Unimported.lean")
        result = self.run_check("./Unimported.lean", "--workers", "3")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Source audit failed: ./Unimported.lean", result.stderr)
        self.assertEqual(len(self.audits()), 3)
        self.assertEqual(len({a["content"] for a in self.audits()}), 3)
        self.assertFalse(any(call[-1] == "Audit.lean" for call in self.calls()))

    def test_invalid_worker_count_and_ignored_source_fail_closed(self):
        self.assertNotEqual(self.run_check("", "--workers", "0").returncode, 0)
        (self.root / ".gitignore").write_text("ignored.lean\n")
        self.source("ignored.lean")
        result = self.run_check("", "--incremental", "--base", "HEAD")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Ignored local Lean source", result.stderr)


if __name__ == "__main__":
    unittest.main()
