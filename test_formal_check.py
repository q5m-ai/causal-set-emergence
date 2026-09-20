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
        binary = self.root / "bin" / "lake"
        binary.parent.mkdir()
        binary.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, sys\n"
            "from pathlib import Path\n"
            "with open(os.environ['LAKE_LOG'], 'a') as log:\n"
            "    log.write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "target = os.environ.get('LAKE_FAIL_ON')\n"
            "failed = target and any(arg == target or Path(arg).name == target for arg in sys.argv[1:])\n"
            "sys.exit(1 if failed else 0)\n"
        )
        binary.chmod(0o755)
        self.env = {
            **os.environ,
            "PATH": f"{binary.parent}:{os.environ['PATH']}",
            "LAKE_LOG": str(self.log),
            "LAKE_FAIL_ON": "",
        }
        for name in ("BoundaryDraft.lean", "BoundaryDraft/Existing.lean", "Audit.lean"):
            self.source(name)

    def source(self, name):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()

    def run_check(self, fail_on=""):
        return subprocess.run(
            ["bash", str(self.root / "check.sh")],
            cwd=self.root.parent,  # The script must resolve its own directory.
            env={**self.env, "LAKE_FAIL_ON": fail_on},
            capture_output=True,
            text=True,
            timeout=10,
            check=False,
        )

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

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
        direct_sources = {call[-1] for call in calls[1:] if call[-1].startswith("./")}
        self.assertEqual(direct_sources, {
            "./BoundaryDraft.lean", "./BoundaryDraft/Existing.lean", "./NewModule.lean",
            "./nested/Unimported.lean", "./nested/With Space.lean", "./nested/Audit.lean",
        })
        source_audits = [call for call in calls if Path(call[-1]).name == "SourceAudit.lean"]
        self.assertEqual(len(source_audits), len(direct_sources))

    def test_build_failure_stops_validation(self):
        self.assertNotEqual(self.run_check("build").returncode, 0)
        self.assertEqual(self.calls(), [["build"]])

    def test_discovery_failure_stops_validation(self):
        find = self.root / "bin" / "find"
        find.write_text("#!/usr/bin/env bash\nexit 1\n")
        find.chmod(0o755)
        self.assertNotEqual(self.run_check().returncode, 0)
        self.assertEqual(self.calls(), [["build"]])

    def test_new_source_failure_is_not_ignored(self):
        self.source("Unimported.lean")
        self.assertNotEqual(self.run_check("./Unimported.lean").returncode, 0)
        self.assertEqual(self.calls()[-1][-1], "./Unimported.lean")

    def test_source_axiom_audit_failure_is_not_ignored(self):
        self.assertNotEqual(self.run_check("SourceAudit.lean").returncode, 0)
        self.assertEqual(Path(self.calls()[-1][-1]).name, "SourceAudit.lean")

    def test_axiom_audit_failure_is_not_ignored(self):
        self.assertNotEqual(self.run_check("Audit.lean").returncode, 0)
        self.assertEqual(self.calls()[-1][-1], "Audit.lean")


if __name__ == "__main__":
    unittest.main()
