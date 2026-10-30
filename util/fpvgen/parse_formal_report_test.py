# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for expected failures in the standalone formal report parsers."""

import importlib.util
import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import hjson

TOOLS = Path(__file__).absolute().parents[2] / "hw" / "formal" / "tools"
LOGS = {
    "jaspergold":
    """\
[1] tb.Good_A proven
[2] tb.Falsified_A cex
[3] tb.Vacuous_A cex
[4] tb.RealBug_A unreachable
[5] tb.AnotherRealBug_A unreachable
[6] tb.Check_A:precondition1 unreachable
[7] tb.Pending_A undetermined
[8] tb.PendingCover_A undetermined
""",
    "vcformal":
    """\
1,assert,proven,tb.Good_A
2,assert,falsified,tb.Falsified_A
3,assert,vacuous,tb.Vacuous_A
4,cover,uncoverable,tb.RealBug_A
5,cover,uncoverable,tb.AnotherRealBug_A
6,cover,covered,tb.Cover_A
7,assert,inconclusive,tb.Pending_A
8,cover,inconclusive,tb.PendingCover_A
""",
}


class TestExpectedFailures(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.parsers = {}
        for tool in LOGS:
            path = TOOLS / tool / "parse-formal-report.py"
            spec = importlib.util.spec_from_file_location(tool, path)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            cls.parsers[tool] = module

    def setUp(self):
        tempdir = tempfile.TemporaryDirectory()
        self.addCleanup(tempdir.cleanup)
        self.tempdir = Path(tempdir.name)
        self.waivers = self.tempdir / "waivers.hjson"

    def read_waivers(self, tool, value):
        self.read_waivers_file(value)
        return self.parsers[tool].get_expected_failures(
            str(self.waivers), tool)

    def run_parser(self, tool, exp_fail_path=None):
        logfile = self.tempdir / "fpv.log"
        report = self.tempdir / "results.hjson"
        logfile.write_text(LOGS[tool], encoding="utf-8")
        waivers = self.waivers if exp_fail_path is None else exp_fail_path
        command = [
            sys.executable,
            str(TOOLS / tool / "parse-formal-report.py"),
            f"--logpath={logfile}",
            f"--reppath={report}",
            f"--exp-fail-path={waivers}",
        ]
        result = subprocess.run(command,
                                capture_output=True,
                                text=True,
                                check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result, hjson.loads(report.read_text(encoding="utf-8"))

    def test_flat_waivers_remain_supported(self):
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                waivers = self.read_waivers(tool, {"cex": ["tb.Falsified_A"]})
                summary = parser.get_summary(LOGS[tool], waivers)
                self.assertEqual(summary["cex"], 1)

    def test_matching_engine_section(self):
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                waivers = self.read_waivers(tool,
                                            {tool: {
                                                "cex": ["tb.Vacuous_A"]
                                            }})
                self.assertEqual(
                    parser.get_summary(LOGS[tool], waivers)["cex"], 1)

    def test_other_engine_section_does_not_apply(self):
        value = {"jaspergold": {"unreachable": ["tb.Check_A:precondition1"]}}
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                waivers = self.read_waivers(tool, value)
                self.assertEqual(
                    parser.get_summary(LOGS[tool], waivers)["unreachable"], 2)

    def test_multiple_patterns_share_one_waiver_pass(self):
        parser = self.parsers["vcformal"]
        waivers = self.read_waivers("vcformal", {
            "cex": ["tb.Vacuous_A"],
            "undetermined": ["tb.PendingCover_A"],
        })
        summary = parser.get_summary(LOGS["vcformal"], waivers)
        self.assertEqual(summary["cex"], 1)
        self.assertEqual(summary["undetermined"], 1)

    def test_stale_waiver_is_reported_and_counted(self):
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                waivers = self.read_waivers(tool, {"cex": ["tb.Gone_A"]})
                with self.assertLogs(level="ERROR") as logs:
                    summary = parser.get_summary(LOGS[tool], waivers)
                self.assertEqual(summary["cex"], 3)
                self.assertIn("is not in the report", "\n".join(logs.output))

    def test_stale_waivers_cannot_match_each_others_placeholders(self):
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                waivers = self.read_waivers(tool,
                                            {"cex": ["tb.Gone_A", "Gone_A"]})
                with self.assertLogs(level="ERROR") as logs:
                    summary = parser.get_summary(LOGS[tool], waivers)
                self.assertEqual(summary["cex"], 4)
                self.assertEqual(len(logs.output), 2)

    def test_ambiguous_waiver_does_not_hide_multiple_properties(self):
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                waivers = self.read_waivers(tool, {"unreachable": ["Bug_A"]})
                with self.assertLogs(level="ERROR") as logs:
                    summary = parser.get_summary(LOGS[tool], waivers)
                self.assertEqual(summary["unreachable"],
                                 3 if tool == "jaspergold" else 2)
                self.assertIn("ambiguous", "\n".join(logs.output))

    def test_invalid_root_is_reported(self):
        for tool in self.parsers:
            for value in [["bad"], "bad", 42, True, [], None, False]:
                with self.subTest(tool=tool, value=value):
                    with self.assertLogs(level="ERROR"):
                        self.assertEqual(self.read_waivers(tool, value), {})

    def test_invalid_categories_and_names_are_reported(self):
        values = [
            {
                "cexx": ["tb.Falsified_A"]
            },
            {
                "cex": "tb.Falsified_A"
            },
            {
                "cex": [42]
            },
            {
                "cex": [""]
            },
            {
                "cex": ["   "]
            },
            {
                "jasper_gold": {
                    "cex": ["tb.Falsified_A"]
                }
            },
            {
                "jaspergold": {},
                "cex": []
            },
        ]
        for tool in self.parsers:
            for value in values:
                with self.subTest(tool=tool, value=value):
                    with self.assertLogs(level="ERROR"):
                        self.assertEqual(self.read_waivers(tool, value), {})

    def test_empty_mapping_and_missing_option_are_supported(self):
        for tool, parser in self.parsers.items():
            with self.subTest(tool=tool):
                self.assertEqual(self.read_waivers(tool, {}), {})
                self.assertEqual(parser.get_expected_failures(None, tool), {})
                self.assertEqual(parser.get_expected_failures("", tool), {})

    def test_unreadable_or_malformed_waiver_file_preserves_results(self):
        for tool, parser in self.parsers.items():
            for contents in [None, "{ bad: ["]:
                with self.subTest(tool=tool, contents=contents):
                    if self.waivers.exists():
                        self.waivers.unlink()
                    if contents is not None:
                        self.waivers.write_text(contents, encoding="utf-8")
                    logfile = self.tempdir / "fpv.log"
                    logfile.write_text(LOGS[tool], encoding="utf-8")
                    with self.assertLogs(level="ERROR"):
                        results = parser.get_results(str(logfile),
                                                     str(self.waivers))
                    self.assertEqual(results["exp_failures"], {})
                    self.assertEqual(results["summary"]["cex"], 2)

    def test_cli_accepts_shared_option_and_writes_waived_summary(self):
        for tool in self.parsers:
            with self.subTest(tool=tool):
                self.read_waivers(tool, {tool: {"cex": ["tb.Falsified_A"]}})
                result, report = self.run_parser(tool)
                self.assertEqual(result.stderr, "")
                self.assertEqual(report["summary"]["cex"], 1)
                # Preserve the raw diagnostics alongside the adjusted counts.
                self.assertEqual(len(report["messages"]["cex"]), 2)

    def test_cli_accepts_empty_path(self):
        for tool in self.parsers:
            with self.subTest(tool=tool):
                result, report = self.run_parser(tool, exp_fail_path="")
                self.assertEqual(result.stderr, "")
                self.assertEqual(report["summary"]["cex"], 2)

    def test_cli_error_matches_dvsim_failure_patterns(self):
        config = hjson.loads(
            (TOOLS / "dvsim" / "common_formal_cfg.hjson").read_text())
        patterns = config["build_fail_patterns"]
        for tool in self.parsers:
            for value in [["bad"], {"cex": [""]}, {"cex": ["tb.Gone_A"]}]:
                with self.subTest(tool=tool, value=value):
                    self.read_waivers_file(value)
                    result, report = self.run_parser(tool)
                    self.assertNotIn("Traceback", result.stderr)
                    self.assertTrue(
                        any(
                            re.search(pattern, result.stderr, re.MULTILINE)
                            for pattern in patterns), result.stderr)
                    self.assertGreaterEqual(report["summary"]["cex"], 2)

    def read_waivers_file(self, value):
        self.waivers.write_text(json.dumps(value), encoding="utf-8")


if __name__ == "__main__":
    unittest.main()
