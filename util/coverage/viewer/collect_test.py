# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tests for collect.py."""

import unittest
import json
import gzip
import tempfile
import shutil
from pathlib import Path

from util.coverage.viewer.coverage_data import simplify_path
from util.coverage.viewer.collect import main


class TestCollectCoverageJson(unittest.TestCase):

    def setUp(self) -> None:
        self.test_dir = Path(tempfile.mkdtemp())

    def tearDown(self) -> None:
        shutil.rmtree(self.test_dir)

    def test_main_end_to_end(self) -> None:
        source_file = self.test_dir / "src.c"
        source_file.write_text("line1\nline2\nline3\n")

        # Test LCOV - must be named coverage.dat and be in a testlogs-like path
        test_dir = self.test_dir / "testlogs" / "pkg" / "mytest"
        test_dir.mkdir(parents=True)
        lcov_file = test_dir / "coverage.dat"
        lcov_file.write_text(
            f"SF:{source_file}\nDA:1,1\nDA:2,0\nend_of_record\n")

        # View LCOV (suffix _coverage_view) - also must be named coverage.dat
        view_test_dir = self.test_dir / "testlogs" / "pkg" / "mytest_coverage_view"
        view_test_dir.mkdir(parents=True)
        view_lcov_file = view_test_dir / "coverage.dat"
        view_lcov_file.write_text(
            f"SF:{source_file}\nDA:1,0\nDA:2,0\nDA:3,0\nend_of_record\n")

        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{lcov_file}\n{view_lcov_file}\n")

        output_file = self.test_dir / "out.json.gz"

        main(["--lcov_files", str(list_file), "--output", str(output_file)])

        self.assertTrue(output_file.exists())
        with gzip.open(output_file, 'rt') as f:
            data = json.load(f)
            # Check metadata
            self.assertIn("metadata", data)
            self.assertIn("timestamp", data["metadata"])

            # Check labels
            self.assertEqual(data["test"]["tests"], ["//pkg:mytest"])
            self.assertEqual(data["view"]["tests"],
                             ["//pkg:mytest_coverage_view"])

            path = simplify_path(str(source_file))

            # Check coverage
            self.assertIn(path, data["test"]["files"])
            self.assertEqual(data["test"]["files"][path]["l"][0]["t"],
                             [0])  # Line 1 hit
            self.assertEqual(data["test"]["files"][path]["l"][1]["t"],
                             [])  # Line 2 missed

            # Check view
            self.assertIn(path, data["view"]["files"])
            self.assertEqual(data["view"]["files"][path]["l"][0]["t"], [0])
            self.assertEqual(data["view"]["files"][path]["l"][1]["t"], [0])
            self.assertEqual(data["view"]["files"][path]["l"][2]["t"], [0])

    def test_main_with_dir_resolution(self) -> None:
        coverage_dir = self.test_dir / "cov_root"
        source_dir = self.test_dir / "src_root"

        source_file = source_dir / "src.c"
        source_file.parent.mkdir(parents=True)
        source_file.write_text("line1\n")

        test_dir = coverage_dir / "testlogs" / "pkg" / "mytest"
        test_dir.mkdir(parents=True)
        lcov_file = test_dir / "coverage.dat"
        # LCOV refers to source file via relative path from source_dir
        rel_src_path = "src.c"
        lcov_file.write_text(f"SF:{rel_src_path}\nDA:1,1\nend_of_record\n")

        list_file = self.test_dir / "list.txt"
        # Relative path from coverage_dir
        rel_lcov_path = lcov_file.relative_to(coverage_dir)
        list_file.write_text(f"{rel_lcov_path}\n")

        output_file = self.test_dir / "out.json.gz"

        main([
            "--lcov_files",
            str(list_file), "--coverage_dir",
            str(coverage_dir), "--source_dir",
            str(source_dir), "--output",
            str(output_file)
        ])

        self.assertTrue(output_file.exists())
        with gzip.open(output_file, 'rt') as f:
            data = json.load(f)
            self.assertEqual(data["test"]["tests"], ["//pkg:mytest"])
            path = simplify_path(rel_src_path)
            self.assertIn(path, data["test"]["files"])
            self.assertEqual(data["test"]["files"][path]["l"][0]["c"], "line1")


if __name__ == "__main__":
    unittest.main()
