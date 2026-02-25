# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tests for lcov.py."""

import unittest
import tempfile
import shutil
from pathlib import Path

from util.coverage.viewer.lcov import parse_lcov, iter_lcov_files


class TestLcovParser(unittest.TestCase):

    def test_basic_parsing(self) -> None:
        lcov_lines = ["SF:file1.c", "DA:1,1", "DA:2,0", "end_of_record"]
        result = parse_lcov(lcov_lines)
        self.assertIn("file1.c", result)
        self.assertEqual(result["file1.c"].da[1], 1)
        self.assertEqual(result["file1.c"].da[2], 0)

    def test_merging_sf_blocks(self) -> None:
        lcov_lines = [
            "SF:file1.c", "DA:1,1", "end_of_record", "SF:file1.c", "DA:2,1",
            "end_of_record"
        ]
        result = parse_lcov(lcov_lines)
        self.assertIn("file1.c", result)
        self.assertEqual(result["file1.c"].da[1], 1)
        self.assertEqual(result["file1.c"].da[2], 1)

    def test_aggregating_da_counts(self) -> None:
        lcov_lines = ["SF:file1.c", "DA:1,1", "DA:1,2", "end_of_record"]
        result = parse_lcov(lcov_lines)
        self.assertEqual(result["file1.c"].da[1], 3)

    def test_fn_fnda_parsing(self) -> None:
        lcov_lines = [
            "SF:file1.c", "FN:10,func1", "FNDA:5,func1", "end_of_record"
        ]
        result = parse_lcov(lcov_lines)
        self.assertEqual(result["file1.c"].fn["func1"], 10)
        self.assertEqual(result["file1.c"].fnda["func1"], 5)

    def test_malformed_lines(self) -> None:
        lcov_lines = [
            "SF:file1.c", "INVALID_TAG:some_data", "DA:1,1",
            "DA:not_a_number,5", "end_of_record"
        ]
        # Should not crash, and should skip malformed DA
        result = parse_lcov(lcov_lines)
        self.assertIn("file1.c", result)
        self.assertEqual(result["file1.c"].da[1], 1)
        self.assertEqual(len(result["file1.c"].da), 1)


class TestLcovIterator(unittest.TestCase):

    def setUp(self) -> None:
        self.test_dir = Path(tempfile.mkdtemp())

    def tearDown(self) -> None:
        shutil.rmtree(self.test_dir)

    def test_iter_lcov_files_label_calculation(self) -> None:
        # Setup: .../testlogs/path/to/test/coverage.dat
        test_log_dir = self.test_dir / "testlogs" / "hw" / "ip" / "uart" / "uart_test"
        test_log_dir.mkdir(parents=True)
        lcov_file = test_log_dir / "coverage.dat"
        lcov_file.write_text("SF:file1.c\nend_of_record\n")

        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{lcov_file}\n")

        results = list(iter_lcov_files(list_file))
        self.assertEqual(len(results), 1)
        # Expected label: //hw/ip/uart:uart_test
        self.assertEqual(results[0].name, "//hw/ip/uart:uart_test")
        self.assertIn("file1.c", results[0].files)

    def test_iter_lcov_files_skip_non_coverage_dat(self) -> None:
        other_file = self.test_dir / "testlogs" / "other.dat"
        other_file.parent.mkdir(parents=True, exist_ok=True)
        other_file.write_text("SF:file2.c\nend_of_record\n")

        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{other_file}\n")

        results = list(iter_lcov_files(list_file))
        self.assertEqual(len(results), 0)

    def test_iter_lcov_files_coverage_dir_resolution(self) -> None:
        # Setup: coverage_dir/relative/path/coverage.dat
        coverage_dir = self.test_dir / "base"
        test_log_dir = coverage_dir / "testlogs" / "pkg" / "test1"
        test_log_dir.mkdir(parents=True)
        lcov_file = test_log_dir / "coverage.dat"
        lcov_file.write_text("SF:file1.c\nend_of_record\n")

        # List file contains relative path from coverage_dir
        rel_path = lcov_file.relative_to(coverage_dir)
        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{rel_path}\n")

        results = list(iter_lcov_files(list_file, coverage_dir=coverage_dir))
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0].name, "//pkg:test1")


if __name__ == "__main__":
    unittest.main()
