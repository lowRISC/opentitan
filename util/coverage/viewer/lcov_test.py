# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tests for lcov.py."""

import unittest
import tempfile
import shutil
from pathlib import Path
from typing import Optional

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
        self.assertEqual(result["file1.c"].fn["func1"], {10})
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

    def _create_lcov(self,
                     rel_path: str,
                     base_dir: Optional[Path] = None) -> Path:
        base = base_dir or self.test_dir
        path = base / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("SF:file1.c\nDA:1,1\nend_of_record\n")
        return path

    def test_iter_lcov_files_label_calculation(self) -> None:
        # Setup: .../testlogs/path/to/test/coverage.dat
        lcov_file = self._create_lcov(
            "testlogs/hw/ip/uart/uart_test/coverage.dat")

        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{lcov_file}\n")

        results = list(iter_lcov_files(list_file))
        self.assertEqual(len(results), 1)
        # Expected label: //hw/ip/uart:uart_test
        self.assertEqual(results[0].name, "//hw/ip/uart:uart_test")
        self.assertIn("file1.c", results[0].files)

    def test_iter_lcov_files_skip_non_coverage_dat(self) -> None:
        other_file = self._create_lcov("testlogs/other.dat")

        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{other_file}\n")

        results = list(iter_lcov_files(list_file))
        self.assertEqual(len(results), 0)

    def test_iter_lcov_files_coverage_dir_resolution(self) -> None:
        # Setup: coverage_dir/relative/path/coverage.dat
        coverage_dir = self.test_dir / "base"
        lcov_file = self._create_lcov("testlogs/pkg/test1/coverage.dat",
                                      base_dir=coverage_dir)

        # List file contains relative path from coverage_dir
        rel_path = lcov_file.relative_to(coverage_dir)
        list_file = self.test_dir / "list.txt"
        list_file.write_text(f"{rel_path}\n")

        results = list(iter_lcov_files(list_file, coverage_dir=coverage_dir))
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0].name, "//pkg:test1")

    def test_iter_lcov_files_sorted_order(self) -> None:
        # Create three coverage files in unsorted order in the list file
        files = ["z_test", "a_test", "m_test"]
        lcov_paths = []
        for name in files:
            lcov_file = self._create_lcov(f"testlogs/{name}/coverage.dat")
            lcov_paths.append(lcov_file)

        # Write them to the list file in a specific non-sorted order
        list_file = self.test_dir / "list.txt"
        list_file.write_text("\n".join(map(str, lcov_paths)) + "\n")

        results = list(iter_lcov_files(list_file))
        self.assertEqual(len(results), 3)
        # Expected order should be sorted: a, m, z
        self.assertEqual(results[0].name, "//:a_test")
        self.assertEqual(results[1].name, "//:m_test")
        self.assertEqual(results[2].name, "//:z_test")


if __name__ == "__main__":
    unittest.main()
