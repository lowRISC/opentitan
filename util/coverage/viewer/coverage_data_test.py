# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Tests for coverage_data.py."""

import unittest
import tempfile
import shutil
from pathlib import Path

from util.coverage.viewer.lcov import FileProfile
from util.coverage.viewer.coverage_data import simplify_path, CoverageCollection


class TestCoverageData(unittest.TestCase):

    def setUp(self) -> None:
        self.test_dir = Path(tempfile.mkdtemp())

    def tearDown(self) -> None:
        shutil.rmtree(self.test_dir)

    def test_simplify_path(self) -> None:
        self.assertEqual(
            simplify_path("bazel-out/k8-fastbuild/bin/path/to/file.c"),
            "generated/bin/path/to/file.c")
        self.assertEqual(
            simplify_path(
                "bazel-out/k8-opt/bin/hw/top_earlgrey/ip/uart/rtl/uart.v"),
            "generated/bin/hw/top_earlgrey/ip/uart/rtl/uart.v")
        self.assertEqual(simplify_path("src/main.c"), "src/main.c")

    def test_coverage_collection_multi_test_aggregation(self) -> None:
        source_file = self.test_dir / "file1.c"
        source_file.write_text("line1\nline2\nline3\n")

        coll = CoverageCollection()

        # Test 1 hits line 1
        coll.add_test("test1", {
            str(source_file):
            FileProfile(sf=str(source_file), da={
                1: 1,
                2: 0
            })
        })

        # Test 2 hits line 2
        coll.add_test("test2", {
            str(source_file):
            FileProfile(sf=str(source_file), da={
                1: 0,
                2: 1
            })
        })

        path = simplify_path(str(source_file))
        data = coll.as_dict()

        self.assertEqual(data["tests"], ["test1", "test2"])
        lines = data["files"][path]["l"]
        self.assertEqual(lines[0]["t"], [0])  # Line 1 hit by test 0
        self.assertEqual(lines[1]["t"], [1])  # Line 2 hit by test 1
        self.assertEqual(lines[2]["t"], [])  # Line 3 not hit

    def test_coverage_collection_add_uncovered(self) -> None:
        source_file = self.test_dir / "file1.c"
        source_file.write_text("line1\nline2\n")

        coll = CoverageCollection()

        # With add_uncovered=True, even 0 counts get the test index
        test_profiles = {
            str(source_file): FileProfile(sf=str(source_file), da={
                1: 0,
                2: 0
            })
        }
        coll.add_test("test_view", test_profiles, add_uncovered=True)

        path = simplify_path(str(source_file))
        data = coll.as_dict()
        lines = data["files"][path]["l"]
        self.assertEqual(lines[0]["t"], [0])
        self.assertEqual(lines[1]["t"], [0])

    def test_missing_source_file_graceful_skip(self) -> None:
        coll = CoverageCollection()
        # file_not_exists.c does not exist on disk
        coll.add_test("test1", {
            "file_not_exists.c":
            FileProfile(sf="file_not_exists.c", da={1: 1})
        })
        self.assertEqual(len(coll.files), 0)

    def test_source_dir_resolution(self) -> None:
        source_dir = self.test_dir / "src_root"
        source_file = source_dir / "dir" / "file.c"
        source_file.parent.mkdir(parents=True)
        source_file.write_text("content\n")

        coll = CoverageCollection(source_dir=source_dir)
        # Profile uses relative path from source_dir
        rel_sf_path = "dir/file.c"
        coll.add_test("test1",
                      {rel_sf_path: FileProfile(sf=rel_sf_path, da={1: 1})})

        path = simplify_path(rel_sf_path)
        self.assertIn(path, coll.files)
        self.assertEqual(coll.files[path]["l"][0]["c"], "content")


if __name__ == "__main__":
    unittest.main()
