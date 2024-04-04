#!/usr/bin/env python3

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from unittest.mock import patch
from pathlib import Path

import unittest_coverage


class AnyStringWith(str):

    def __eq__(self, other):
        return self in other


class TestUnit(unittest.TestCase):

    @patch("unittest_coverage.BAZEL", "<bazel>")
    @patch("unittest_coverage.DEVICE_LIBS_QUERY", "<device libs query>")
    @patch("unittest_coverage.run")
    def test_handle_libs(self, mock_run):
        device_libs_all = ["//foo/a", "//foo/b", "//foo/c", "//foo/d"]
        device_libs_incompat = ["//foo/b", "//foo/c"]
        device_libs = ["//foo/a", "//foo/d"]
        mock_run.side_effect = (device_libs_incompat, )

        self.assertEqual(unittest_coverage.handle_libs(device_libs_all),
                         device_libs)

        mock_run.assert_called_once_with(
            "<bazel>", "cquery", "<device libs query>", "--output=starlark",
            AnyStringWith("IncompatiblePlatformProvider"))

    @patch("unittest_coverage.LLD_HOST", "<lld_host>")
    @patch("unittest_coverage.run")
    def test_handle_objs(self, mock_run):
        merged_library = Path("/foo/merged.so")
        obj_files = ["//foo/a.o", "//foo/mock_a.o", "//foo/d.o"]

        unittest_coverage.handle_objs(merged_library, obj_files)

        mock_run.assert_called_once_with("<lld_host>", "--shared", "-o",
                                         str(merged_library), "//foo/a.o",
                                         "//foo/d.o")

    def test_handle_test_targets(self):
        test_targets = ["//foo", "//bar"]

        res = unittest_coverage.handle_test_targets(test_targets)
        self.assertTrue(set(res) > set(test_targets))
        self.assertTrue(len([test for test in res if "unittest" in test]) > 0)

    def test_handle_test_log_dirs(self):
        test_log_dirs = [Path("/testlogs/foo"), Path("/testlogs/bar")]
        profiles = [
            Path("/testlogs/foo/coverage.dat"),
            Path("/testlogs/bar/coverage.dat")
        ]
        self.assertEqual(unittest_coverage.handle_test_log_dirs(test_log_dirs),
                         profiles)

    def test_params(self):
        self.assertEqual(unittest_coverage.PARAMS.bazel_test_type,
                         AnyStringWith("cc_test"))
        self.assertEqual(unittest_coverage.PARAMS.config,
                         "ot_coverage_off_target")
        self.assertEqual(unittest_coverage.PARAMS.libs_fn,
                         unittest_coverage.handle_libs)
        self.assertEqual(unittest_coverage.PARAMS.objs_fn,
                         unittest_coverage.handle_objs)
        self.assertEqual(unittest_coverage.PARAMS.test_targets_fn,
                         unittest_coverage.handle_test_targets)
        self.assertEqual(unittest_coverage.PARAMS.test_log_dirs_fn,
                         unittest_coverage.handle_test_log_dirs)
        self.assertEqual(unittest_coverage.PARAMS.report_title,
                         AnyStringWith("Unit Test"))


if __name__ == "__main__":
    unittest.main()
