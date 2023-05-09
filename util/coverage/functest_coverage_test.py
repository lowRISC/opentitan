#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from unittest.mock import (
    MagicMock,
    patch,
)
from pathlib import Path
from io import BytesIO

import functest_coverage


class AnyStringWith(str):

    def __eq__(self, other):
        return self in other


class TestFunc(unittest.TestCase):

    def test_handle_libs(self):
        device_libs_all = [
            "//foo/a", "//foo/b_on_host_do_not", "//foo/c_on_host", "//foo/d"
        ]
        device_libs = ["//foo/a", "//foo/d"]

        self.assertEqual(functest_coverage.handle_libs(device_libs_all),
                         device_libs)

    @patch("functest_coverage.LLD_TARGET", "<lld_target>")
    @patch("functest_coverage.run")
    def test_handle_objs(self, mock_run):
        merged_library = Path("/foo/merged.so")
        obj_files = ["//foo/a.o", "//foo/d.o"]

        functest_coverage.handle_objs(merged_library, obj_files)

        mock_run.assert_called_once_with(
            "<lld_target>", AnyStringWith("unresolved"), "-e", "0x0",
            "--defsym", '__llvm_profile_register_names_function=0', '--defsym',
            '__llvm_profile_register_function=0', '--defsym',
            '__llvm_profile_runtime=0', '-o', str(merged_library), *obj_files)

    @patch("functest_coverage.run")
    def test_handle_test_targets(self, mock_run):
        test_targets = [
            "//foo/test", "//bar/test_cw310_test_rom",
            "//qux/long_wycheproof_test"
        ]
        mock_run.side_effect = (
            None,
            ["workspace_path"],
            ["bitstream_file.bit"],
            None,
        )

        res = functest_coverage.handle_test_targets(test_targets)

        self.assertEqual(res, ["//bar/test_cw310_test_rom"])
        calls_mock_run = mock_run.call_args_list
        self.assertEqual(len(calls_mock_run), 4)
        self.assertEqual(calls_mock_run[0][0],
                         (functest_coverage.BAZEL, "build",
                          functest_coverage.BITSTREAM_TARGET))
        self.assertEqual(calls_mock_run[1][0],
                         (functest_coverage.BAZEL, "info", "workspace"))
        self.assertEqual(
            calls_mock_run[2][0],
            (functest_coverage.BAZEL, "cquery", "--output=starlark",
             "--starlark:expr", "target.files.to_list()[0].path",
             functest_coverage.BITSTREAM_TARGET))
        self.assertEqual(
            calls_mock_run[3][0],
            (functest_coverage.BAZEL, "run", "//sw/host/opentitantool", "--",
             "fpga", "load-bitstream", "workspace_path/bitstream_file.bit"))

    def mock_binary_file(self: unittest.TestCase,
                         name: str,
                         contents: bytes = None) -> MagicMock:
        mock_file = MagicMock(autospec=BytesIO)
        mock_file.__enter__.side_effect = [mock_file]
        mock_file.name = name
        if contents:
            mock_file.read.side_effect = [contents]
        return mock_file

    @patch("pathlib.Path.open", autospec=True)
    @patch("functest_coverage.extract_profile_data")
    @patch("pathlib.Path.__truediv__",
           side_effect=Path.__truediv__,
           autospec=True)
    def test_handle_test_log_dirs(self, mock_path_div,
                                  mock_extract_profile_data, mock_path_open):
        test_log_dirs = [Path("/testlogs/foo"), Path("/testlogs/bar")]
        test_logs = [
            Path("/testlogs/foo/test.log"),
            Path("/testlogs/bar/test.log")
        ]
        profiles = [
            Path("/testlogs/foo/prof.raw"),
            Path("/testlogs/bar/prof.raw")
        ]

        mock_files = [
            self.mock_binary_file(name=test_logs[0], contents=b"<log_0>"),
            self.mock_binary_file(name=profiles[0]),
            self.mock_binary_file(name=test_logs[1], contents=b"<log_1>"),
            self.mock_binary_file(name=profiles[1]),
        ]
        mock_path_open.side_effect = mock_files
        mock_extract_profile_data.side_effect = (b"<raw_profile_0>",
                                                 b"<raw_profile_1>")

        self.assertEqual(functest_coverage.handle_test_log_dirs(test_log_dirs),
                         profiles)

        calls_path_div = mock_path_div.call_args_list
        self.assertEqual(len(calls_path_div), 4)
        self.assertEqual(calls_path_div[0][0], (test_log_dirs[0], "test.log"))
        self.assertEqual(calls_path_div[1][0], (test_log_dirs[0], "prof.raw"))
        self.assertEqual(calls_path_div[2][0], (test_log_dirs[1], "test.log"))
        self.assertEqual(calls_path_div[3][0], (test_log_dirs[1], "prof.raw"))

        calls_path_open = mock_path_open.call_args_list
        self.assertEqual(len(calls_path_open), 4)
        self.assertEqual(calls_path_open[0][0], (test_logs[0], "rb"))
        self.assertEqual(calls_path_open[1][0], (profiles[0], "wb"))
        self.assertEqual(calls_path_open[2][0], (test_logs[1], "rb"))
        self.assertEqual(calls_path_open[3][0], (profiles[1], "wb"))

        calls_extract_profile_data = mock_extract_profile_data.call_args_list
        self.assertEqual(len(calls_extract_profile_data), 2)
        self.assertEqual(calls_extract_profile_data[0][0], ("<log_0>", ))
        self.assertEqual(calls_extract_profile_data[1][0], ("<log_1>", ))

        mock_files[1].write.assert_called_once_with(b"<raw_profile_0>")
        mock_files[3].write.assert_called_once_with(b"<raw_profile_1>")

    def test_params(self):
        self.assertEqual(functest_coverage.PARAMS.bazel_test_type,
                         AnyStringWith("sh_test"))
        self.assertEqual(functest_coverage.PARAMS.config,
                         "ot_coverage_on_target")
        self.assertEqual(functest_coverage.PARAMS.libs_fn,
                         functest_coverage.handle_libs)
        self.assertEqual(functest_coverage.PARAMS.objs_fn,
                         functest_coverage.handle_objs)
        self.assertEqual(functest_coverage.PARAMS.test_targets_fn,
                         functest_coverage.handle_test_targets)
        self.assertEqual(functest_coverage.PARAMS.test_log_dirs_fn,
                         functest_coverage.handle_test_log_dirs)
        self.assertEqual(functest_coverage.PARAMS.report_title,
                         AnyStringWith("Functional Test"))


if __name__ == "__main__":
    unittest.main()
