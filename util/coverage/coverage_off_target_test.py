#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
import subprocess
from pathlib import Path
from unittest.mock import mock_open, patch

import coverage_off_target


class AnyStringWith(str):

    def __eq__(self, other):
        return self in other


class TestExtractProfileData(unittest.TestCase):

    @patch("coverage_off_target.subprocess.run")
    def test_run_single_arg_error(self, mock_run):
        mock_run.side_effect = Exception("foo")
        with self.assertRaisesRegex(Exception, "foo"):
            coverage_off_target.run("ls")
        mock_run.assert_called_once_with(("ls",),
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE,
                                         encoding="utf-8",
                                         check=True)

    @patch("coverage_off_target.subprocess.run")
    def test_run_multi_arg_error(self, mock_run):
        mock_run.side_effect = Exception("foo")
        with self.assertRaisesRegex(Exception, "foo"):
            coverage_off_target.run("ls", "-la", "./")
        mock_run.assert_called_once_with(("ls", "-la", "./"),
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE,
                                         encoding="utf-8",
                                         check=True)

    @patch("coverage_off_target.subprocess.run")
    def test_run_single_arg_success(self, mock_run):
        coverage_off_target.run("ls")
        mock_run.assert_called_once_with(("ls",),
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE,
                                         encoding="utf-8",
                                         check=True)

    @patch("coverage_off_target.subprocess.run")
    def test_run_multi_arg_success(self, mock_run):
        coverage_off_target.run("ls", "-la", "./")
        mock_run.assert_called_once_with(("ls", "-la", "./"),
                                         stdout=subprocess.PIPE,
                                         stderr=subprocess.PIPE,
                                         encoding="utf-8",
                                         check=True)

    @patch("coverage_off_target.run")
    def test_gather_and_build_libs(self, mock_run):
        libs_all = ["//foo/bar1", "//foo/bar2", "//foo/incompat"]
        libs_incompat = ["//foo/incompat"]
        libs = list(set(libs_all) - set(libs_incompat))
        # (1) return all libs, (2) return incompat., (3) build
        mock_run.side_effect = (libs_all, libs_incompat, [])

        self.assertEqual(coverage_off_target.gather_and_build_libs(), libs)

        calls = mock_run.call_args_list
        self.assertEqual(len(calls), 3)
        self.assertEqual(calls[0][0][:2], (coverage_off_target.BAZEL, "query"))
        self.assertEqual(calls[1][0][:2], (coverage_off_target.BAZEL, "cquery"))
        self.assertEqual(calls[2][0], (coverage_off_target.BAZEL, "build",
                                       "--config=coverage_clang", *libs))

    @patch("coverage_off_target.run")
    def test_create_merged_library(self, mock_run):
        libs = ["//foo/bar1", "//foo/bar2"]
        libs_query = "(//foo/bar1 + //foo/bar2)"
        merged_so = Path("merged.so")
        objs = ["foo/bar1.o", "foo/bar2.o"]
        # (1) return object files, (2) link.
        mock_run.side_effect = (objs, [])

        coverage_off_target.create_merged_library(libs, merged_so)

        calls = mock_run.call_args_list
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][0][:3],
                         (coverage_off_target.BAZEL, "cquery", libs_query))
        self.assertEqual(
            calls[1][0],
            (coverage_off_target.LLD, "--shared", "-o", str(merged_so), *objs))

    @patch("coverage_off_target.run")
    def test_measure_unit_test_coverage(self, mock_run):
        tests = ["//foo:test1", "//foo:test2"]
        testlogs = ["/some/long/path"]
        profiles = [
            "/some/long/path/foo/test1/coverage.dat",
            "/some/long/path/foo/test2/coverage.dat"
        ]
        merged_profile = Path("merged.profdata")
        # (1) find test targets, (2) measure coverage, (3) get testlogs dir, (4) merge
        # profile data.
        mock_run.side_effect = (tests, [], testlogs, [])

        coverage_off_target.measure_unit_test_coverage(merged_profile)

        calls = mock_run.call_args_list
        self.assertEqual(len(calls), 4)
        self.assertEqual(calls[0][0][:2], (coverage_off_target.BAZEL, "query"))
        self.assertEqual(calls[1][0], (coverage_off_target.BAZEL, "coverage",
                                       "--config=coverage_clang", *tests))
        self.assertEqual(calls[2][0],
                         (coverage_off_target.BAZEL, "info", "bazel-testlogs"))
        self.assertEqual(
            calls[3][0],
            (coverage_off_target.LLVM_PROFDATA, "merge", "--sparse", "--output",
             str(merged_profile), *profiles))

    @patch("coverage_off_target.print")
    @patch("pathlib.Path.open", new_callable=mock_open)
    @patch("pathlib.Path.__truediv__",
           side_effect=Path.__truediv__,
           autospec=True)
    @patch("coverage_off_target.run")
    def test_generate_report(self, mock_run, mock_path_div, mock_path_open,
                             mock_print):
        for print_text_report in (True, False):
            for m in [mock_run, mock_path_div, mock_path_open, mock_print]:
                m.reset_mock()
            with self.subTest(f"print_text_report:{print_text_report}"):
                out_dir = Path("foo")
                merged_profile = Path("merged.profdata")
                merged_so = Path("merged.so")
                text_report_content = [
                    "<contents of coverage report in text format>"
                ]
                # (1) html report, (2) text report, (3) print text report (if requested)
                mock_run.side_effect = ([], text_report_content,
                                        text_report_content)

                coverage_off_target.generate_report(out_dir, merged_profile,
                                                    merged_so,
                                                    print_text_report)

                calls_run = mock_run.call_args_list
                self.assertEqual(
                    (*calls_run[0][0][:2], *calls_run[0][0][-5:]),
                    (coverage_off_target.LLVM_COV, "show",
                     "--format=html", "--output-dir=./foo", "--instr-profile",
                     str(merged_profile), str(merged_so)))
                self.assertEqual(
                    calls_run[1][0],
                    (coverage_off_target.LLVM_COV, "report", "--instr-profile",
                     str(merged_profile), str(merged_so)))
                mock_path_div.assert_called_once_with(out_dir, "report.txt")
                mock_path_open.assert_called_once_with("w")
                mock_path_open().write.assert_called_once_with(
                    *text_report_content)

                if print_text_report:
                    self.assertEqual(len(calls_run), 3)
                    self.assertEqual(calls_run[2][0],
                                     (coverage_off_target.LLVM_COV, "report",
                                      "--use-color", "--instr-profile",
                                      str(merged_profile), str(merged_so)))

                    calls_print = mock_print.call_args_list
                    self.assertEqual(len(calls_print), 2)
                    self.assertEqual(calls_print[0][0], (*text_report_content,))
                    self.assertEqual(calls_print[1][0],
                                     AnyStringWith("coverage artifacts in"))
                else:
                    self.assertEqual(len(calls_run), 2)
                    mock_print.assert_called_once_with(
                        AnyStringWith("coverage artifacts in"))

    # Use `autospec=True` to mock the unbounded `Path.mkdir` and `Path.__truediv__`
    # methods so that we can assert the values of both the `self` and the `other`
    # arguments of calls.
    @patch("pathlib.Path.mkdir", autospec=True)
    @patch("pathlib.Path.__truediv__", autospec=True)
    @patch("coverage_off_target.run")
    def test_create_out_dir(self, mock_run, mock_path_div, mock_path_mkdir):
        out_root_dir = Path("foo")
        head_hash = ["123abc"]
        head_timestamp = ["123456"]
        out_dir = Path(
            f"{out_root_dir}/{head_timestamp[0]}-{head_hash[0]}/unittest/")

        mock_run.side_effect = (head_hash, head_timestamp)
        mock_path_div.side_effect = (out_dir,)

        self.assertEqual(coverage_off_target.create_out_dir(out_root_dir),
                         out_dir)

        calls = mock_run.call_args_list
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][0], ("git", "rev-parse", "HEAD"))
        self.assertEqual(calls[1][0],
                         ("git", "show", "-s", "--format=%ct", "HEAD"))

        mock_path_div.assert_called_once_with(out_root_dir,
                                              "123456-123abc/unittest/")
        mock_path_mkdir.assert_called_once_with(out_dir,
                                                parents=True,
                                                exist_ok=True)

    @patch("coverage_off_target.generate_report")
    @patch("coverage_off_target.measure_unit_test_coverage")
    @patch("coverage_off_target.create_merged_library")
    @patch("coverage_off_target.gather_and_build_libs")
    @patch("coverage_off_target.create_out_dir")
    def test_main(self, mock_create_out_dir, mock_gather_and_build_libs,
                  mock_create_merged_library, mock_measure_unit_test_coverage,
                  mock_generate_report):
        out_dir = Path("foo")
        merged_so = out_dir / "merged.so"
        merged_profile = out_dir / "merged.profdata"
        libs = ["//foo/bar1", "//foo/bar2"]

        mock_create_out_dir.side_effect = (out_dir,)
        mock_gather_and_build_libs.side_effect = (libs,)

        coverage_off_target.main()

        mock_create_out_dir.assert_called_once_with(Path("coverage"))
        mock_gather_and_build_libs.assert_called()
        mock_create_merged_library.assert_called_once_with(libs, merged_so)
        mock_measure_unit_test_coverage.assert_called_once_with(merged_profile)
        mock_generate_report.assert_called_once_with(out_dir, merged_profile,
                                                     merged_so, False)


if __name__ == "__main__":
    unittest.main()
