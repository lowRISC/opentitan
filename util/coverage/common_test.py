#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import subprocess
import unittest
from collections import namedtuple
from pathlib import Path, PurePath
from unittest.mock import Mock, mock_open, patch

import common


class AnyStringWith(str):

    def __eq__(self, other):
        return self in other


class AnyDict(dict):

    def __eq__(self, other):
        return True


class TestCommon(unittest.TestCase):

    RUN_ARGS = {
        "check": True,
        "encoding": "ascii",
        "errors": "ignore",
        "env": AnyDict(),
        "stderr": subprocess.PIPE,
        "stdout": subprocess.PIPE,
    }

    @patch("common.subprocess.run")
    def test_run_single_arg_error(self, mock_run):
        mock_run.side_effect = Exception("foo")
        with self.assertRaisesRegex(Exception, "foo"):
            common.run("ls")
        mock_run.assert_called_once_with(("ls", ), **self.RUN_ARGS)

    @patch("common.subprocess.run")
    def test_run_multi_arg_error(self, mock_run):
        mock_run.side_effect = Exception("foo")
        with self.assertRaisesRegex(Exception, "foo"):
            common.run("ls", "-la", "./")
        mock_run.assert_called_once_with(("ls", "-la", "./"), **self.RUN_ARGS)

    @patch("common.subprocess.run")
    def test_run_single_arg_success(self, mock_run):
        MockStreams = namedtuple("MockStdout", ["stdout", "stderr"])
        mock_run.side_effect = (MockStreams(
            stdout="\nline 1\n\nline 2\nline3\n\n", stderr=""), )
        self.assertEqual(common.run("ls"), ["line 1", "line 2", "line3"])
        mock_run.assert_called_once_with(("ls", ), **self.RUN_ARGS)

    @patch("common.subprocess.run")
    def test_run_multi_arg_success(self, mock_run):
        common.run("ls", "-la", "./")
        mock_run.assert_called_once_with(("ls", "-la", "./"), **self.RUN_ARGS)

    @patch("common.run")
    def test_artifacts_relpath(self, mock_run):
        head_hash = ["abcdef"]
        head_timestamp = ["123456"]
        expected_relpath = PurePath(f"{head_timestamp[0]}-{head_hash[0]}")

        mock_run.side_effect = (head_hash, head_timestamp)

        self.assertEqual(common.artifacts_relpath(), expected_relpath)

        calls_run = mock_run.call_args_list
        self.assertEqual(len(calls_run), 2)
        self.assertEqual(calls_run[0][0], ("git", "rev-parse", "HEAD"))
        self.assertEqual(calls_run[1][0],
                         ("git", "show", "-s", "--format=%ct", "HEAD"))

    @patch("common.run")
    def test_instrument_device_libs(self, mock_run):
        device_libs = ["//foo:bar", "//foo:baz"]
        obj_files = ["foo.o", "bar.o", "baz.o"]

        mock_run.side_effect = (None, obj_files)

        self.assertEqual(common.instrument_device_libs(device_libs, 'qux'),
                         obj_files)
        calls_run = mock_run.call_args_list
        self.assertEqual(len(calls_run), 2)
        self.assertEqual(calls_run[0][0],
                         (common.BAZEL, "build", "--config=qux", *device_libs))
        starlark_list = "[f.path for f in target.output_groups.compilation_outputs.to_list()]"
        self.assertEqual(calls_run[1][0],
                         (common.BAZEL, "cquery", "--config=qux",
                          "(//foo:bar + //foo:baz)", '--output=starlark',
                          f"--starlark:expr='\\n'.join({starlark_list})"))

    @patch("common.run")
    def test_get_test_log_dirs(self, mock_run):
        test_targets = ["//foo:bar", "//foo:baz"]
        test_log_dir = ["/qux/testlogs"]

        mock_run.side_effect = (test_log_dir, )

        self.assertEqual(
            common.get_test_log_dirs(test_targets),
            [Path("/qux/testlogs/foo/bar"),
             Path("/qux/testlogs/foo/baz")])
        mock_run.assert_called_once_with(common.BAZEL, "info",
                                         "bazel-testlogs")

    @patch("common.print")
    @patch("pathlib.Path.open", new_callable=mock_open)
    @patch("pathlib.Path.__truediv__",
           side_effect=Path.__truediv__,
           autospec=True)
    @patch("common.run")
    def test_generate_report(self, mock_run, mock_path_div, mock_path_open,
                             mock_print):
        for print_text_report in (True, False):
            for m in [mock_run, mock_path_div, mock_path_open, mock_print]:
                m.reset_mock()
            with self.subTest(f"print_text_report:{print_text_report}"):
                out_dir = Path("foo")
                merged_profile = Path("merged.profdata")
                merged_library = Path("merged.so")
                report_title = "My Report"
                text_report_content = [
                    "<contents of coverage report in text format>"
                ]
                # (1) html report, (2) text report, (3) print text report (if requested)
                mock_run.side_effect = ([], text_report_content,
                                        text_report_content)

                common.generate_report(out_dir, merged_profile, merged_library,
                                       report_title, print_text_report)

                calls_run = mock_run.call_args_list
                self.assertEqual(
                    calls_run[0][0],
                    (common.LLVM_COV, "show", "--show-line-counts",
                     "--show-regions", f"--project-title={report_title}",
                     "--format=html", "--output-dir=./foo", "--instr-profile",
                     str(merged_profile), str(merged_library)))
                self.assertEqual(calls_run[1][0],
                                 (common.LLVM_COV, "report", "--instr-profile",
                                  str(merged_profile), str(merged_library)))
                mock_path_div.assert_called_once_with(out_dir, "report.txt")
                mock_path_open.assert_called_once_with("w")
                mock_path_open().write.assert_called_once_with(
                    *text_report_content)

                if print_text_report:
                    self.assertEqual(len(calls_run), 3)
                    self.assertEqual(calls_run[2][0],
                                     (common.LLVM_COV, "report", "--use-color",
                                      "--instr-profile", str(merged_profile),
                                      str(merged_library)))

                    calls_print = mock_print.call_args_list
                    self.assertEqual(len(calls_print), 2)
                    self.assertEqual(calls_print[0][0],
                                     (*text_report_content, ))
                    self.assertEqual(calls_print[1][0],
                                     AnyStringWith("coverage artifacts in"))
                else:
                    self.assertEqual(len(calls_run), 2)
                    mock_print.assert_called_once_with(
                        AnyStringWith("coverage artifacts in"))

    @patch("common.generate_report")
    @patch("common.get_test_log_dirs")
    @patch("common.instrument_device_libs")
    # Use `autospec=True` to mock the unbounded `Path.mkdir` and `Path.__truediv__`
    # methods so that we can assert the values of both the `self` and the `other`
    # arguments of calls.
    @patch("pathlib.Path.mkdir", autospec=True)
    @patch("pathlib.Path.__truediv__", autospec=True)
    @patch("common.run")
    def test_measure_coverage(self, mock_run, mock_path_div, mock_path_mkdir,
                              mock_instrument_device_libs,
                              mock_get_test_logs_dir, mock_generate_report):
        out_dir = Path("{out_root_dir}/123456-cafecafe/{out_sub_dir}")
        device_libs_all = ["//foo:bar1", "//foo:bar2", "//foo:bar3"]
        device_libs = ["//for:bar2", "//foo:bar3"]
        obj_files = ["//foo:bar2.o", "//foo:bar3.o"]
        merged_library = out_dir / "merged.so"
        bazel_test_type = common.BazelTestType.CC_TEST
        config = "my_config"
        test_targets_all = ["//foo:test1", "//foo:test2", "//foo:test3"]
        test_targets = ["//foo:test1", "//foo:test3"]
        test_log_dirs = ["/testlogs/foo/test1", "/testlogs/foo/test3"]
        profile_files = [
            "/testlogs/foo/test1/coverage.profdata",
            "/testlogs/foo/test3/coverage.profdata"
        ]
        merged_profile = out_dir / "merged.profdata"
        report_title = "My Report"
        print_text_report = True

        mock_libs_fn = Mock(side_effect=(device_libs, ))
        mock_objs_fn = Mock(side_effect=(obj_files, ))
        mock_test_targets_fn = Mock(side_effect=(test_targets, ))
        mock_test_log_dirs_fn = Mock(side_effect=(profile_files, ))

        mock_run.side_effect = (
            device_libs_all,
            test_targets_all,
            None,
            None,
        )
        mock_instrument_device_libs.side_effect = (obj_files, )
        mock_get_test_logs_dir.side_effect = (test_log_dirs, )

        common.measure_coverage(
            bazel_test_type=bazel_test_type,
            config=config,
            libs_fn=mock_libs_fn,
            log_level=common.LogLevel.NONE,
            objs_fn=mock_objs_fn,
            out_dir=out_dir,
            print_text_report=print_text_report,
            report_title=report_title,
            test_log_dirs_fn=mock_test_log_dirs_fn,
            test_targets_fn=mock_test_targets_fn,
        )

        mock_path_mkdir.assert_called_once_with(out_dir,
                                                parents=True,
                                                exist_ok=True)
        calls_run = mock_run.call_args_list
        self.assertEqual(len(calls_run), 4)
        self.assertEqual(calls_run[0][0],
                         (common.BAZEL, "query", common.DEVICE_LIBS_QUERY))
        mock_libs_fn.assert_called_once_with(device_libs_all)
        mock_instrument_device_libs.assert_called_once_with(
            device_libs, config)
        mock_objs_fn.assert_called_once_with(out_dir / "merged.so", obj_files)
        self.assertEqual(
            calls_run[1][0],
            (common.BAZEL, "query", AnyStringWith(bazel_test_type.value)))
        mock_test_targets_fn.assert_called_once_with(test_targets_all)
        self.assertEqual(
            calls_run[2][0],
            (common.BAZEL, "coverage", "--define", "bitstream=skip",
             f"--config={config}", "--test_output=all", *test_targets))
        mock_get_test_logs_dir.assert_called_once_with(test_targets)
        mock_test_log_dirs_fn.assert_called_once_with(test_log_dirs)
        self.assertEqual(calls_run[3][0],
                         (common.LLVM_PROFDATA, "merge", "--sparse",
                          "--output", str(merged_profile), *profile_files))
        mock_generate_report.assert_called_once_with(out_dir, merged_profile,
                                                     merged_library,
                                                     report_title,
                                                     print_text_report)


if __name__ == "__main__":
    unittest.main()
