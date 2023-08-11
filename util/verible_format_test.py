# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import importlib
import unittest
from collections import namedtuple
from unittest.mock import patch

# The name of the module under test contains a hyphen, so we cannot
# syntactically say `import verible-format`.
vf = importlib.import_module("verible-format")

# This object is based on `subprocess.CompletedProcess`. It's useful for mocking
# the return value of `subprocess.run`.
MockProc = namedtuple("MockProc", ["stdout", "stderr"])


class Test(unittest.TestCase):
    @patch("subprocess.run")
    def test_get_repo_top(self, mock_run):
        mock_run.side_effect = (MockProc(stdout="/path/to/opentitan\n",
                                         stderr=""), )
        self.assertEqual(vf.get_repo_top(), "/path/to/opentitan")

    @patch("subprocess.run")
    def test_get_repo_top_ignores_stderr(self, mock_run):
        mock_run.side_effect = (MockProc(stdout="/path/to/opentitan\n",
                                         stderr="foo"), )
        self.assertEqual(vf.get_repo_top(), "/path/to/opentitan")

    @patch("subprocess.run")
    def test_build_bazel_args(self, mock_run):
        mock_run.side_effect = (MockProc(stdout="/path/to/opentitan\n",
                                         stderr=""), )
        self.assertEqual(vf.VeribleTool.FORMAT.build_bazel_args(), [
            "/path/to/opentitan/bazelisk.sh",
            "run",
            "--ui_event_filters=-info,-stdout,-stderr",
            "--noshow_progress",
            "//third_party/verible:verible-verilog-format",
            "--",
        ])

    @patch("subprocess.run")
    def test_get_verible_version(self, mock_run):
        mock_run.side_effect = (
            MockProc(stdout="/path/to/opentitan\n", stderr=""),
            MockProc(stdout="v0.0-2135-gb534c1fe\n"
                     "Commit  2022-04-07 12:23:30 -0700\n"
                     "Built   2022-04-07T19:55:11Z\n",
                     stderr=""),
        )
        self.assertEqual(vf.VeribleTool.FORMAT.get_version(),
                         "v0.0-2135-gb534c1fe")


if __name__ == "__main__":
    unittest.main()
