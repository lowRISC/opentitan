#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import subprocess
import unittest
from collections import namedtuple
from unittest.mock import patch

from util.py.packages.lib import ot_logging
from util.py.packages.lib.run import run

ot_logging.init()


class AnyDict(dict):

    def __eq__(self, other):
        return True


class TestRun(unittest.TestCase):

    RUN_ARGS = {
        "check": True,
        "encoding": "ascii",
        "errors": "ignore",
        "env": AnyDict(),
        "stderr": subprocess.PIPE,
        "stdout": subprocess.PIPE,
    }

    @patch("util.py.packages.lib.run.subprocess.run")
    def test_run_single_arg_error(self, mock_run):
        mock_run.side_effect = Exception("foo")
        with self.assertRaisesRegex(Exception, "foo"):
            run("ls")
        mock_run.assert_called_once_with(("ls", ), **self.RUN_ARGS)

    @patch("util.py.packages.lib.run.subprocess.run")
    def test_run_multi_arg_error(self, mock_run):
        mock_run.side_effect = Exception("foo")
        with self.assertRaisesRegex(Exception, "foo"):
            run("ls", "-la", "./")
        mock_run.assert_called_once_with(("ls", "-la", "./"), **self.RUN_ARGS)

    @patch("util.py.packages.lib.run.subprocess.run")
    def test_run_single_arg_success(self, mock_run):
        MockStreams = namedtuple("MockStdout", ["stdout", "stderr"])
        mock_run.side_effect = (MockStreams(
            stdout="\nline 1\n\nline 2\nline3\n\n", stderr=""), )
        self.assertEqual(run("ls"), ["line 1", "line 2", "line3"])
        mock_run.assert_called_once_with(("ls", ), **self.RUN_ARGS)

    @patch("util.py.packages.lib.run.subprocess.run")
    def test_run_multi_arg_success(self, mock_run):
        run("ls", "-la", "./")
        mock_run.assert_called_once_with(("ls", "-la", "./"), **self.RUN_ARGS)


if __name__ == "__main__":
    unittest.main()
