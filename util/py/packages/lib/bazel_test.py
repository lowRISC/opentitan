#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from pathlib import Path
from unittest.mock import patch

from util.py.packages.lib.bazel import (build_target, get_rule_deps_of_kind,
                                        get_target_files_with_ext)


class TestRun(unittest.TestCase):

    @patch("util.py.packages.lib.bazel.run")
    def test_build_target(self, mock_run):
        build_target("my_target", ["config1", "config2"])
        mock_run.assert_called_once_with("./bazelisk.sh", "build",
                                         "--config=config1",
                                         "--config=config2", "my_target")

    @patch("util.py.packages.lib.bazel.run")
    def test_get_rule_deps_of_kind(self, mock_run):
        mock_run.side_effect = ("query result", )

        self.assertEqual(get_rule_deps_of_kind("my_target", "my_kind"),
                         "query result")
        mock_run.assert_called_once_with(
            "./bazelisk.sh", "query",
            "kind('^my_kind rule$', deps('my_target') ^ siblings('my_target'))"
        )

    @patch("util.py.packages.lib.bazel.run")
    def test_get_target_files_with_ext(self, mock_run):
        mock_run.side_effect = (["/my/path/1", "/my/path/2"], )

        self.assertEqual(
            get_target_files_with_ext("my_target",
                                      ["my_config_1", "my_config_2"],
                                      "my_ext"),
            [Path("/my/path/1"), Path("/my/path/2")])
        mock_run.assert_called_once_with(
            "./bazelisk.sh", "cquery", "--config=my_config_1",
            "--config=my_config_2", "--output=starlark",
            ("--starlark:expr='\\n'.join("
             "[f.path for f in target.files.to_list() if f.path.endswith('.my_ext')])"
             ), "my_target")


if __name__ == "__main__":
    unittest.main()
