#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from collections import namedtuple
from pathlib import (
    Path,
    PurePath,
)
import unittest
from unittest.mock import patch

import common
import coverage

MockParams = namedtuple("MockParams", ["foo"])


class TestExtractProfileData(unittest.TestCase):

    @patch("coverage.UNITTEST_PARAMS", MockParams("bar"))
    @patch("coverage.measure_coverage")
    def test_measure(self, mock_measure_coverage):
        out_root_dir = Path("foo")
        log_level = common.LogLevel.DEBUG
        print_text_report = True

        coverage.measure(out_root_dir, log_level, print_text_report)

        mock_measure_coverage.assert_called_once_with(
            log_level=log_level,
            out_root_dir=out_root_dir,
            out_sub_dir=PurePath("unit"),
            print_text_report=print_text_report,
            foo="bar")


if __name__ == "__main__":
    unittest.main()
