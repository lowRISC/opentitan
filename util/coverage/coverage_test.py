#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from collections import namedtuple
from pathlib import Path
from unittest.mock import patch

import common

import coverage

MockParams = namedtuple("MockParams", ["foo"])


class TestExtractProfileData(unittest.TestCase):

    @patch.dict("coverage.PARAMS",
                {common.CoverageType.UNITTEST: MockParams("bar")},
                clear=True)
    @patch("coverage.measure")
    def test_measure(self, mock_measure_coverage):
        coverage_type = common.CoverageType.UNITTEST
        out_dir = Path("foo")
        log_level = common.LogLevel.DEBUG
        print_text_report = True

        coverage.measure(coverage_type, out_dir, log_level, print_text_report)

        mock_measure_coverage.assert_called_once_with(coverage_type, out_dir,
                                                      log_level,
                                                      print_text_report)


if __name__ == "__main__":
    unittest.main()
