#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import unittest
from unittest.mock import call, patch

from util.py.packages.lib.ot_logging import LogLevel, init, log


class TestLogging(unittest.TestCase):

    def test_log_level_definitions(self):
        self.assertSetEqual({"ERROR", "WARNING", "INFO", "DEBUG"},
                            set([level.name for level in LogLevel]))
        for level in LogLevel:
            self.assertEqual(level.value, level.name.lower())

    def test_not_initialized(self):
        with self.assertRaisesRegex(RuntimeError, "not initialized"):
            log.debug("foo")

    @patch("util.py.packages.lib.ot_logging.log.replace_wrapped")
    @patch("util.py.packages.lib.ot_logging.logging.getLogger")
    @patch("util.py.packages.lib.ot_logging.logging.basicConfig")
    @patch("util.py.packages.lib.ot_logging.RichHandler")
    def test_init(self, mock_rich_handler, mock_basic_config, mock_get_logger,
                  mock_replace_wrapped):
        INIT_ARGS = {
            "level": LogLevel.WARNING.value.upper(),
            "format": "%(message)s",
            "datefmt": "[%X]",
            "handlers": ["my_handler"],
        }
        mock_rich_handler.side_effect = ("my_handler", ) * 2
        mock_get_logger.side_effect = ("my_logger_1", "my_logger_2")

        # Default level
        init()
        # Debug level
        init(log_level=LogLevel.DEBUG)

        calls_rich_handler = mock_rich_handler.call_args_list
        self.assertEqual(calls_rich_handler, [call(), call()])

        calls_basic_config = mock_basic_config.call_args_list
        self.assertEqual(
            calls_basic_config,
            [call(**INIT_ARGS),
             call(**{
                 **INIT_ARGS, "level": "DEBUG"
             })])

        calls_get_logger = mock_get_logger.call_args_list
        self.assertEqual(calls_get_logger, [call("rich")] * 2)

        calls_replace_wrapped = mock_replace_wrapped.call_args_list
        self.assertEqual(
            calls_replace_wrapped,
            [call("my_logger_1"), call("my_logger_2")])


if __name__ == "__main__":
    unittest.main()
