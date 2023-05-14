# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
from enum import Enum

from rich.logging import RichHandler

from util.py.packages.lib.wrapper import Wrapper

log = Wrapper()


class LogLevel(str, Enum):
    ERROR: str = "error"
    WARNING: str = "warning"
    INFO: str = "info"
    DEBUG: str = "debug"


def init(log_level: LogLevel = LogLevel.WARNING):
    global log
    logging.basicConfig(level=log_level.upper(),
                        format="%(message)s",
                        datefmt="[%X]",
                        handlers=[RichHandler()])
    log.replace_wrapped(logging.getLogger("rich"))
