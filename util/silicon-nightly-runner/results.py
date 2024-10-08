#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""
Extracted result information from the tests.
"""

import datetime

from dataclasses import dataclass, field
from enum import Enum


class State(Enum):
    PASSED = "Passed"
    FAILED = "Failed"
    SKIPPED = "Skipped"
    ERRORED = "Error"


@dataclass
class Result(object):
    name: str
    state: State
    duration: float
    output: str


@dataclass
class Results(object):
    hostname: str = ""
    tests: list[Result] = field(default_factory=list)
    timestamp: datetime.datetime = None

    def __iter__(self):
        return iter(self.tests)

    @property
    def ntests(self):
        return len(self.tests)

    @property
    def npassed(self):
        return len([test for test in self.tests if test.state == State.PASSED])

    @property
    def nskipped(self):
        return len([test for test in self.tests if test.state == State.SKIPPED])

    @property
    def nfailed(self):
        return len([test for test in self.tests if test.state == State.FAILED])

    @property
    def nerrored(self):
        return len([test for test in self.tests if test.state == State.ERRORED])

    @property
    def duration(self):
        return sum(test.duration for test in self.tests)
