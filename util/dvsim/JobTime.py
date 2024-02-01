# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""An abstraction for maintaining job runtime and its units.
"""

from copy import copy
from typing import Tuple
import unittest


class JobTime:
    # Possible units.
    units = ["h", "m", "s", "ms", "us", "ns", "ps", "fs"]
    dividers = [60.0, ] * 3 + [1000.0, ] * 5

    def __init__(self, time: float = 0.0, unit: str = "s", normalize: bool = True):
        self.set(time, unit, normalize)

    def set(self, time: float, unit: str, normalize: bool = True):
        """Public API to set the instance variables time, unit."""
        self.__time = time
        self.__unit = unit
        assert self.__unit in self.units
        if normalize:
            self._normalize()

    def get(self) -> Tuple[float, str]:
        """Returns the time and unit as a tuple."""
        return self.__time, self.__unit

    def with_unit(self, unit: str):
        """Return a copy of this object that has a specific unit and a value
        scaled accordingly.

        Note that the scaling may not be lossless due to rounding errors and
        limited precision.
        """
        target_index = self.units.index(unit)
        index = self.units.index(self.__unit)
        jt = copy(self)
        while index < target_index:
            index += 1
            jt.__time *= self.dividers[index]
            jt.__unit = self.units[index]
        while index > target_index:
            jt.__time /= self.dividers[index]
            index -= 1
            jt.__unit = self.units[index]
        return jt

    def _normalize(self):
        """Brings the time and its units to a more meaningful magnitude.

        If the time is very large with a lower magnitude, this method divides
        the time to get it to the next higher magnitude recursively, stopping
        if the next division causes the time to go < 1. Examples:
          123123232ps -> 123.12us
          23434s -> 6.509h

        The supported magnitudes and their associated divider values are
        provided by JobTime.units and JobTime.dividers.
        """
        if self.__time == 0:
            return

        index = self.units.index(self.__unit)
        normalized_time = self.__time
        while index > 0 and normalized_time >= self.dividers[index]:
            normalized_time = normalized_time / self.dividers[index]
            index = index - 1
        self.__time = normalized_time
        self.__unit = self.units[index]

    def __str__(self):
        """Indicates <time><unit> as string.

        The time value is truncated to 3 decimal places.
        Returns an empty string if the __time is set to 0.
        """
        if self.__time == 0:
            return ""
        else:
            return f"{self.__time:.3f}{self.__unit}"

    def __eq__(self, other) -> bool:
        assert isinstance(other, JobTime)
        other_time, other_unit = other.get()
        return self.__unit == other_unit and self.__time == other_time

    def __gt__(self, other) -> bool:
        if self.__time == 0:
            return False

        assert isinstance(other, JobTime)
        other_time, other_unit = other.get()
        if other_time == 0:
            return True

        sidx = JobTime.units.index(self.__unit)
        oidx = JobTime.units.index(other_unit)
        if sidx < oidx:
            return True
        elif sidx > oidx:
            return False
        else:
            return self.__time > other_time


class TestJobTimeMethods(unittest.TestCase):

    def test_with_unit(self):
        # First data set
        h = JobTime(6, 'h', normalize=False)
        m = JobTime(360, 'm', normalize=False)
        s = JobTime(21600, 's', normalize=False)
        ms = JobTime(21600000, 'ms', normalize=False)
        for src in [h, m, s, ms]:
            for unit, dst in [('h', h), ('m', m), ('s', s), ('ms', ms)]:
                self.assertEqual(src.with_unit(unit), dst)
        # Second data set
        fs = JobTime(123456000000, 'fs', normalize=False)
        ps = JobTime(123456000, 'ps', normalize=False)
        ns = JobTime(123456, 'ns', normalize=False)
        us = JobTime(123.456, 'us', normalize=False)
        ms = JobTime(0.123456, 'ms', normalize=False)
        for src in [fs, ps, ns, us, ms]:
            for unit, dst in [('fs', fs), ('ps', ps), ('ns', ns), ('us', us),
                              ('ms', ms)]:
                self.assertEqual(src.with_unit(unit), dst)
