# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""An abstraction for maintaining job runtime and its units.
"""

from typing import Tuple


class JobTime:
    # Possible units.
    units = ["h", "m", "s", "ms", "us", "ns", "ps", "fs"]
    dividers = [60.0, ] * 3 + [1000.0, ] * 5

    def __init__(self, time: float = 0.0, unit: str = "s"):
        self.set(time, unit)

    def set(self, time: float, unit: str):
        """Public API to set the instance variables time, unit."""
        self.__time = time
        self.__unit = unit
        assert self.__unit in self.units
        self._normalize()

    def get(self) -> Tuple[float, str]:
        """Returns the time and unit as a tuple."""
        return self.__time, self.__unit

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
