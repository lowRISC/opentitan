# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from reggen.lib import check_keys
from reggen.window import Window


class Memory:
    '''A class representing a memory'''

    windows: list[Window] = list()
    """A list of windows into the memory"""

    def __init__(self) -> None:
        pass

    @staticmethod
    def from_raw(raw: object) -> 'Memory':
        # No keys supported at the moment.
        check_keys(raw, 'memory', [], [])
        return Memory()

    def _asdict(self) -> dict[str, object]:
        return {}
