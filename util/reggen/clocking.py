# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing clocking or resets for an IP block'''

from typing import Dict, List, Optional

from .lib import check_keys, check_list, check_bool, check_optional_name
import re


class ClockingItem:
    def __init__(self, clock: Optional[str], reset: Optional[str], primary: bool):
        if primary:
            assert clock is not None
            assert reset is not None

        self.clock = clock
        self.reset = reset
        self.primary = primary

    @staticmethod
    def from_raw(raw: object, only_item: bool, where: str) -> 'ClockingItem':
        what = f'clocking item at {where}'
        rd = check_keys(raw, what, [], ['clock', 'reset', 'primary'])

        clock = check_optional_name(rd.get('clock'), 'clock field of ' + what)
        reset = check_optional_name(rd.get('reset'), 'reset field of ' + what)
        primary = check_bool(rd.get('primary', only_item),
                             'primary field of ' + what)

        if primary:
            if clock is None:
                raise ValueError('No clock signal for primary '
                                 f'clocking item at {what}.')
            if reset is None:
                raise ValueError('No reset signal for primary '
                                 f'clocking item at {what}.')

        return ClockingItem(clock, reset, primary)

    def set_reg_clock(self, clock: str) -> None:

        self.reg = True

    def _asdict(self) -> Dict[str, object]:
        ret = {}  # type: Dict[str, object]
        if self.clock is not None:
            ret['clock'] = self.clock,
        if self.reset is not None:
            ret['reset'] = self.reset

        ret['primary'] = self.primary
        return ret

    def get_base_name(self) -> str:
        if not self.clock:
            raise ValueError('Cannot extract clock base name from None clock')

        match = re.match(r'^clk_([A-Za-z0-9_]+)_i', str(self.clock))
        if match:
            return match.group(1)
        else:
            return ""


class Clocking:
    def __init__(self, items: List[ClockingItem], primary: ClockingItem):
        assert items
        self.items = items
        self.primary = primary

    @staticmethod
    def from_raw(raw: object, where: str) -> 'Clocking':
        what = f'clocking items at {where}'
        raw_items = check_list(raw, what)
        if not raw_items:
            raise ValueError(f'Empty list of clocking items at {where}.')

        just_one_item = len(raw_items) == 1

        items = []
        primaries = []
        for idx, raw_item in enumerate(raw_items):
            item_where = f'entry {idx} of {what}'
            item = ClockingItem.from_raw(raw_item, just_one_item, item_where)
            if item.primary:
                primaries.append(item)
            items.append(item)

        if len(primaries) != 1:
            raise ValueError('There should be exactly one primary clocking '
                             f'item at {where}, but we saw {len(primaries)}.')

        return Clocking(items, primaries[0])

    def other_clocks(self) -> List[str]:
        ret = []
        for item in self.items:
            if not item.primary and item.clock is not None:
                ret.append(item.clock)
        return ret

    def clock_signals(self) -> List[str]:
        return [item.clock for item in self.items if item.clock is not None]

    def reset_signals(self) -> List[str]:
        return [item.reset for item in self.items if item.reset is not None]

    def get_by_clock(self, name: Optional[str]) -> object:
        for item in self.items:
            if name == item.clock:
                return item

        return None
