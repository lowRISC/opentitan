# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing clocking or resets for an IP block'''

from typing import Dict, List, Optional
import re

from reggen.lib import check_keys, check_list, check_bool, check_optional_name


class ClockingItem:
    def __init__(self,
                 clock: Optional[str],
                 reset: Optional[str],
                 idle: Optional[str],
                 primary: bool,
                 internal: bool,
                 clock_base_name: Optional[str]):
        if primary:
            assert clock is not None
            assert reset is not None

        self.clock = clock
        self.clock_base_name = clock_base_name
        self.reset = reset
        self.primary = primary
        self.idle = idle
        # Internal means this clock is generated completely internal to the module
        # and not supplied by the top level.
        # However, the IpBlock may need to be aware of this clock for CDC purposes
        self.internal = internal

    @staticmethod
    def from_raw(raw: object, only_item: bool, where: str) -> 'ClockingItem':
        what = f'clocking item at {where}'
        rd = check_keys(raw, what, [], ['clock', 'reset', 'idle', 'primary', 'internal'])

        clock = check_optional_name(rd.get('clock'), 'clock field of ' + what)
        reset = check_optional_name(rd.get('reset'), 'reset field of ' + what)
        idle = check_optional_name(rd.get('idle'), 'idle field of ' + what)
        primary = check_bool(rd.get('primary', only_item),
                             'primary field of ' + what)
        internal = check_bool(rd.get('internal', False),
                              'internal field of ' + what)

        match = re.match(r'^clk_([A-Za-z0-9_]+)_i', str(clock))
        if not clock or clock in ['clk_i', 'scan_clk_i']:
            clock_base_name = ""
        elif match:
            clock_base_name = match.group(1)
        else:
            raise ValueError(f'clock name must be of the form clk_*_i or clk_i. '
                             f'{clock} is illegal.')

        if primary:
            if clock is None:
                raise ValueError('No clock signal for primary '
                                 f'clocking item at {what}.')
            if reset is None:
                raise ValueError('No reset signal for primary '
                                 f'clocking item at {what}.')

        return ClockingItem(clock, reset, idle, primary, internal, clock_base_name)

    def _asdict(self) -> Dict[str, object]:
        ret = {}  # type: Dict[str, object]
        if self.clock is not None:
            ret['clock'] = self.clock,
        if self.reset is not None:
            ret['reset'] = self.reset
        if self.idle is not None:
            ret['idle'] = self.idle

        ret['primary'] = self.primary
        return ret


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

    def clock_signals(self, ret_internal: bool = True) -> List[str]:
        # By default clock_signals returns all clocks, including internal clocks.
        # If the ret_internal input is set to false, then only externally supplied
        # clocks are returned.
        return [item.clock for item in self.items if item.clock is not None and
                (ret_internal or not item.internal)]

    def reset_signals(self) -> List[str]:
        return [item.reset for item in self.items if item.reset is not None]

    def get_by_clock(self, name: Optional[str]) -> ClockingItem:
        ret = None
        for item in self.items:
            if name == item.clock:
                ret = item
                break

        if ret is None:
            raise ValueError(f'The requested clock {name} does not exist.')
        else:
            return ret
