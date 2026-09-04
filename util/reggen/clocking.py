# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Code representing clocking or resets for an IP block'''

from typing import Dict, List, Optional, Tuple
import re

from reggen.lib import (PARTITIONS, PART_PRIMARY, PART_SECONDARY, check_keys, check_list,
                        check_bool, check_optional_name)


class ClockingItem:

    def __init__(self, clock: Optional[str], reset: Optional[str],
                 idle: Optional[str], primary: bool, internal: bool,
                 clock_base_name: Optional[str],
                 partition: str = PART_PRIMARY):
        if primary:
            assert clock is not None
            assert reset is not None
        assert partition in PARTITIONS

        self.clock = clock
        self.clock_base_name = clock_base_name
        self.reset = reset
        self.primary = primary
        self.idle = idle
        # Internal means this clock is generated completely internal to the module
        # and not supplied by the top level.
        # However, the IpBlock may need to be aware of this clock for CDC purposes
        self.internal = internal
        # The partition of a split IP that this clock/reset belongs to.
        self.partition = partition

    @staticmethod
    def from_raw(raw: object, only_item: bool, where: str,
                 partition: str = PART_PRIMARY) -> 'ClockingItem':
        what = f'clocking item at {where}'
        rd = check_keys(raw, what, [],
                        ['clock', 'reset', 'idle', 'primary', 'internal'])

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
            raise ValueError(
                f'clock name must be of the form clk_*_i or clk_i. '
                f'{clock} is illegal.')

        if primary:
            if clock is None:
                raise ValueError('No clock signal for primary '
                                 f'clocking item at {what}.')
            if reset is None:
                raise ValueError('No reset signal for primary '
                                 f'clocking item at {what}.')

        return ClockingItem(clock, reset, idle, primary, internal,
                            clock_base_name, partition)

    def _asdict(self) -> Dict[str, object]:
        ret = {}  # type: Dict[str, object]
        if self.clock is not None:
            ret['clock'] = self.clock
        if self.reset is not None:
            ret['reset'] = self.reset
        if self.idle is not None:
            ret['idle'] = self.idle
        # Only emitted for split IPs, so non-split IPs see default attribute.
        # TODO: Consider always exporting so no check is needed where topgen reads this.
        if self.partition != PART_PRIMARY:
            ret['partition'] = self.partition
        ret['primary'] = self.primary
        return ret


class Clocking:

    def __init__(self, items: List[ClockingItem],
                 primary_clocks: Dict[str, ClockingItem]):
        assert items
        assert PART_PRIMARY in primary_clocks
        self.items = items
        self._primaries = primary_clocks
        self.primary = primary_clocks[PART_PRIMARY]

    @staticmethod
    def from_raw(raw: object, where: str) -> 'Clocking':
        '''Parse the clocking definition, which comes in one of two shapes.

        A flat list of clocking items describes the clocking for a non split IP.
        A {primary, secondary} dict describes the partitions of a split IP.
        '''
        what = f'clocking items at {where}'

        # Extract the raw lists for each partition.
        raw_partitions: List[Tuple[str, List[object]]] = []
        if isinstance(raw, dict):
            # An unclocked secondary partition may omit the key or leave it
            # empty.
            rd = check_keys(raw, what, [PART_PRIMARY], [PART_SECONDARY])
            for partition in PARTITIONS:
                if rd.get(partition):
                    raw_clocks = check_list(rd[partition],
                                            f'{partition} partition of {what}')
                    raw_partitions.append((partition, raw_clocks))
        elif isinstance(raw, list):
            raw_partitions.append((PART_PRIMARY, raw))
        else:
            raise ValueError(f'{what} is of type {type(raw).__name__}, but '
                             'must be either a list of clocking items or a '
                             'dict with primary / secondary partitions.')

        # Generate a list of all clockings and extract the primary clocking for
        # each partition.
        items: List[ClockingItem] = []
        primaries: Dict[str, ClockingItem] = {}
        for partition, raw_clocks in raw_partitions:
            partition_what = f'{partition} partition of {what}'
            if not raw_clocks:
                raise ValueError(f'Empty list of clocking items at '
                                 f'{partition_what}.')

            just_one_item = len(raw_clocks) == 1

            partition_primaries = []
            for idx, raw_item in enumerate(raw_clocks):
                item_where = f'entry {idx} of {partition_what}'
                item = ClockingItem.from_raw(raw_item, just_one_item,
                                             item_where, partition)
                if item.primary:
                    partition_primaries.append(item)
                items.append(item)

            if len(partition_primaries) != 1:
                raise ValueError('There should be exactly one primary clocking '
                                 f'item at {partition_what}, but we saw '
                                 f'{len(partition_primaries)}.')
            primaries[partition] = partition_primaries[0]

        return Clocking(items, primaries)

    @property
    def partitions(self) -> List[str]:
        return [p for p in PARTITIONS if p in self._primaries]

    def has_partition(self, partition: str) -> bool:
        return partition in self._primaries

    def items_for(self, partition: Optional[str]) -> List[ClockingItem]:
        '''Return the list of clocking items for the given partition.

        If partition is None, return all items.'''
        if partition is None:
            return self.items
        return [item for item in self.items if item.partition == partition]

    def get_primary_clock(self, partition: str = PART_PRIMARY) -> Optional[ClockingItem]:
        return self._primaries.get(partition)

    def other_clocks(self, partition: Optional[str] = PART_PRIMARY) -> List[str]:
        ret = []
        for item in self.items_for(partition):
            if not item.primary and item.clock is not None:
                ret.append(item.clock)
        return ret

    def clock_signals(self,
                      ret_internal: bool = True,
                      partition: Optional[str] = PART_PRIMARY) -> List[str]:
        # By default clock_signals returns all clocks, including internal clocks.
        # If the ret_internal input is set to false, then only externally supplied
        # clocks are returned.
        return [
            item.clock for item in self.items_for(partition)
            if item.clock is not None and (ret_internal or not item.internal)
        ]

    def reset_signals(self, partition: Optional[str] = PART_PRIMARY) -> List[str]:
        return [item.reset for item in self.items_for(partition) if item.reset is not None]

    def get_by_clock(self,
                     name: Optional[str],
                     partition: Optional[str] = PART_PRIMARY) -> ClockingItem:
        ret = None
        for item in self.items_for(partition):
            if name == item.clock:
                ret = item
                break

        if ret is None:
            raise ValueError(f'The requested clock {name} does not exist.')
        else:
            return ret

    def as_raw(self) -> object:
        '''Serialize back to the hjson shape this was parsed from.'''
        if self.partitions == [PART_PRIMARY]:
            return self.items
        return {p: self.items_for(p) for p in self.partitions}
