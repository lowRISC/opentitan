# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Sequence

from reggen.bits import Bits
from reggen.lib import (check_keys, check_name, check_str, check_int,
                        check_list, check_bool, check_partition)


class Signal:

    # For split IPs, the partition ('primary' / 'secondary') this signal
    # belongs to. A class-level default so it stays out of an instance's
    # __dict__ unless explicitly non-default -- topgen dumps leftover objects
    # via `default=vars`, so an unconditional instance attribute would leak
    # `partition: primary` into generated configs.
    partition = 'primary'

    def __init__(self, name: str, desc: str, bits: Bits,
                 enabled_after_reset: bool = False,
                 partition: str = 'primary'):
        self.name = name
        self.desc = desc
        self.bits = bits
        self.enabled_after_reset = enabled_after_reset
        if partition != 'primary':
            self.partition = partition

    @staticmethod
    def from_raw(what: str, lsb: int, raw: object) -> 'Signal':
        rd = check_keys(raw, what, ["name", "desc"],
                        ["width", "enabled_after_reset", "partition"])

        name = check_name(rd['name'], 'name field of ' + what)
        desc = check_str(rd['desc'], 'desc field of ' + what)
        width = check_int(rd.get('width', 1), 'width field of ' + what)
        enabled_after_reset = check_bool(rd.get("enabled_after_reset", False),
                                         "enabled_after_reset field of " + what)
        partition = check_partition(rd.get("partition", "primary"),
                                    "partition field of " + what)

        if width <= 0:
            raise ValueError(f'The width field of signal {name} ({what}) '
                             f'has value {width}, but should be positive.')

        bits = Bits(lsb + width - 1, lsb)

        return Signal(name, desc, bits, enabled_after_reset, partition)

    @staticmethod
    def from_raw_list(what: str, raw: object) -> Sequence['Signal']:
        lsb = 0
        ret = []
        for idx, entry in enumerate(check_list(raw, what)):
            entry_what = 'entry {} of {}'.format(idx, what)
            interrupt = Signal.from_raw(entry_what, lsb, entry)
            ret.append(interrupt)
            lsb += interrupt.bits.width()
        return ret

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'desc': self.desc,
            'width': str(self.bits.width())
        }

    def as_nwt_dict(self, type_field: str) -> Dict[str, object]:
        '''Return a view of the signal as a dictionary

        The dictionary has fields "name", "width" and "type", the last
        of which comes from the type_field argument. Used for topgen
        integration.

        '''
        ret = {
            'name': self.name,
            'width': self.bits.width(),
            'type': type_field
        }  # type: Dict[str, object]
        # Only emitted for split IPs, so non-split IPs see no change.
        if self.partition != 'primary':
            ret['partition'] = self.partition
        return ret
