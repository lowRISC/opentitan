# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Sequence

from .bits import Bits
from .lib import check_keys, check_name, check_str, check_int, check_list


class Signal:
    def __init__(self, name: str, desc: str, bits: Bits):
        self.name = name
        self.desc = desc
        self.bits = bits

    @staticmethod
    def from_raw(what: str, lsb: int, raw: object) -> 'Signal':
        rd = check_keys(raw, what,
                        ['name', 'desc'],
                        ['width'])

        name = check_name(rd['name'], 'name field of ' + what)
        desc = check_str(rd['desc'], 'desc field of ' + what)
        width = check_int(rd.get('width', 1), 'width field of ' + what)
        if width <= 0:
            raise ValueError('The width field of signal {} ({}) '
                             'has value {}, but should be positive.'
                             .format(name, what, width))

        bits = Bits(lsb + width - 1, lsb)

        return Signal(name, desc, bits)

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
        return {'name': self.name,
                'width': self.bits.width(),
                'type': type_field}
