# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Sequence

from reggen.access import JsonEnum
from reggen.bits import Bits
from reggen.lib import check_keys, check_name, check_str, check_int, check_list
from reggen.signal import Signal


class IntrType(JsonEnum):
    Event = 1
    Status = 2


_intr_type_map = {'event': IntrType.Event, 'status': IntrType.Status}


class Interrupt(Signal):

    def __init__(self, name: str, desc: str, bits: Bits, intr_type: IntrType):
        super().__init__(name, desc, bits)
        self.intr_type = intr_type

    @staticmethod
    def from_raw(what: str, lsb: int, raw: object) -> 'Interrupt':
        rd = check_keys(raw, what, ['name', 'desc'], ['width', 'type'])

        name = check_name(rd['name'], 'name field of ' + what)
        desc = check_str(rd['desc'], 'desc field of ' + what)
        width = check_int(rd.get('width', 1), 'width field of ' + what)
        if width <= 0:
            raise ValueError('The width field of signal {} ({}) '
                             'has value {}, but should be positive.'.format(
                                 name, what, width))
        bits = Bits(lsb + width - 1, lsb)
        intr_type_str = check_str(rd.get('type', 'event'),
                                  'intr_type field of ' + what)

        try:
            intr_type = _intr_type_map[intr_type_str.lower()]
        except KeyError:
            raise ValueError(
                'The intr_type field of signal {} ({}) '
                'has value {}, but should be either event or status.'.format(
                    name, what, intr_type_str))

        return Interrupt(name, desc, bits, intr_type)

    @staticmethod
    def from_raw_list(what: str, raw: object) -> Sequence['Interrupt']:
        lsb = 0
        ret = []
        for idx, entry in enumerate(check_list(raw, what)):
            entry_what = 'entry {} of {}'.format(idx, what)
            interrupt = Interrupt.from_raw(entry_what, lsb, entry)
            ret.append(interrupt)
            lsb += interrupt.bits.width()
        return ret
