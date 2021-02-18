# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List

from .bits import Bits
from .signal import Signal
from .lib import check_keys, check_name, check_str, check_list


class Alert(Signal):
    def __init__(self, name: str, desc: str, bit: int):
        super().__init__(name, desc, Bits(bit, bit))
        self.bit = bit

    @staticmethod
    def from_raw(what: str,
                 lsb: int,
                 raw: object) -> 'Alert':
        rd = check_keys(raw, what, ['name', 'desc'], [])

        name = check_name(rd['name'], 'name field of ' + what)
        desc = check_str(rd['desc'], 'desc field of ' + what)
        return Alert(name, desc, lsb)

    @staticmethod
    def from_raw_list(what: str, raw: object) -> List['Alert']:
        ret = []
        for idx, entry in enumerate(check_list(raw, what)):
            entry_what = 'entry {} of {}'.format(idx, what)
            alert = Alert.from_raw(entry_what, idx, entry)
            ret.append(alert)
        return ret

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'desc': self.desc,
        }
