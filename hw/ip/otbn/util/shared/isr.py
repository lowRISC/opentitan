# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Iterable
from serialize.parse_helpers import (check_keys, check_str, check_list,
                                     check_int, check_bool, load_yaml)


class Isr:
    def __init__(self, name: str, address: int,
                 doc: str, read_only: bool, bits: Dict[int, str]) -> None:
        self.name = name
        self.address = address
        self.doc = doc
        self.read_only = read_only
        self.bits = bits

    def access_str(self) -> str:
        return 'RO' if self.read_only else 'RW'

    @staticmethod
    def from_yml(yml: object) -> 'Isr':
        yd = check_keys(yml, 'isr',
                        ['name', 'address', 'doc'],
                        ['read-only', 'bits'])
        name = check_str(yd['name'], 'name')
        address = check_int(yd['address'], 'index/address')
        if address < 0:
            raise ValueError(f'Address of ISR {name:!r} is negative.')
        read_only = check_bool(yd.get('read-only', False), 'read-only flag')
        doc = check_str(yd['doc'], 'documentation')
        pre_bits = yd.get('bits', {})
        if not isinstance(pre_bits, dict):
            raise ValueError(f'bits field of ISR {name:!r} is not a dict.')
        bits = {}  # type: Dict[int, str]
        for k, v in pre_bits.items():
            k_int = check_int(k, 'address of ISR bit')
            v_str = check_str(v, f'description of ISR bit {k}')
            bits[k_int] = v_str

        return Isr(name, address, doc, read_only, bits)


def read_isrs(path: str) -> Iterable[Isr]:
    isrs = {}  # type: Dict[int, Isr]
    yml = load_yaml(path, None)
    for isr_yml in check_list(yml, 'contents of ISR file'):
        isr = Isr.from_yml(isr_yml)
        if isr.address in isrs:
            raise ValueError(f'Multiple ISRs at address {isr.address}')
        isrs[isr.address] = isr

    return isrs.values()
