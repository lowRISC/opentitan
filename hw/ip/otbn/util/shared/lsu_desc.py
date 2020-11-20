# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List

from .yaml_parse_helpers import check_keys, check_str, check_int


class LSUDesc:
    '''Represents the "lsu" field for an instruction in the YAML ISA.

    This has a type (mem-load, mem-store, csr or wsr), a list of operands whose
    values are summed to get the address or index that's loaded and possibly a
    'bytes' value: the number of addresses touched by the operation.

    '''

    TYPES = ['mem-load', 'mem-store', 'csr', 'wsr-load', 'wsr-store']

    def __init__(self,
                 lsu_type: str,
                 target: List[str],
                 idx_width: int) -> None:

        assert lsu_type in LSUDesc.TYPES

        self.lsu_type = lsu_type
        self.target = target
        # idx_width is the number of addresses/indices touched by the
        # operation. For a memory, this is measured in bytes. For a csr/wsr
        # operation, this is always 1 (one register).
        self.idx_width = idx_width

    @staticmethod
    def from_yaml(yml: object, what: str) -> 'LSUDesc':
        yd = check_keys(yml, what, ['type', 'target'], ['bytes'])

        type_what = 'type field for ' + what
        lsu_type = check_str(yd['type'], type_what)
        if lsu_type not in LSUDesc.TYPES:
            raise ValueError('{} is {!r}, but should be one '
                             'of the following: {}.'
                             .format(type_what, lsu_type,
                                     ', '.join(repr(t)
                                               for t in LSUDesc.TYPES)))

        target = yd['target']
        if isinstance(target, str):
            target_parts = [target]
        else:
            target_parts = []
            if not isinstance(target, list):
                raise ValueError('target field for {} should be a string or a '
                                 'list of strings, but actually has type {}.'
                                 .format(what, type(target).__name__))
            for idx, part in enumerate(target):
                elt_what = ('element {} of the target list for {}'
                            .format(idx, what))
                target_parts.append(check_str(part, elt_what))

        if lsu_type.startswith('mem-'):
            if 'bytes' not in yd:
                raise ValueError('{} defines a memory operation, so requires '
                                 'a bytes field (how many bytes does this touch?)'
                                 .format(what))
            idx_width = check_int(yd['bytes'], 'bytes field for ' + what)
        else:
            if 'bytes' in yd:
                raise ValueError("{} isn't a memory operation, so cannot have "
                                 "a bytes field."
                                 .format(what))
            idx_width = 1

        return LSUDesc(lsu_type, target_parts, idx_width)
