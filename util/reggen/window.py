# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict

from .access import SWAccess
from .lib import check_keys, check_str, check_bool, check_int
from .params import ReggenParams


REQUIRED_FIELDS = {
    'name': ['s', "name of the window"],
    'desc': ['t', "description of the window"],
    'items': ['d', "size in fieldaccess width words of the window"],
    'swaccess': ['s', "software access permitted"],
}

# TODO potential for additional optional to give more type info?
# eg sram-hw-port: "none", "sync", "async"
OPTIONAL_FIELDS = {
    'data-intg-passthru': [
        's', "True if the window has data integrity pass through. "
        "Defaults to false if not present."
    ],
    'byte-write': [
        's', "True if byte writes are supported. "
        "Defaults to false if not present."
    ],
    'validbits': [
        'd', "Number of valid data bits within "
        "regwidth sized word. "
        "Defaults to regwidth. If "
        "smaller than the regwidth then in each "
        "word of the window bits "
        "[regwidth-1:validbits] are unused and "
        "bits [validbits-1:0] are valid."
    ],
    'unusual': [
        's', "True if window has unusual parameters "
        "(set to prevent Unusual: errors)."
        "Defaults to false if not present."
    ]
}


class Window:
    '''A class representing a memory window'''
    def __init__(self,
                 name: str,
                 desc: str,
                 unusual: bool,
                 byte_write: bool,
                 data_intg_passthru: bool,
                 validbits: int,
                 items: int,
                 size_in_bytes: int,
                 offset: int,
                 swaccess: SWAccess):
        assert 0 < validbits
        assert 0 < items <= size_in_bytes

        self.name = name
        self.desc = desc
        self.unusual = unusual
        self.byte_write = byte_write
        self.data_intg_passthru = data_intg_passthru
        self.validbits = validbits
        self.items = items
        self.size_in_bytes = size_in_bytes
        self.offset = offset
        self.swaccess = swaccess

        # Check that offset has been adjusted so that the first item in the
        # window has all zeros in the low bits.
        po2_size = 1 << (self.size_in_bytes - 1).bit_length()
        assert not (offset & (po2_size - 1))

    @staticmethod
    def from_raw(offset: int,
                 reg_width: int,
                 params: ReggenParams,
                 raw: object) -> 'Window':
        rd = check_keys(raw, 'window',
                        list(REQUIRED_FIELDS.keys()),
                        list(OPTIONAL_FIELDS.keys()))

        wind_desc = 'window at offset {:#x}'.format(offset)
        name = check_str(rd['name'], wind_desc)
        wind_desc = '{!r} {}'.format(name, wind_desc)

        desc = check_str(rd['desc'], 'desc field for ' + wind_desc)

        unusual = check_bool(rd.get('unusual', False),
                             'unusual field for ' + wind_desc)
        byte_write = check_bool(rd.get('byte-write', False),
                                'byte-write field for ' + wind_desc)
        data_intg_passthru = check_bool(rd.get('data-intg-passthru', False),
                                        'data-intg-passthru field for ' + wind_desc)

        validbits = check_int(rd.get('validbits', reg_width),
                              'validbits field for ' + wind_desc)
        if validbits <= 0:
            raise ValueError('validbits field for {} is not positive.'
                             .format(wind_desc))
        if validbits > reg_width:
            raise ValueError('validbits field for {} is {}, '
                             'which is greater than {}, the register width.'
                             .format(wind_desc, validbits, reg_width))

        r_items = check_str(rd['items'], 'items field for ' + wind_desc)
        items = params.expand(r_items, 'items field for ' + wind_desc)
        if items <= 0:
            raise ValueError("Items field for {} is {}, "
                             "which isn't positive."
                             .format(wind_desc, items))

        assert reg_width % 8 == 0
        size_in_bytes = items * (reg_width // 8)

        # Round size_in_bytes up to the next power of 2. The calculation is
        # like clog2 calculations in SystemVerilog, where we start with the
        # last index, rather than the number of elements.
        assert size_in_bytes > 0
        po2_size = 1 << (size_in_bytes - 1).bit_length()

        # A size that isn't a power of 2 is not allowed unless the unusual flag
        # is set.
        if po2_size != size_in_bytes and not unusual:
            raise ValueError('Items field for {} is {}, which gives a size of '
                             '{} bytes. This is not a power of 2 (next power '
                             'of 2 is {}). If you want to do this even so, '
                             'set the "unusual" flag.'
                             .format(wind_desc, items,
                                     size_in_bytes, po2_size))

        # Adjust offset if necessary to make sure the base address of the first
        # item in the window has all zeros in the low bits.
        addr_mask = po2_size - 1
        if offset & addr_mask:
            offset = (offset | addr_mask) + 1
        offset = offset

        swaccess = SWAccess(wind_desc, rd['swaccess'])
        if not (swaccess.value[4] or unusual):
            raise ValueError('swaccess field for {} is {}, which is an '
                             'unusual access type for a window. If you want '
                             'to do this, set the "unusual" flag.'
                             .format(wind_desc, swaccess.key))

        return Window(name, desc, unusual, byte_write, data_intg_passthru,
                      validbits, items, size_in_bytes, offset, swaccess)

    def next_offset(self, addrsep: int) -> int:
        return self.offset + self.size_in_bytes

    def _asdict(self) -> Dict[str, object]:
        rd = {
            'desc': self.desc,
            'items': self.items,
            'swaccess': self.swaccess.key,
            'byte-write': self.byte_write,
            'validbits': self.validbits,
            'unusual': self.unusual
        }
        if self.name is not None:
            rd['name'] = self.name

        return {'window': rd}
