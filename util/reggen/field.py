# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Optional

from design.mubi import prim_mubi

from reggen.access import SWAccess, HWAccess
from reggen.bits import Bits
from reggen.enum_entry import EnumEntry
from reggen.lib import (check_keys, check_str, check_name, check_bool,
                        check_list, check_str_list, check_xint)
from reggen.params import ReggenParams

REQUIRED_FIELDS = {
    'bits': ['b', "bit or bit range (msb:lsb)"]
}

OPTIONAL_FIELDS = {
    'name': ['s', "name of the field"],
    'desc': [
        't',
        "description of field (required if the field has a name). "
        "This field supports the markdown syntax."
    ],
    'alias_target': [
        's',
        "name of the field to apply the alias definition to."
    ],
    'swaccess': [
        's', "software access permission, copied from "
        "register if not provided in field. "
        "(Tool adds if not provided.)"
    ],
    'hwaccess': [
        's', "hardware access permission, copied from "
        "register if not provided in field. "
        "(Tool adds if not provided.)"
    ],
    'hwqe': [
        'b', "'true' if hardware uses 'q' enable signal, "
        "which is latched signal of software write pulse. "
        "Copied from register if not provided in field. "
        "(Tool adds if not provided.)"
    ],
    'resval': [
        'x', "reset value, comes from register resval "
        "if not provided in field. Zero if neither "
        "are provided and the field is readable, "
        "x if neither are provided and the field "
        "is wo. Must match if both are provided."
    ],
    'enum': ['l', "list of permitted enumeration groups"],
    'tags': [
        's',
        "tags for the field, followed by the format 'tag_name:item1:item2...'"
    ],
    'mubi': [
        'b',
        "boolean flag for whether the field is a multi-bit type"
    ],
    'auto_split': [
        'b',
        "boolean flag which determines whether the field "
        "should be automatically separated into 1-bit sub-fields."
        "This flag is used as a hint for automatically generated "
        "software headers with register description."
    ]
}


class Field:
    def __init__(self,
                 name: str,
                 alias_target: Optional[str],
                 desc: Optional[str],
                 tags: List[str],
                 swaccess: SWAccess,
                 hwaccess: HWAccess,
                 hwqe: bool,
                 bits: Bits,
                 resval: Optional[int],
                 enum: Optional[List[EnumEntry]],
                 mubi: bool,
                 auto_split: bool):
        self.name = name
        self.alias_target = alias_target
        self.desc = desc
        self.tags = tags
        self.swaccess = swaccess
        self.hwaccess = hwaccess
        self.hwqe = hwqe
        self.bits = bits
        self.resval = resval
        self.enum = enum
        self.mubi = mubi
        self.auto_split = auto_split

    @staticmethod
    def from_raw(reg_name: str,
                 field_idx: int,
                 num_fields: int,
                 default_swaccess: SWAccess,
                 default_hwaccess: HWAccess,
                 reg_resval: Optional[int],
                 reg_width: int,
                 params: ReggenParams,
                 hwext: bool,
                 default_hwqe: bool,
                 shadowed: bool,
                 is_alias: bool,
                 raw: object) -> 'Field':
        where = 'field {} of {} register'.format(field_idx, reg_name)
        rd = check_keys(raw, where,
                        list(REQUIRED_FIELDS.keys()),
                        list(OPTIONAL_FIELDS.keys()))

        raw_name = rd.get('name')
        if raw_name is None:
            name = ('field{}'.format(field_idx + 1)
                    if num_fields > 1 else reg_name)
        else:
            name = check_name(raw_name, 'name of {}'.format(where))

        alias_target = None
        if rd.get('alias_target') is not None:
            if is_alias:
                alias_target = check_name(rd.get('alias_target'),
                                          'name of alias target register')
            else:
                raise ValueError('Field {} may not have an alias_target key.'
                                 .format(name))

        raw_desc = rd.get('desc')
        if raw_desc is None and raw_name is not None:
            raise ValueError('Missing desc field for {}'
                             .format(where))
        if raw_desc is None:
            desc = None
        else:
            desc = check_str(raw_desc, 'desc field for {}'.format(where))

        tags = check_str_list(rd.get('tags', []),
                              'tags for {}'.format(where))

        raw_mubi = rd.get('mubi', False)
        is_mubi = check_bool(raw_mubi, 'mubi field for {}'.format(where))
        raw_swaccess = rd.get('swaccess')
        if raw_swaccess is not None:
            swaccess = SWAccess(where, raw_swaccess, is_mubi)
        else:
            swaccess = default_swaccess
            swaccess.is_mubi = is_mubi

        raw_hwaccess = rd.get('hwaccess')
        if raw_hwaccess is not None:
            hwaccess = HWAccess(where, raw_hwaccess)
        else:
            hwaccess = default_hwaccess

        raw_hwqe = rd.get('hwqe', default_hwqe)
        hwqe = check_bool(raw_hwqe, 'hwqe field for {}'.format(where))
        raw_auto_split = rd.get('auto_split', False)
        is_auto_split = check_bool(raw_auto_split, 'auto_split field for {}'.format(where))

        # Currently internal shadow registers do not support hw write type
        if not hwext and shadowed and hwaccess.allows_write():
            raise ValueError('Internal Shadow registers do not currently support '
                             'hardware write')

        bits = Bits.from_raw(where, reg_width, params, rd['bits'])
        raw_resval = rd.get('resval')
        if is_mubi:
            # When mubi type, the resval supplied is a boolean which is converted
            # to a mubi value
            chk_resval = check_bool(raw_resval, 'resval field for {}'.format(where))

            # Check mubi width is supported
            if not prim_mubi.is_width_valid(bits.width()):
                raise ValueError(f'mubi field for {name} does not support width '
                                 f'of {bits.width()}')

            # Get actual integer value based on mubi selection
            raw_resval = prim_mubi.mubi_value_as_int(chk_resval, bits.width())

        if raw_resval is None:
            # The field doesn't define a reset value. Use bits from reg_resval
            # if it's defined. If not, we assume that a hwext register comes up
            # as "x" (because the reggen code doesn't have any way to predict
            # it). That's represented as None. A non-hwext register is reset to
            # zero.
            if reg_resval is not None:
                resval = bits.extract_field(reg_resval)  # type: Optional[int]
            elif hwext:
                resval = None
            else:
                resval = 0
        else:
            # The field does define a reset value. It should be an integer or
            # 'x'. In the latter case, we set resval to None (as above).
            resval = check_xint(raw_resval, 'resval field for {}'.format(where))
            if resval is None:
                # We don't allow a field to be explicitly 'x' on reset but for
                # the containing register to have a reset value.
                if reg_resval is not None:
                    raise ValueError('resval field for {} is "x", but the '
                                     'register defines a resval as well.'
                                     .format(where))
            else:
                # Check that the reset value is representable with bits
                if not (0 <= resval <= bits.max_value()):
                    raise ValueError("resval field for {} is {}, which "
                                     "isn't representable as an unsigned "
                                     "{}-bit integer."
                                     .format(where, resval, bits.width()))

                # If the register had a resval, check this value matches it.
                if reg_resval is not None:
                    resval_from_reg = bits.extract_field(reg_resval)
                    if resval != resval_from_reg:
                        raise ValueError('resval field for {} is {}, but the '
                                         'register defines a resval as well, '
                                         'where bits {}:{} would give {}.'
                                         .format(where, resval,
                                                 bits.msb, bits.lsb,
                                                 resval_from_reg))

        raw_enum = rd.get('enum')
        if raw_enum is None:
            enum = None
        else:
            enum = []
            raw_entries = check_list(raw_enum,
                                     'enum field for {}'.format(where))
            enum_val_to_name = {}  # type: Dict[int, str]
            for idx, raw_entry in enumerate(raw_entries):
                entry = EnumEntry('entry {} in enum list for {}'
                                  .format(idx + 1, where),
                                  bits.max_value(),
                                  raw_entry)
                if entry.value in enum_val_to_name:
                    raise ValueError('In {}, duplicate enum entries for '
                                     'value {} ({} and {}).'
                                     .format(where,
                                             entry.value,
                                             enum_val_to_name[entry.value],
                                             entry.name))
                enum.append(entry)
                enum_val_to_name[entry.value] = entry.name

        return Field(name, alias_target, desc, tags, swaccess, hwaccess,
                     hwqe, bits, resval, enum, is_mubi, is_auto_split)

    def has_incomplete_enum(self) -> bool:
        return (self.enum is not None and
                len(self.enum) != 1 + self.bits.max_value())

    def get_n_bits(self, hwext: bool, hwre: bool, bittype: List[str]) -> int:
        '''Get the size of this field in bits

        bittype should be a list of the types of signals to count. The elements
        should come from the following list:

        - 'q': A signal for the value of the field. Only needed if HW can read
          its contents.

        - 'd': A signal for the next value of the field. Only needed if HW can
          write its contents.

        - 'de': A write enable signal for hardware accesses. Only needed if HW
          can write the field's contents and the register data is stored in the
          register block (true if the hwext flag is false).

        '''
        n_bits = 0
        if "q" in bittype and self.hwaccess.allows_read():
            n_bits += self.bits.width()
        if "d" in bittype and self.hwaccess.allows_write():
            n_bits += self.bits.width()
        if "qe" in bittype and self.hwaccess.allows_read():
            n_bits += int(self.hwqe)
        if "re" in bittype and self.hwaccess.allows_read():
            n_bits += int(hwre)
        if "de" in bittype and self.hwaccess.allows_write():
            n_bits += int(not hwext)
        return n_bits

    def make_multi(self,
                   reg_width: int,
                   min_reg_idx: int,
                   max_reg_idx: int,
                   cname: str,
                   creg_idx: int,
                   stripped: bool) -> List['Field']:
        assert 0 <= min_reg_idx <= max_reg_idx

        # Check that we won't overflow reg_width. We assume that the LSB should
        # be preserved: if msb=5, lsb=2 then the replicated copies will be
        # [5:2], [11:8] etc.
        num_copies = 1 + max_reg_idx - min_reg_idx
        field_width = self.bits.msb + 1

        if field_width * num_copies > reg_width:
            raise ValueError('Cannot replicate field {} {} times: the '
                             'resulting width would be {}, but the register '
                             'width is just {}.'
                             .format(self.name, num_copies,
                                     field_width * num_copies, reg_width))

        desc = ('For {}{}'.format(cname, creg_idx)
                if stripped else self.desc)
        enum = None if stripped else self.enum

        ret = []
        for reg_idx in range(min_reg_idx, max_reg_idx + 1):
            name = '{}_{}'.format(self.name, reg_idx)
            # In case this is an alias register, we need to make sure that
            # the alias_target name is expanded as well.
            alias_target = None
            if self.alias_target is not None:
                alias_target = '{}_{}'.format(self.alias_target, reg_idx)

            bit_offset = field_width * (reg_idx - min_reg_idx)
            bits = (self.bits
                    if bit_offset == 0
                    else self.bits.make_translated(bit_offset))

            ret.append(Field(name, alias_target, desc,
                             self.tags, self.swaccess, self.hwaccess, self.hwqe,
                             bits, self.resval, enum, self.mubi, self.auto_split))

        return ret

    def make_suffixed(self, suffix: str,
                      cname: str,
                      creg_idx: int,
                      stripped: bool) -> 'Field':
        desc = ('For {}{}'.format(cname, creg_idx)
                if stripped else self.desc)
        enum = None if stripped else self.enum

        alias_target = None
        if self.alias_target is not None:
            alias_target = self.alias_target + suffix

        return Field(self.name + suffix, alias_target,
                     desc, self.tags, self.swaccess, self.hwaccess, self.hwqe,
                     self.bits, self.resval, enum, self.mubi, self.auto_split)

    def _asdict(self) -> Dict[str, object]:
        rd = {
            'bits': self.bits.as_str(),
            'name': self.name,
            'swaccess': self.swaccess.key,
            'hwaccess': self.hwaccess.key,
            'resval': 'x' if self.resval is None else str(self.resval),
            'tags': self.tags
        }  # type: Dict[str, object]

        if self.desc is not None:
            rd['desc'] = self.desc
        if self.enum is not None:
            rd['enum'] = self.enum
        if self.alias_target is not None:
            rd['alias_target'] = self.alias_target
        return rd

    def sw_readable(self) -> bool:
        return self.swaccess.key not in ['wo', 'r0w1c']

    def sw_writable(self) -> bool:
        return self.swaccess.key != 'ro'

    def apply_alias(self, alias_field: 'Field', where: str) -> None:
        '''Compare all attributes and replace overridable values.

        This updates the overridable field attributes with the alias values and
        ensures that all non-overridable attributes have identical values.
        '''

        # Attributes to be crosschecked
        attrs = ['bits', 'swaccess', 'hwaccess', 'hwqe', 'mubi']
        for attr in attrs:
            if getattr(self, attr) != getattr(alias_field, attr):
                raise ValueError('Value mismatch for attribute {} between '
                                 'alias field {} and field {} in {}.'
                                 .format(attr, self.name,
                                         alias_field.name, where))

        # These attributes can be overridden by the aliasing mechanism.
        self.name = alias_field.name
        self.desc = alias_field.desc
        self.enum = alias_field.enum
        self.resval = alias_field.resval
        self.tags = alias_field.tags
        # We also keep track of the alias_target when overriding attributes.
        # This gives us a way to check whether a register has been overridden
        # or not, and what the name of the original register was.
        self.alias_target = alias_field.alias_target

    def scrub_alias(self, where: str) -> None:
        '''Replaces sensitive fields in field with generic names

        This function can be used to create the generic field descriptions
        from full alias hjson definitions.
        '''
        # These attributes are scrubbed. Note that the name is scrubbed in
        # register.py already.
        self.desc = ''
        self.enum = []
        self.resval = 0
        self.tags = []
        self.alias_target = None
