# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from typing import Dict, Tuple, Union

from .bool_literal import BoolLiteral
from .encoding_scheme import EncSchemeField, EncSchemes
from .operand import Operand
from .yaml_parse_helpers import check_keys, check_str


class EncodingField:
    '''A single element of an encoding's mapping'''
    def __init__(self,
                 value: Union[BoolLiteral, str],
                 scheme_field: EncSchemeField) -> None:
        self.value = value
        self.scheme_field = scheme_field

    @staticmethod
    def from_yaml(as_str: str,
                  scheme_field: EncSchemeField,
                  name_to_operand: Dict[str, Operand],
                  what: str) -> 'EncodingField':
        # The value should either be a boolean literal ("000xx11" or similar)
        # or should be a name, which is taken as the name of an operand.
        if not as_str:
            raise ValueError('Empty string as {}.'.format(what))

        # Set self.value to be either the bool literal or the name of the
        # operand.
        value_width = None
        value = ''  # type: Union[BoolLiteral, str]
        if re.match(r'b[01x_]+$', as_str):
            value = BoolLiteral.from_string(as_str, what)
            value_width = value.width
            value_type = 'a literal value'
        else:
            operand = name_to_operand.get(as_str)
            if operand is None:
                raise ValueError('Unknown operand, {!r}, as {}'
                                 .format(as_str, what))
            value_width = operand.op_type.width
            value = as_str
            value_type = 'an operand'

        # Unless we had an operand of type 'imm' (unknown width), we now have
        # an expected width. Check it matches the width of the schema field.
        if value_width is not None:
            if scheme_field.bits.width != value_width:
                raise ValueError('{} is mapped to {} with width {}, but the '
                                 'encoding schema field has width {}.'
                                 .format(what, value_type, value_width,
                                         scheme_field.bits.width))

        # Track the scheme field as well (so we don't have to keep track of a
        # scheme once we've made an encoding object)
        return EncodingField(value, scheme_field)


class Encoding:
    '''The encoding for an instruction'''
    def __init__(self,
                 yml: object,
                 schemes: EncSchemes,
                 name_to_operand: Dict[str, Operand],
                 mnemonic: str):
        what = 'encoding for instruction {!r}'.format(mnemonic)
        yd = check_keys(yml, what, ['scheme', 'mapping'], [])

        scheme_what = 'encoding scheme for instruction {!r}'.format(mnemonic)
        scheme_name = check_str(yd['scheme'], scheme_what)
        scheme_fields = schemes.resolve(scheme_name, mnemonic)

        what = 'encoding mapping for instruction {!r}'.format(mnemonic)

        # Check we've got exactly the right fields for the scheme
        ydm = check_keys(yd['mapping'], what, list(scheme_fields.op_fields), [])

        # Track the set of operand names that were used in some field
        operands_used = set()

        self.fields = {}
        for field_name, scheme_field in scheme_fields.fields.items():
            if scheme_field.value is not None:
                field = EncodingField(scheme_field.value, scheme_field)
            else:
                field_what = ('value for {} field in encoding for instruction {!r}'
                              .format(field_name, mnemonic))
                field = EncodingField.from_yaml(check_str(ydm[field_name], field_what),
                                                scheme_fields.fields[field_name],
                                                name_to_operand,
                                                field_what)

                # If the field's value is an operand rather than a literal, it
                # will have type str. Track the operands that we've used.
                if isinstance(field.value, str):
                    operands_used.add(field.value)

            self.fields[field_name] = field

        # We know that every field in the encoding scheme has a value. But we
        # still need to check that every operand ended up in some field.
        assert operands_used <= set(name_to_operand.keys())
        unused_ops = set(name_to_operand.keys()) - operands_used
        if unused_ops:
            raise ValueError('Not all operands used in {} (missing: {}).'
                             .format(what, ', '.join(list(unused_ops))))

    def get_masks(self) -> Tuple[int, int]:
        '''Return zeros/ones masks for encoding

        Returns a pair (m0, m1) where m0 is the "zeros mask": a mask where a
        bit is set if there is an bit pattern matching this encoding with that
        bit zero. m1 is the ones mask: equivalent, but for that bit one.

        '''
        m0 = 0
        m1 = 0
        for field_name, field in self.fields.items():
            if isinstance(field.value, str):
                m0 |= field.scheme_field.bits.mask
                m1 |= field.scheme_field.bits.mask
            else:
                # Match up the bits in the value with the ranges in the scheme.
                assert field.value.width > 0
                assert field.value.width == field.scheme_field.bits.width
                bits_seen = 0
                for msb, lsb in field.scheme_field.bits.ranges:
                    val_msb = field.scheme_field.bits.width - 1 - bits_seen
                    val_lsb = val_msb - msb + lsb
                    bits_seen += msb - lsb + 1

                    for idx in range(0, msb - lsb + 1):
                        desc = field.value.char_for_bit(val_lsb + idx)
                        if desc in ['0', 'x']:
                            m0 |= 1 << (idx + lsb)
                        if desc in ['1', 'x']:
                            m1 |= 1 << (idx + lsb)

        all_bits = (1 << 32) - 1
        assert (m0 | m1) == all_bits
        return (m0, m1)

    def get_ones_mask(self) -> int:
        '''Return the mask of fixed bits that are set

        For literal values of x (unused bits in the encoding), we'll prefer
        '0'.

        '''
        m0, m1 = self.get_masks()
        return m1 & ~m0

    def assemble(self, op_to_idx: Dict[str, int]) -> int:
        '''Assemble an instruction

        op_to_idx should map each operand in the encoding to some integer
        index, which should be small enough to fit in the width of the
        operand's type and should be representable after any shift. Will raise
        a ValueError if not.

        '''
        val = self.get_ones_mask()
        for field_name, field in self.fields.items():
            if not isinstance(field.value, str):
                # We've done this field already (in get_ones_mask)
                continue

            # Try to get the operand value for the field. If this is an
            # optional operand, we might not have one, and just encode zero.
            field_val = op_to_idx.get(field.value, 0)

            # Are there any low bits that shouldn't be there?
            shift_mask = (1 << field.scheme_field.shift) - 1
            if field_val & shift_mask:
                raise ValueError("operand field {} has a shift of {}, "
                                 "so can't represent the value {:#x}."
                                 .format(field.value,
                                         field.scheme_field.shift,
                                         field_val))

            shifted = field_val >> field.scheme_field.shift

            # Is the number too big? At the moment, we are assuming immediates
            # are unsigned (because the OTBN big number instructions all have
            # unsigned immediates).
            if shifted >> field.scheme_field.bits.width:
                shift_msg = ((' (shifted right by {} bits from {:#x})'
                              .format(field.scheme_field.shift, field_val))
                             if field.scheme_field.shift
                             else '')
                raise ValueError("operand field {} has a width of {}, "
                                 "so can't represent the value {:#x}{}."
                                 .format(field.value,
                                         field.scheme_field.bits.width,
                                         shifted, shift_msg))

            val |= field.scheme_field.bits.encode(shifted)

        return val
