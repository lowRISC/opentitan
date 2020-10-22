# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from typing import Dict, Tuple, Union

from .bool_literal import BoolLiteral
from .encoding_scheme import EncSchemeField, EncSchemes
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
                  what: str) -> 'EncodingField':
        # The value should either be a boolean literal ("000xx11" or similar)
        # or should be a name, which is taken as the name of an operand.
        if not as_str:
            raise ValueError('Empty string as {}.'.format(what))

        # Set self.value to be either the bool literal or the name of the
        # operand.
        value = ''  # type: Union[BoolLiteral, str]
        if re.match(r'b[01x_]+$', as_str):
            value = BoolLiteral.from_string(as_str, what)

            # Check that the literal operand value matches the width of the
            # schema field.
            if scheme_field.bits.width != value.width:
                raise ValueError('{} is mapped to a literal value with width '
                                 '{}, but the encoding schema field has '
                                 'width {}.'
                                 .format(what, value.width,
                                         scheme_field.bits.width))
        else:
            value = as_str

        # Track the scheme field as well (so we don't have to keep track of a
        # scheme once we've made an encoding object)
        return EncodingField(value, scheme_field)


class Encoding:
    '''The encoding for an instruction'''
    def __init__(self,
                 yml: object,
                 schemes: EncSchemes,
                 mnemonic: str):
        what = 'encoding for instruction {!r}'.format(mnemonic)
        yd = check_keys(yml, what, ['scheme', 'mapping'], [])

        scheme_what = 'encoding scheme for instruction {!r}'.format(mnemonic)
        scheme_name = check_str(yd['scheme'], scheme_what)
        scheme_fields = schemes.resolve(scheme_name, mnemonic)

        what = 'encoding mapping for instruction {!r}'.format(mnemonic)

        # Check we've got exactly the right fields for the scheme
        ydm = check_keys(yd['mapping'], what, list(scheme_fields.op_fields), [])

        # Build a map from operand name to the name of a field that uses it.
        self.op_to_field_name = {}  # type: Dict[str, str]

        self.fields = {}
        for field_name, scheme_field in scheme_fields.fields.items():
            if scheme_field.value is not None:
                field = EncodingField(scheme_field.value, scheme_field)
            else:
                field_what = ('value for {} field in '
                              'encoding for instruction {!r}'
                              .format(field_name, mnemonic))
                ef_val = check_str(ydm[field_name], field_what)
                field = EncodingField.from_yaml(ef_val,
                                                scheme_fields.fields[field_name],
                                                field_what)

                # If the field's value has type str, the field uses an operand
                # rather than a literal. Check for linearity and store the
                # mapping.
                if isinstance(field.value, str):
                    other_field_name = self.op_to_field_name.get(field.value)
                    if other_field_name is not None:
                        raise ValueError('Non-linear use of operand with name '
                                         '{!r} in encoding for instruction '
                                         '{!r}: used in fields {!r} and {!r}.'
                                         .format(field.value, mnemonic,
                                                 other_field_name,
                                                 field_name))
                    self.op_to_field_name[field.value] = field_name

            self.fields[field_name] = field

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

            # The encoding process should already have converted anything
            # negative to a 2's complement representation.
            assert field_val >= 0

            # Is the number too big? At the moment, we are assuming immediates
            # are unsigned (because the OTBN big number instructions all have
            # unsigned immediates).
            if field_val >> field.scheme_field.bits.width:
                raise ValueError("operand field {} has a width of {}, "
                                 "so can't represent the value {:#x}."
                                 .format(field.value,
                                         field.scheme_field.bits.width,
                                         field_val))

            val |= field.scheme_field.bits.encode(field_val)

        return val

    def extract_operands(self, word: int) -> Dict[str, int]:
        '''Extract the encoded operand values from an encoded instruction'''
        ret = {}
        for field in self.fields.values():
            # The operand fields (rather than fixed ones) have the operand name as
            # their value.
            if not isinstance(field.value, str):
                continue

            ret[field.value] = field.scheme_field.bits.decode(word)

        return ret
