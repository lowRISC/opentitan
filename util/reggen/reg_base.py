# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List

from .field import Field


class RegBase:
    '''An abstract class inherited by Register and MultiRegister

    This represents a block of one or more registers with a base address.

    '''
    def __init__(self, offset: int):
        self.offset = offset

    def get_n_bits(self, bittype: List[str]) -> int:
        '''Get the size of this register / these registers in bits

        See Field.get_n_bits() for the precise meaning of bittype.

        '''
        raise NotImplementedError()

    def get_field_list(self) -> List[Field]:
        '''Get an ordered list of the fields in the register(s)

        Registers are ordered from low to high address. Within a register,
        fields are ordered as Register.fields: from LSB to MSB.

        '''
        raise NotImplementedError()

    def is_homogeneous(self) -> bool:
        '''True if every field in the block is identical

        For a single register, this is true if it only has one field. For a
        multireg, it is true if the generating register has just one field.
        Note that if the compact flag is set, the generated registers might
        have multiple (replicated) fields.

        '''
        raise NotImplementedError()
