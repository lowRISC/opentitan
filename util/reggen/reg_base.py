# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from dataclasses import dataclass

from reggen.clocking import ClockingItem
from reggen.field import Field


@dataclass
class RegBase:
    '''An abstract class inherited by Register and MultiRegister

    This represents a block of one or more registers with a base address.
    '''
    name: str
    '''The name of the register/multiregister'''

    offset: int
    '''The offset or address of the register. For a MultiRegister, this gives
    the address of the first concrete register in the expansion.'''

    async_clk: tuple[str, ClockingItem] | None
    '''An optional asynchronous clock used for the data backing the
    register/multiregister.'''

    sync_clk: tuple[str, ClockingItem] | None
    '''An optional asynchronous clock used for the data backing the
    register/multiregister. Unlike an asynchronous clock, there is no CDC
    needed between the main clock and the clock used by the register.'''

    alias_target: str | None
    '''The name of an analogous register/multiregister that we are going to
    override. This is used when building closed source components which
    override a generic register/multiregister implementation with extra
    fields/flags etc.'''

    def __hash__(self) -> int:
        return hash((self.offset, self.name))

    def get_n_bits(self, bittype: list[str]) -> int:
        '''Get the size of this register / these registers in bits

        See Field.get_n_bits() for the precise meaning of bittype.

        '''
        raise NotImplementedError()

    def get_field_list(self) -> list[Field]:
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
