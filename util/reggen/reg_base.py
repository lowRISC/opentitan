# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional

from reggen.clocking import ClockingItem
from reggen.field import Field


class RegBase:
    '''An abstract class inherited by Register and MultiRegister

    This represents a block of one or more registers with a base address.

    Instance variables:

      name       The name of the register/multiregister

      offset     The offset or address of the register. For a MultiRegister,
                 this gives the address of the first concrete register in the
                 expansion.

      async_name The name of an asynchronous clock used for the data backing
                 the register/multiregister.

      async_clk  The clocking item named by async_name

      sync_name  The name of a synchronous clock used for the data backing the
                 register/multiregister. Unlike an asynchronous clock, there is
                 no CDC needed between the main clock and the clock used by the
                 register.

      sync_clk   The clocking item named by sync_name

      alias_target The name of an analogous register/multiregister that we are
                   going to override. This is used when building closed source
                   components which override a generic register/multiregister
                   implementation with extra fields/flags etc.
    '''

    def __init__(self,
                 name: str,
                 offset: int,
                 async_name: Optional[str], async_clk: Optional[ClockingItem],
                 sync_name: Optional[str], sync_clk: Optional[ClockingItem],
                 alias_target: Optional[str]):
        self.name = name
        self.offset = offset

        self.async_name = async_name
        self.async_clk = async_clk
        self.sync_name = sync_name
        self.sync_clk = sync_clk

        self.alias_target = alias_target

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
