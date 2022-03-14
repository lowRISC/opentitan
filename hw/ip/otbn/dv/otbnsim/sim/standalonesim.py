# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional, TextIO
from .sim import OTBNSim

_TEST_RND_DATA = \
    0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999

# This is the default seed for URND PRNG. Note that the actualy URND value will
# be random since we are modelling PRNG inside the URND register model.
_TEST_URND_DATA = [
    0x84ddfadaf7e1134d, 0x70aa1c59de6197ff,
    0x25a4fe335d095f1e, 0x2cba89acbe4a07e9
]


class StandaloneSim(OTBNSim):
    def run(self, verbose: bool, dump_file: Optional[TextIO]) -> int:
        '''Run until ECALL.

        Return the number of cycles taken.

        '''
        insn_count = 0
        # ISS will stall at start until URND data is valid; immediately set it
        # valid when in free running mode as nothing else will.
        self.state.wsrs.URND.set_seed(_TEST_URND_DATA)
        while self.state.executing():
            self.step(verbose)
            insn_count += 1

            # If an instruction requests RND data, make it available
            # immediately.
            if self.state.wsrs.RND.pending_request:
                self.state.wsrs.RND.set_unsigned(_TEST_RND_DATA)

            # Dump registers on the first wipe cycle. This makes sure that we
            # dump them before zeroing.
            if dump_file is not None and self.state.wiping():
                self.dump_regs(dump_file)
                dump_file = None

        return insn_count

    def dump_regs(self, tgt: TextIO) -> None:
        for idx, value in enumerate(self.state.gprs.peek_unsigned_values()):
            tgt.write(' x{:<2} = 0x{:08x}\n'.format(idx, value))
        for idx, value in enumerate(self.state.wdrs.peek_unsigned_values()):
            tgt.write(' w{:<2} = 0x{:064x}\n'.format(idx, value))
