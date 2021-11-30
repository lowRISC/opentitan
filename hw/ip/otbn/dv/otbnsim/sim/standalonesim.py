# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from .sim import OTBNSim

_TEST_RND_DATA = \
    0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999

# This is the default seed for URND PRNG. Note that the actualy URND value will
# be random since we are modelling PRNG inside the URND register model.
_TEST_URND_DATA = \
    [0x84ddfadaf7e1134d, 0x70aa1c59de6197ff, 0x25a4fe335d095f1e, 0x2cba89acbe4a07e9]


class StandaloneSim(OTBNSim):
    def run(self, verbose: bool) -> int:
        '''Run until ECALL.

        Return the number of cycles taken.

        '''
        insn_count = 0
        # ISS will stall at start until URND data is valid; immediately set it
        # valid when in free running mode as nothing else will.
        self.state.wsrs.URND.set_seed(_TEST_URND_DATA)
        while self.state.running():
            self.step(verbose)
            insn_count += 1

            if self.state.wsrs.RND.pending_request:
                # If an instruction requests RND data, make it available
                # immediately.
                self.state.wsrs.RND.set_unsigned(_TEST_RND_DATA)

        return insn_count
