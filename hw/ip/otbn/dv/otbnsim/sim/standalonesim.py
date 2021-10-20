# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from .sim import OTBNSim

_TEST_RND_DATA = \
    0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999


class StandaloneSim(OTBNSim):
    def run(self, verbose: bool) -> int:
        '''Run until ECALL.

        Return the number of cycles taken.

        '''
        insn_count = 0
        # ISS will stall at start until URND data is valid; immediately set it
        # valid when in free running mode as nothing else will.
        self.state.set_urnd_reseed_complete()
        while self.state.running():
            self.step(verbose)
            insn_count += 1

            if self.state.wsrs.RND.pending_request:
                # If an instruction requests RND data, make it available
                # immediately.
                self.state.wsrs.RND.set_unsigned(_TEST_RND_DATA)

        return insn_count
