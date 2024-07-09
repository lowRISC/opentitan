# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from itertools import cycle
from typing import Optional, TextIO
from .sim import OTBNSim
from .state import FsmState

_TEST_RND_DATA = cycle([
    0xAAAAAAAA_99999999_AAAAAAAA_99999999_AAAAAAAA_99999999_AAAAAAAA_99999999,
    0xCCCCCCCC_BBBBBBBB_CCCCCCCC_BBBBBBBB_CCCCCCCC_BBBBBBBB_CCCCCCCC_BBBBBBBB,
])


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

        # Skip the initial secure wipe
        self.state.complete_init_sec_wipe()

        while True:
            # If there's a RND request, respond immediately
            if self.state.ext_regs.read('RND_REQ', True):
                self.state.wsrs.RND.set_unsigned(next(_TEST_RND_DATA), False,
                                                 False)
            # If there's a URND request, respond immediately.
            if not self.state.wsrs.URND.running:
                self.state.wsrs.URND.set_seed(_TEST_URND_DATA)

            # Similarly, if URND is not running, provide it with some arbitrary
            # seed.
            if not self.state.wsrs.URND.running:
                self.state.wsrs.URND.set_seed(_TEST_URND_DATA)

            self.step(verbose)
            insn_count += 1

            # Dump registers on the first wipe cycle. This makes sure that we
            # dump them before zeroing.
            if self.state.get_fsm_state() in [FsmState.IDLE, FsmState.LOCKED]:
                if dump_file is not None:
                    self.dump_regs(dump_file)
                break

        return insn_count

    def dump_regs(self, tgt: TextIO) -> None:
        for reg in ['ERR_BITS', 'INSN_CNT', 'STOP_PC']:
            value = self.state.ext_regs.read(reg, False)
            tgt.write(' {} = 0x{:08x}\n'.format(reg, value))
        for idx, value in enumerate(self.state.gprs.peek_unsigned_values()):
            tgt.write(' x{:<2} = 0x{:08x}\n'.format(idx, value))
        for idx, value in enumerate(self.state.wdrs.peek_unsigned_values()):
            tgt.write(' w{:<2} = 0x{:064x}\n'.format(idx, value))
