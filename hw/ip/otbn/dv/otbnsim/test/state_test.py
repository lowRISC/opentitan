# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Test the implementation of OTBNState.'''

import py

from sim.constants import ErrBits, Status
from testutil import prepare_sim_for_asm_str


def test_ext_regs_success(tmpdir: py.path.local) -> None:
    '''Check the contents of the external registers after a successful run.'''

    simple_asm = """
    nop
    ecall
    """

    sim = prepare_sim_for_asm_str(simple_asm, tmpdir, False)
    sim.run(verbose=False)

    assert sim.state.ext_regs.read('ERR_BITS', False) == 0
    assert sim.state.ext_regs.read('FATAL_ALERT_CAUSE', False) == 0

    # The CMD register is write-only from software.
    assert sim.state.ext_regs.read('CMD', from_hw=True) == 0

    # Only INTR_STATE.done is set
    assert sim.state.ext_regs.read('INTR_STATE', False) == (1 << 0)

    # STATUS must be IDLE
    assert sim.state.ext_regs.read('STATUS', False) == Status.IDLE


def test_ext_regs_err_bits_bad(tmpdir: py.path.local) -> None:
    '''Test an invalid instruction is reflected in ERR_BITS.'''

    invalid_jump_asm = """
    jal x0, 10
    ecall
    """

    sim = prepare_sim_for_asm_str(invalid_jump_asm, tmpdir, False)
    sim.run(verbose=False)

    assert sim.state.ext_regs.read('ERR_BITS', False) == ErrBits.BAD_INSN_ADDR

    assert sim.state.ext_regs.read('FATAL_ALERT_CAUSE', False) == 0
