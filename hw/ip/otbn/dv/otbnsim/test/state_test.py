# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Test the implementation of OTBNState.'''

import py

import sim.err_bits as err_bits
from testutil import prepare_sim_for_asm_str


def test_ext_regs_success(tmpdir: py.path.local) -> None:
    '''Check the contents of the external registers after a successful run.'''

    simple_asm = """
    nop
    ecall
    """

    sim = prepare_sim_for_asm_str(simple_asm, tmpdir, start_addr=4)
    sim.run(verbose=False, collect_stats=False)

    assert sim.state.ext_regs.read('ERR_BITS', False) == 0
    assert sim.state.ext_regs.read('FATAL_ALERT_CAUSE', False) == 0

    # The CMD register only contains the start field, which is write-only.
    assert sim.state.ext_regs.read('CMD', False) == 0

    # Only INTR_STATE.done is set
    assert sim.state.ext_regs.read('INTR_STATE', False) == (1 << 0)

    # STATUS.busy (the only field in this register) must be zero.
    assert sim.state.ext_regs.read('STATUS', False) == 0

    # START_ADDR should reflect the start address that was last written there
    # when the simulation was started.
    # START_ADDR is write-only from software; only reads from hardware reveal
    # the actual value.
    assert sim.state.ext_regs.read('START_ADDR', from_hw=True) == 4


def test_ext_regs_err_bits_bad(tmpdir: py.path.local) -> None:
    '''Test an invalid instruction is reflected in ERR_BITS.'''

    invalid_jump_asm = """
    jal x0, 10
    ecall
    """

    sim = prepare_sim_for_asm_str(invalid_jump_asm, tmpdir, start_addr=0)
    sim.run(verbose=False, collect_stats=False)

    assert sim.state.ext_regs.read('ERR_BITS', False) == err_bits.BAD_INSN_ADDR

    assert sim.state.ext_regs.read('FATAL_ALERT_CAUSE', False) == 0
