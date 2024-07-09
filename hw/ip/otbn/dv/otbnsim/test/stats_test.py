# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import py
import os

from sim.standalonesim import StandaloneSim
from sim.stats import ExecutionStats
import testutil


def _run_sim_for_stats(sim: StandaloneSim) -> ExecutionStats:
    sim.run(verbose=False, dump_file=None)

    # Ensure that the execution was successful.
    assert sim.state.ext_regs.read('ERR_BITS', False) == 0

    assert sim.stats
    return sim.stats


def _simulate_asm_file(asm_file: str, tmpdir: py.path.local) -> ExecutionStats:
    '''Run the OTBN simulator, collect statistics, and return them.'''

    sim = testutil.prepare_sim_for_asm_file(asm_file, tmpdir, True)
    return _run_sim_for_stats(sim)


def _simulate_asm_str(assembly: str, tmpdir: py.path.local) -> ExecutionStats:
    sim = testutil.prepare_sim_for_asm_str(assembly, tmpdir, True)
    return _run_sim_for_stats(sim)


def test_basic_block_stats(tmpdir: py.path.local) -> None:
    '''Check if statistics for basic blocks are calculated correctly.'''

    asm = """
    jump:
      /* A basic block of 4 instructions, ending with a jump. */
      addi x7, x7, 1
      addi x7, x7, 2
      addi x7, x7, 3
      jal x0, branch1

    nop /* Should never be executed. */

    branch1:
      /* A basic block of 3 instructions, ending with a branch. */
      addi x7, x7, 4
      addi x7, x7, -10
      beq x7, x0, branch2

    branch2:
      /* A basic block of 3 instructions, ending with a branch. */
      addi x7, x7, 4
      addi x7, x7, -4
      beq x7, x0, exit

    nop /* Should never be executed. */

    exit:
      ecall
    """

    stats = _simulate_asm_str(asm, tmpdir)

    assert stats.get_insn_count() == 11
    assert sorted(stats.basic_block_histo) == sorted({
        4: 1,  # 1 basic block with 4 instructions (jump)
        3: 2,  # 2 basic blocks with 3 instructions (branch1 and branch2)
        1: 1   # 1 basic block with 1 instruction (exit)
    })

    assert sorted(stats.ext_basic_block_histo) == sorted({
        7: 1,  # 1 ext. basic block with 7 instructions (jump + branch1)
        3: 2,  # 1 ext. basic block with 3 instructions (branch2)
        1: 1   # 1 ext. basic block with 1 instruction (exit)
    })


def test_basic_block_stats_loop(tmpdir: py.path.local) -> None:
    '''Check if statistics for basic blocks LOOPs are calculated properly.'''

    asm = """
    /* Loop x7 == 3 times over a body of 2 instructions. */
    addi x7, x0, 3
    loop x7, 2
      nop
      nop
    ecall
    """

    stats = _simulate_asm_str(asm, tmpdir)

    assert stats.get_insn_count() == 9
    assert sorted(stats.basic_block_histo) == sorted({
        4: 1,  # 1 basic block with 4 instructions (addi + loop + 2x nop)
        2: 1,  # 1 basic block with 2 instructions (loop body on second iter.)
        1: 1   # 1 basic block with 1 instruction (ecall)
    })

    assert (sorted(stats.ext_basic_block_histo) ==
            sorted(stats.basic_block_histo))


def test_basic_block_stats_loopi(tmpdir: py.path.local) -> None:
    '''Check statistics for basic blocks in LOOPIs are calculated properly'''

    asm = """
    /* Loop 3 times over a body of 2 instructions. */
    loopi 3, 2
      nop
      nop
    ecall
    """

    stats = _simulate_asm_str(asm, tmpdir)

    assert stats.get_insn_count() == 8
    assert sorted(stats.basic_block_histo) == sorted({
        3: 1,  # 1 basic block with 4 instructions (addi + loop + 2x nop)
        2: 1,  # 1 basic block with 2 instructions (loop body on second iter.)
        1: 1   # 1 basic block with 1 instruction (ecall)
    })

    assert sorted(stats.ext_basic_block_histo) == sorted({
        8: 1  # All instructions are statically determined.
    })


def test_general_and_loop(tmpdir: py.path.local) -> None:
    '''Test the collection of general statistics as well as loop stats.'''

    asm_file = os.path.join(os.path.dirname(__file__),
                            'simple', 'loops', 'loops.s')
    stats = _simulate_asm_file(asm_file, tmpdir)

    # General statistics
    assert stats.stall_count == 4
    assert stats.get_insn_count() == 28
    assert stats.insn_histo == {'addi': 22, 'loop': 4, 'loopi': 1, 'ecall': 1}
    assert stats.func_calls == []

    # Loop statistics.
    exp = [
        # Outer LOOPI
        {'iterations': 4, 'loop_addr': 8, 'loop_len': 4},

        # Inner LOOP
        {'iterations': 3, 'loop_addr': 16, 'loop_len': 1},
        {'iterations': 3, 'loop_addr': 16, 'loop_len': 1},
        {'iterations': 3, 'loop_addr': 16, 'loop_len': 1},
        {'iterations': 3, 'loop_addr': 16, 'loop_len': 1}
    ]
    assert stats.loops == exp


def test_func_call_direct(tmpdir: py.path.local) -> None:
    '''Test the collection of statistics related to loops.'''

    asm_file = os.path.join(os.path.dirname(__file__),
                            'simple', 'subroutines', 'direct-call.s')
    stats = _simulate_asm_file(asm_file, tmpdir)

    exp = [{'call_site': 4, 'callee_func': 12, 'caller_func': 0}]
    assert stats.func_calls == exp


def test_func_call_indirect(tmpdir: py.path.local) -> None:
    '''Test the collection of statistics related to loops.'''

    asm_file = os.path.join(os.path.dirname(__file__),
                            'simple', 'subroutines', 'indirect-call.s')
    stats = _simulate_asm_file(asm_file, tmpdir)

    exp = [{'call_site': 8, 'callee_func': 16, 'caller_func': 0}]
    assert stats.func_calls == exp
