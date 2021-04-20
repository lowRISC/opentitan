# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import py
import os

from sim.sim import OTBNSim
from sim.stats import ExecutionStats
from sim.elf import load_elf
import testutil


def _run_sim_for_stats(asm_file: str, tmpdir: str) -> ExecutionStats:
    """ Run the OTBN simulator, collect statistics, and return them. """

    assert os.path.exists(asm_file)
    elf_file = testutil.asm_and_link_one_file(asm_file, tmpdir)

    sim = OTBNSim()
    load_elf(sim, elf_file)

    sim.state.start(0)
    sim.run(verbose=False, collect_stats=True)

    return sim.stats


def test_general_and_loop(tmpdir: py.path.local) -> None:
    """ Test the collection of general statistics as well as loop stats. """

    asm_file = os.path.join(os.path.dirname(__file__),
                            'simple', 'loops', 'loops.s')
    stats = _run_sim_for_stats(asm_file, str(tmpdir))

    # General statistics
    assert stats.stall_count == 2
    assert stats.insn_count == 28
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
    """ Test the collection of statistics related to loops. """

    asm_file = os.path.join(os.path.dirname(__file__),
                            'simple', 'subroutines', 'direct-call.s')
    stats = _run_sim_for_stats(asm_file, str(tmpdir))

    exp = [{'call_site': 4, 'callee_func': 12, 'caller_func': 0}]
    assert stats.func_calls == exp


def test_func_call_indirect(tmpdir: py.path.local) -> None:
    """ Test the collection of statistics related to loops. """

    asm_file = os.path.join(os.path.dirname(__file__),
                            'simple', 'subroutines', 'indirect-call.s')
    stats = _run_sim_for_stats(asm_file, str(tmpdir))

    exp = [{'call_site': 8, 'callee_func': 16, 'caller_func': 0}]
    assert stats.func_calls == exp
