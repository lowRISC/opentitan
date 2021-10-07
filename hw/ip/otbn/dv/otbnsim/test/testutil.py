# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import py
import os
import subprocess
import tempfile

from sim.elf import load_elf
from sim.sim import OTBNSim


OTBN_DIR = os.path.join(os.path.dirname(__file__), '../../..')
UTIL_DIR = os.path.join(OTBN_DIR, 'util')
SIM_DIR = os.path.join(os.path.dirname(__file__), '..')


def asm_and_link_one_file(asm_path: str, work_dir: py.path.local) -> str:
    '''Assemble and link file at asm_path in work_dir.

    Returns the path to the resulting ELF

    '''
    otbn_as = os.path.join(UTIL_DIR, 'otbn-as')
    otbn_ld = os.path.join(UTIL_DIR, 'otbn-ld')
    obj_path = os.path.join(work_dir, 'tst.o')
    elf_path = os.path.join(work_dir, 'tst')

    subprocess.run([otbn_as, '-o', obj_path, asm_path], check=True)
    subprocess.run([otbn_ld, '-o', elf_path, obj_path], check=True)
    return elf_path


def prepare_sim_for_asm_file(asm_file: str,
                             tmpdir: py.path.local,
                             collect_stats: bool) -> OTBNSim:
    '''Set up the simulation of a single assembly file.

    The returned simulation is ready to be run through the run() method.

    '''
    assert os.path.exists(asm_file)
    elf_file = asm_and_link_one_file(asm_file, tmpdir)

    sim = OTBNSim()
    load_elf(sim, elf_file)

    sim.state.ext_regs.commit()
    sim.start(collect_stats)
    return sim


def prepare_sim_for_asm_str(assembly: str,
                            tmpdir: py.path.local,
                            collect_stats: bool) -> OTBNSim:
    '''Set up the simulation for an assembly snippet passed as string.

    The returned simulation is ready to be run through the run() method.

    '''
    with tempfile.NamedTemporaryFile('w', dir=tmpdir) as fp:
        fp.write(assembly)
        fp.flush()
        return prepare_sim_for_asm_file(fp.name, tmpdir, collect_stats)
