# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import subprocess


OTBN_DIR = os.path.join(os.path.dirname(__file__), '../../..')
UTIL_DIR = os.path.join(OTBN_DIR, 'util')
SIM_DIR = os.path.join(os.path.dirname(__file__), '..')


def asm_and_link_one_file(asm_path: str, work_dir: str) -> str:
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
