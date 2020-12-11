# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Run tests to make sure the simulator works as expected

We expect a test in each directory below ./simple. This test should comprise a
single assembly file (called <something>.s) and a file called expected.txt,
containing a list of expected register values.

'''

import os
import py
import re
import subprocess
from typing import Any, Dict, List, Tuple


_OTBN_DIR = os.path.join(os.path.dirname(__file__), '../../..')
_UTIL_DIR = os.path.join(_OTBN_DIR, 'util')
_SIM_DIR = os.path.join(os.path.dirname(__file__), '..')

_REG_RE = re.compile(r'\s*([xw][0-9]+)\s*=\s*((:?0x[0-9a-f]+)|([0-9]+))$')


def find_simple_tests() -> List[Tuple[str, str]]:
    '''Find all tests below ./simple (relative to this file)

    Returns (asm, expected) pairs, with the paths to the assembly file and
    expected values.

    '''
    root = os.path.join(os.path.dirname(__file__), 'simple')
    ret = []
    for subdir, _, files in os.walk(root):
        # We're interested in pairs foo.s / foo.exp, which contain the assembly
        # and expected values, respectively.
        asm_files = {}
        exp_files = {}

        for filename in files:
            basename, ext = os.path.splitext(filename)
            if ext == '.s':
                assert basename not in asm_files
                asm_files[basename] = filename
            elif ext == '.exp':
                assert basename not in exp_files
                exp_files[basename] = filename
            else:
                # Ignore any files that aren't called .s or .exp (which allows
                # things like adding READMEs to the tree)
                pass

        dirname = os.path.join(root, subdir)

        # Pair up the files we found
        for basename, asm_file in asm_files.items():
            exp_file = exp_files.get(basename)
            if exp_file is None:
                raise RuntimeError('In the directory {!r}, there is {}, but '
                                   'no {}.exp, which should contain expected '
                                   'values.'
                                   .format(dirname, asm_file, basename))

            ret.append((os.path.join(dirname, asm_file),
                        os.path.join(dirname, exp_file)))

        # We've checked that every .s file has a matching .exp. Check the other
        # way around too.
        for basename, exp_file in exp_files.items():
            if basename not in asm_files:
                raise RuntimeError('In the directory {!r}, there is {}, but '
                                   'no {}.s, which should contain the program '
                                   'that generates the expected values.'
                                   .format(dirname, exp_file, basename))

        assert len(exp_files) == len(asm_files)

    return ret


def asm_and_link_one_file(asm_path: str, work_dir: str) -> str:
    '''Assemble and link file at asm_path in work_dir.

    Returns the path to the resulting ELF

    '''
    otbn_as = os.path.join(_UTIL_DIR, 'otbn-as')
    otbn_ld = os.path.join(_UTIL_DIR, 'otbn-ld')
    obj_path = os.path.join(work_dir, 'tst.o')
    elf_path = os.path.join(work_dir, 'tst')

    subprocess.run([otbn_as, '-o', obj_path, asm_path], check=True)
    subprocess.run([otbn_ld, '-o', elf_path, obj_path], check=True)
    return elf_path


def get_reg_dump(stdout: str) -> Dict[str, int]:
    '''Parse the output from a simple test ending in print_regs

    Returns a dictionary keyed by register name and with value equal to the
    value that register ended up with.

    '''
    started = False
    done = False
    ret = {}
    for line in stdout.split('\n'):
        if line == 'PRINT_REGS':
            if started:
                raise RuntimeError('Multiple PRINT_REGS lines seen')
            started = True
            continue
        if done or not started:
            continue

        if line == '.':
            done = True
            continue

        m = _REG_RE.match(line)
        if not m:
            raise RuntimeError('Failed to parse line after PRINT_REGS ({!r}).'
                               .format(line))

        ret[m.group(1)] = int(m.group(2), 0)

    return ret


def get_reg_expected(exp_path: str) -> Dict[str, int]:
    '''Read expected.txt

    Returns same format as get_reg_dump, assuming any unspecified registers
    should be zero.

    '''
    ret = {}
    for idx in range(32):
        ret['x{}'.format(idx)] = 0
        ret['w{}'.format(idx)] = 0

    with open(exp_path) as exp_file:
        for idx, line in enumerate(exp_file):
            # Comments with '#'; ignore blank lines
            line = line.split('#', 1)[0].strip()
            if not line:
                continue

            m = _REG_RE.match(line)
            if m is None:
                raise RuntimeError('{}:{}: Bad format for line in expected.txt.'
                                   .format(exp_path, idx + 1))
            ret[m.group(1)] = int(m.group(2), 0)

    return ret


def test_count(tmpdir: py.path.local,
               asm_file: str,
               expected_file: str) -> None:
    # Start by assembling and linking the input file
    elf_file = asm_and_link_one_file(asm_file, str(tmpdir))

    # Run the simulation. We can just pass a list of commands to stdin, and
    # don't need to do anything clever to track what's going on.
    stepped_py = os.path.join(_SIM_DIR, 'stepped.py')
    commands = 'load_elf {}\nstart 0\nrun\nprint_regs\n'.format(elf_file)
    sim_proc = subprocess.run([stepped_py], check=True, input=commands,
                              stdout=subprocess.PIPE, universal_newlines=True)

    regs_seen = get_reg_dump(sim_proc.stdout)
    regs_expected = get_reg_expected(expected_file)

    assert regs_seen == regs_expected


def pytest_generate_tests(metafunc: Any) -> None:
    if metafunc.function is test_count:
        metafunc.parametrize("asm_file,expected_file", find_simple_tests())
