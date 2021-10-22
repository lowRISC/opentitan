#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A handy wrapper that uses gen-binaries.sh and a Verilated binary

Use this with a command line like

    run-some.py --size=1500 --count=10 XXX

which will generate 10 OTBN binaries, each with up to 1500 instructions in
their respective traces. It will also build a Verilated model of OTBN (using
otbn_top_sim) and run the model on each binary.

'''

import argparse
import os
import shlex
import subprocess
import sys
from typing import TextIO

_SCRIPT_DIR = os.path.dirname(__file__)


def find_gen_binaries() -> str:
    '''Find the path to gen-binaries.py'''
    path = os.path.join(_SCRIPT_DIR, '../uvm/gen-binaries.py')
    if not os.path.exists(path):
        raise RuntimeError(f'No such file: {path}')
    return os.path.normpath(path)


def get_projdir() -> str:
    '''Return the path to the top of the project'''
    path = os.path.join(_SCRIPT_DIR, '../../../../..')
    assert os.path.exists(os.path.join(path, '.git'))
    return os.path.normpath(path)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--count', type=int, default=10,
                        help='Number of binaries to generate and run')
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--size', type=int, default=100)
    parser.add_argument('destdir', help='Destination directory')

    args = parser.parse_args()

    # Run gen-binaries.py in --gen-only mode, which will produce a
    # build.ninja.gen describing how to generate the binaries.
    gb_flags = ['--gen-only',
                '--ninja-suffix=gen',
                '--count={}'.format(args.count),
                '--seed={}'.format(args.seed),
                '--size={}'.format(args.size)]

    gb_cmd = [find_gen_binaries()] + gb_flags + [args.destdir]
    if subprocess.run(gb_cmd, check=False).returncode:
        print('Failed to run generate-binaries (command: {})'
              .format(' '.join([shlex.quote(arg) for arg in gb_cmd])),
              file=sys.stderr)
        return 1

    # Next, we make our own build.ninja, which says how to compile and run the
    # verilated testbench
    with open(os.path.join(args.destdir, 'build.ninja'), 'w') as ninja_handle:
        write_ninja(ninja_handle, args.destdir, args.seed, args.count)

    # Finally, use ninja to run everything, continuing on error (so that you
    # can run 100 seeds and see what proportion fails).
    ninja_cmd = ['ninja', '-C', args.destdir, '-k0', 'run']
    return subprocess.run(ninja_cmd, check=False).returncode


def write_ninja(handle: TextIO,
                destdir: str,
                seed: int,
                count: int) -> None:
    handle.write('include build.ninja.gen\n\n')

    # Find the project directory, as viewed from destdir
    projdir_from_here = get_projdir()
    projdir_from_destdir = os.path.relpath(projdir_from_here, destdir)

    # The rule to build the Verilated system
    handle.write('rule fusesoc\n'
                 f'  command = fusesoc --cores-root={projdir_from_destdir} '
                 'run --target=sim --setup --build lowrisc:ip:otbn_top_sim '
                 '>fusesoc.log 2>&1\n\n')
    handle.write('tb = build/lowrisc_ip_otbn_top_sim_0.1/'
                 'sim-verilator/Votbn_top_sim\n\n')
    handle.write('build $tb: fusesoc\n\n')

    # Collect up all the generated files
    basenames = [str(seed + off) for off in range(count)]

    # Rules to run them
    handle.write(f'rule run\n'
                 f'  command = REPO_TOP={projdir_from_destdir} '
                 f'$tb --load-elf $in >$out\n\n')
    for name in basenames:
        handle.write(f'build {name}.out: run {name}.elf | $tb\n')
    handle.write('\n')

    # A phony rule to run everything
    handle.write('build run: phony {}\n\n'
                 .format(' '.join([f'{name}.out' for name in basenames])))


if __name__ == '__main__':
    sys.exit(main())
