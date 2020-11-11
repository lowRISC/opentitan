#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A helper script to generate a default set of binaries for OTBN testing

This is intended for use with dvsim, which should call this script as
part of the test build phase.

'''

import argparse
import os
import subprocess
import sys
import tempfile


def read_positive(val):
    ival = -1
    try:
        ival = int(val, 0)
    except ValueError:
        pass

    if ival <= 0:
        raise argparse.ArgumentTypeError('{!r} is not a positive integer.'
                                         .format(val))
    return ival


def read_jobs(val):
    if val == 'unlimited':
        return 'unlimited'
    if val is None:
        return None

    return read_positive(val)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--count', type=read_positive, default=10,
                        help='Number of binaries to generate')
    parser.add_argument('--seed', type=read_positive, default=0)
    parser.add_argument('--jobs', '-j', type=read_jobs, nargs='?',
                        const='unlimited', help='Number of parallel jobs.')
    parser.add_argument('destdir',
                        help='Destination directory')

    args = parser.parse_args()
    if args.count < 0:
        print('ERROR: Any argument to --count must be positive.',
              file=sys.stderr)
        return 1

    otbn_dir = os.path.normpath(os.path.join(os.path.dirname(__file__),
                                             '../..'))

    rig_count = args.count - 1
    util_dir = os.path.join(otbn_dir, 'util')
    smoke_src_dir = os.path.join(otbn_dir, 'dv/smoke')

    with tempfile.TemporaryDirectory() as tmpdir:
        with open(os.path.join(tmpdir, 'Makefile'), 'w') as make_handle:
            write_makefile(make_handle, rig_count, args.seed,
                           util_dir, args.destdir, smoke_src_dir)

        if args.jobs is None:
            j_args = []
        elif args.jobs == 'unlimited':
            j_args = ['-j']
        else:
            j_args = ['-j', str(args.jobs)]

        subprocess.run(['make', '-C', tmpdir] + j_args + ['install'])

    return 0


def write_makefile(handle, rig_count, start_seed,
                   util_dir, dst_dir, smoke_src_dir):
    '''Write a Makefile to build rig_count random binaries and a smoke test

    Everything gets created in the Makefile's directory, then copied to
    dst_dir. OTBN tooling is found in util_dir.

    '''
    # A prefix that should be prepended to OTBN tooling. We resolve util_dir to
    # an absolute path here because the Makefile is interpreted in a different
    # directory from the one we're currently in.
    otbn_util_pfx = os.path.join(os.path.abspath(util_dir), 'otbn-')

    seeds = [start_seed + idx for idx in range(rig_count)]

    for seed in seeds:
        # This first rule actually generates the .s and .ld files. Since
        # tracking multiple targets in Make is painful, we'll pretend it just
        # generates the .s.
        handle.write('{seed}.s:\n'
                     '\t{pfx}rig gen --size 100 --seed {seed} | '
                     '{pfx}rig asm -o {seed}\n\n'
                     .format(seed=seed, pfx=otbn_util_pfx))

        # Assemble the .s file to an object
        handle.write('{seed}.o: {seed}.s\n'
                     '\t{pfx}as -o $@ $<\n\n'
                     .format(seed=seed, pfx=otbn_util_pfx))

        # Link the object using the generated linker script (generated, but not
        # tracked, in the first rule)
        handle.write('{seed}.elf: {seed}.o\n'
                     '\t{pfx}ld -o $@ -T {seed}.ld $<\n\n'
                     .format(seed=seed, pfx=otbn_util_pfx))

    # Rules to build the smoke test.
    smoke_src = os.path.join(os.path.abspath(smoke_src_dir), 'smoke_test.s')
    handle.write('smoke.o: {smoke_src}\n'
                 '\t{pfx}as -o $@ $<\n\n'
                 .format(smoke_src=smoke_src, pfx=otbn_util_pfx))
    handle.write('smoke.elf: smoke.o\n'
                 '\t{pfx}ld -o $@ $<\n\n'
                 .format(pfx=otbn_util_pfx))

    # A rule to generate the installation directory if needed
    abs_dst_dir = os.path.abspath(dst_dir)
    handle.write('{dst_dir}:\n'
                 '\tmkdir -p $@\n\n'
                 .format(dst_dir=abs_dst_dir))

    # Finally, define a rule to copy everything to the destination directory.
    elf_files = ' '.join(['smoke.elf'] +
                         ['{}.elf'.format(seed) for seed in seeds])
    handle.write('.PHONY: install\n'
                 'install: {elf_files} | {dst_dir}\n'
                 '\tcp -t {dst_dir} $^\n\n'
                 .format(elf_files=elf_files,
                         dst_dir=abs_dst_dir))


if __name__ == '__main__':
    sys.exit(main())
