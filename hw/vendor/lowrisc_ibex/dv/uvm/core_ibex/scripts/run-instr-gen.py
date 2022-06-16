#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import re
import shlex
import shutil
import sys
import tempfile
from typing import List

from scripts_lib import (read_test_dot_seed, start_riscv_dv_run_cmd,
                         get_config, get_isas_for_config, run_one)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--end-signature-addr', required=True)
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--gen-build-dir', required=True)
    parser.add_argument('--ibex-config', required=True)

    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed, required=True)

    args = parser.parse_args()

    cfg = get_config(args.ibex_config)
    isa, iss_isa = get_isas_for_config(cfg)

    testname, seed = args.test_dot_seed

    inst_overrides = [
        'riscv_asm_program_gen',
        'ibex_asm_program_gen',
        'uvm_test_top.asm_gen'
    ]
    sim_opts_dict = {
        'uvm_set_inst_override': ','.join(inst_overrides),
        'signature_addr': args.end_signature_addr,
        'pmp_num_regions': str(cfg.pmp_num_regions),
        'pmp_granularity': str(cfg.pmp_granularity),
        'tvec_alignment': '8'
    }
    sim_opts_str = ' '.join('+{}={}'.format(k, v)
                            for k, v in sim_opts_dict.items())

    # Ensure that the output directory actually exists
    os.makedirs(args.output_dir, exist_ok=True)

    riscv_dv_log = os.path.join(args.output_dir, f'riscv-dv.log')
    gen_log = os.path.join(args.output_dir, f'gen-cmds.log')

    with tempfile.TemporaryDirectory() as td:
        orig_list = os.path.join(td, 'cmds.list')

        placeholder = os.path.join(td, '@@PLACEHOLDER@@')

        cmd = (start_riscv_dv_run_cmd(args.verbose) +
               ['--so', '--steps=gen',
                '--output', placeholder,
                '--simulator', args.simulator,
                '--isa', isa,
                '--test', testname,
                '--start_seed', str(seed),
                '--iterations', '1',
                '--sim_opts', sim_opts_str,
                '--debug', orig_list])

        # Run riscv-dv to generate commands. This is rather chatty, so redirect
        # its output to a log file.
        gen_retcode = run_one(args.verbose, cmd,
                              redirect_stdstreams=riscv_dv_log)
        if gen_retcode:
            return gen_retcode

        # Those commands assume the riscv-dv directory layout, where the build
        # and run directories are the same. Transform each of the commands as
        # necessary to point at the built generator
        cmds = reloc_commands(placeholder,
                              args.gen_build_dir,
                              td,
                              args.simulator,
                              testname,
                              orig_list)

        # Open up a file to take output from running the commands
        with open(gen_log, 'w') as log_fd:
            # Run the commands in sequence to create outputs in the temporary
            # directory. Redirect stdout and stderr to gen_log
            ret = 0
            for cmd in cmds:
                ret = run_one(args.verbose, cmd, redirect_stdstreams=log_fd)
                if ret != 0:
                    break

        test_file_copies = {
            'riscv_csr_test': [('riscv_csr_test_0.S', 'test.S', False)]
        }
        default_file_copies = [('gen.log', 'gen.log', True),
                               ('test_0.S', 'test.S', False)]

        file_copies = test_file_copies.get(testname, default_file_copies)

        do_file_copies(td, args.output_dir, file_copies, ret != 0)

    return 0


def reloc_commands(placeholder_dir: str,
                   build_dir: str,
                   scratch_dir: str,
                   simulator: str,
                   testname: str,
                   src: str) -> List[List[str]]:
    '''Reads the (one) line in src and apply relocations to it

    The result should be a series of commands that build a single test into
    scratch_dir/test_0.S, dumping a log into scratch_dir/gen.log.

    '''
    ret = []
    with open(src) as src_file:
        for line in src_file:
            line = line.strip()
            if not line:
                continue

            ret.append([reloc_word(simulator,
                                   placeholder_dir, build_dir,
                                   scratch_dir, testname, w)
                        for w in shlex.split(line)])
    return ret


def reloc_word(simulator: str,
               placeholder_dir: str, build_dir: str, scratch_dir: str,
               testname: str, word: str) -> str:
    '''Helper function for reloc_commands that relocates just one word'''
    sim_relocs = {
        'vcs': [
            # The VCS-generated binary
            (os.path.join(placeholder_dir, 'vcs_simv'),
             os.path.join(build_dir, 'vcs_simv'))
        ],
        'xlm': [
            # For Xcelium, the build directory gets passed as the
            # "-xmlibdirpath" argument.
            (placeholder_dir, build_dir)
        ]
    }
    always_relocs = [
        # The generated test. Since riscv-dv expects to make more than one of
        # them, this gets supplied as a plusarg with just the test name (with
        # no seed suffix).
        (os.path.join(placeholder_dir, 'asm_test', testname),
         os.path.join(scratch_dir, 'test')),

        # The asm_test directory. Annoyingly, the riscv_csr_test flow works
        # differently from the others and runs gen_csr_test.py, which has an
        # --out argument pointing here. More annoyingly still, it will write a
        # file there called `riscv_csr_test_0.S` which we'll have to move as a
        # tidy-up step at the end.
        #
        # Note that this needs to come after the relocation above, because that
        # renames the underlying file as well.
        (os.path.join(placeholder_dir, 'asm_test'),
         os.path.join(scratch_dir)),

        # The log file for generation itself
        (os.path.join(placeholder_dir, f'sim_{testname}_0.log'),
         os.path.join(scratch_dir, 'gen.log'))
    ]

    # Special handling for plusargs with filenames, which end up looking
    # something like +my_argument=foo/bar/baz.
    match = re.match(r'(\+[A-Za-z0-9_]+=)(.*)', word)
    if match is not None:
        pre = match.group(1)
        post = match.group(2)
    else:
        pre = ''
        post = word

    abs_post = os.path.abspath(post)

    for orig, reloc in sim_relocs[simulator] + always_relocs:
        abs_orig = os.path.abspath(orig)
        if abs_orig == abs_post:
            post = reloc
            break

    reloc = pre + post

    # Check there's no remaining occurrence of the placeholder
    if placeholder_dir in reloc:
        raise RuntimeError('Failed to replace an occurrence of the '
                           f'placeholder in {word} (got {reloc})')

    return reloc


def do_file_copies(src_dir, dst_dir, copy_rules, run_failed):
    '''Copy files back from src_dir to dst_dir, following copy_rules.

    These rules are a list of triples (src_name, dst_name, copy_on_fail). Here,
    the names are appended to src_dir and dst_dir to get source and destination
    paths. If a run failed, rules where copy_on_fail is False get ignored. If a
    run succeeded, we raise an error if a rule's source path doesn't point at a
    file that exists.

    '''
    for src_name, dst_name, copy_on_fail in copy_rules:
        if run_failed and not copy_on_fail:
            continue

        src_path = os.path.join(src_dir, src_name)
        dst_path = os.path.join(dst_dir, dst_name)

        if os.path.exists(src_path):
            shutil.copy(src_path, dst_path)
        elif not run_failed:
            raise RuntimeError(f'Generation commands exited with zero status '
                               f'but left no {src_name} in scratch directory.')


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as e:
        print(f'ERROR: {e}', file=sys.stderr)
        sys.exit(1)
