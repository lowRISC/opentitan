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
import pathlib3x as pathlib
from typing import List

from test_entry import read_test_dot_seed
import riscvdv_interface
from scripts_lib import run_one, format_to_cmd
from ibex_cmd import get_config
from metadata import RegressionMetadata
from test_run_result import TestRunResult

import logging
logger = logging.getLogger(__name__)


def reloc_commands(placeholder_dir: str,
                   build_dir: str,
                   scratch_dir: str,
                   simulator: str,
                   testname: str,
                   src: str) -> List[List[str]]:
    """Read (one) line in src and apply relocations to it.

    The result should be a series of commands that build a single test into
    scratch_dir/test_0.S, dumping a log into scratch_dir/gen.log.

    """
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
    """Helper function for reloc_commands that relocates just one word."""
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


def _main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    parser.add_argument('--test-dot-seed', type=read_test_dot_seed, required=True)
    args = parser.parse_args()
    tds = args.test_dot_seed
    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)
    trr = TestRunResult.construct_from_metadata_dir(args.dir_metadata, f"{tds[0]}.{tds[1]}")

    cfg = get_config(md.ibex_config)

    inst_overrides = [
        'riscv_asm_program_gen',
        'ibex_asm_program_gen',
        'uvm_test_top.asm_gen'
    ]

    # Special-case for riscv_csr_test -> fixup the handshake addr.
    # Currently use (signature_addr - 0x4) for test_done channel.
    sig = ((md.signature_addr) if ('riscv_csr_test' not in trr.testname)
           else
           f'{(int(md.signature_addr, 16) - 4):x}')  # (signature_addr - 0x4)

    sim_opts_dict = {
        'uvm_set_inst_override': ','.join(inst_overrides),
        'require_signature_addr': '1',
        'signature_addr': sig,
        'pmp_num_regions': str(cfg.pmp_num_regions),
        'pmp_granularity': str(cfg.pmp_granularity),
        'tvec_alignment': '8'
    }

    with tempfile.TemporaryDirectory() as td:
        orig_list = pathlib.Path(td)/'cmds.list'
        placeholder = pathlib.Path(td)/'@@PLACEHOLDER@@'

        cmd = (riscvdv_interface.get_run_cmd(md.verbose) +
               ['--so', '--steps=gen',
                '--output', str(placeholder),
                '--simulator', md.simulator,
                '--isa', md.isa_ibex,
                '--test', trr.testname,
                '--start_seed', str(trr.seed),
                '--iterations', '1',
                '--end_signature_addr', sig,
                '--debug', str(orig_list),
                '--sim_opts', ' '.join('+{}={}'.format(k, v)
                                       for k, v in sim_opts_dict.items())
                ])

        # Ensure that the output directory actually exists
        trr.dir_test.mkdir(parents=True, exist_ok=True)
        trr.riscvdv_run_gen_stdout = md.dir_instruction_generator/'riscvdv_cmds.log'
        trr.riscvdv_run_gen_cmds   = [format_to_cmd(cmd)]
        # Run riscv-dv to generate commands. This is rather chatty, so redirect
        # its output to a log file.
        gen_retcode = run_one(md.verbose, trr.riscvdv_run_gen_cmds[0],
                              redirect_stdstreams=trr.riscvdv_run_gen_stdout)
        if gen_retcode:
            return gen_retcode

        # Those commands assume the riscv-dv directory layout, where the build
        # and run directories are the same. Transform each of the commands as
        # necessary to point at the built generator
        cmds = reloc_commands(str(placeholder),
                              str(md.dir_instruction_generator.resolve()),
                              td,
                              md.simulator,
                              trr.testname,
                              str(orig_list))

        trr.riscvdv_run_cmds   = [format_to_cmd(cmd) for cmd in cmds]
        trr.riscvdv_run_stdout = md.dir_instruction_generator/'riscvdv_run.log'
        trr.assembly           = trr.dir_test / 'test.S'
        # Open up a file to take output from running the commands
        with trr.riscvdv_run_stdout.open('w') as log_fd:
            # Run the commands in sequence to create outputs in the temporary
            # directory. Redirect stdout and stderr to gen_log
            ret = 0
            for cmd in trr.riscvdv_run_cmds:
                ret = run_one(md.verbose, cmd, redirect_stdstreams=log_fd)
                if ret != 0:
                    break

        test_file_copies = {
            'riscv_csr_test': [('riscv_csr_test_0.S', 'test.S', False)]
        }
        default_file_copies = [('gen.log', 'gen.log', True),
                               ('test_0.S', 'test.S', False)]

        file_copies = test_file_copies.get(trr.testname, default_file_copies)

        do_file_copies(td, trr.dir_test, file_copies, ret != 0)

    trr.export(write_yaml=True)

    return 0


if __name__ == '__main__':
    sys.exit(_main())
