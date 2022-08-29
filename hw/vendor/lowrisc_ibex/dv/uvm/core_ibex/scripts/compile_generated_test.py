#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shlex
import sys
import tempfile
import pathlib3x as pathlib

from scripts_lib import run_one, format_to_cmd
import riscvdv_interface
from test_entry import read_test_dot_seed
from metadata import RegressionMetadata
from test_run_result import TestRunResult


def _main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    parser.add_argument('--test-dot-seed', type=read_test_dot_seed, required=True)
    args = parser.parse_args()
    tds = args.test_dot_seed
    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)
    trr = TestRunResult.construct_from_metadata_dir(args.dir_metadata, f"{tds[0]}.{tds[1]}")

    # Run riscv-dv to get a list of commands that it would run to try to
    # compile and convert the files in question. These will need some massaging
    # to match our paths, but we can't generate the commands by hand because
    # there are several test-specific options that might appear.
    with tempfile.TemporaryDirectory() as td:
        placeholder = os.path.join(td, '@@PLACEHOLDER@@')
        orig_list = os.path.join(td, 'orig-cmds.list')

        cmd = (riscvdv_interface.get_run_cmd(bool(md.verbose)) +
               ['--verbose',
                '--output', placeholder,
                '--steps=gcc_compile',
                '--test', trr.testname,
                '--start_seed', str(trr.seed),
                '--iterations', '1',
                '--isa', md.isa_ibex,
                '--debug', orig_list])

        trr.compile_asm_gen_log = trr.dir_test / 'compile_gen.riscv-dv.log'
        trr.compile_asm_gen_cmds = [format_to_cmd(cmd)]

        dv_ret = run_one(md.verbose, trr.compile_asm_gen_cmds[0],
                         redirect_stdstreams=trr.compile_asm_gen_log)
        if dv_ret:
            return dv_ret

        orig_cmds = []
        with open(orig_list) as orig_file:
            for line in orig_file:
                line = line.strip()
                if not line:
                    continue
                orig_cmds.append(shlex.split(line))

    # Do the massaging. We intentionally used "@@PLACEHOLDER@@" as a path in
    # our call to riscv-dv, which should let us find all the things that matter
    # easily.
    trr.objectfile = trr.dir_test / 'test.o'
    trr.binary = trr.dir_test / 'test.bin'

    rewrites = [
        (f"{placeholder}/asm_test/{trr.testname}_0.S", str(trr.assembly)),
        (f"{placeholder}/asm_test/{trr.testname}_0.o", str(trr.objectfile)),
        (f"{placeholder}/asm_test/{trr.testname}_0.bin", str(trr.binary))
    ]
    new_cmds = []
    for cmd in orig_cmds:
        new_cmd = []
        for word in cmd:
            for old, new in rewrites:
                word = word.replace(old, new)

            if placeholder in word:
                raise RuntimeError("Couldn't replace every copy of "
                                   f"placeholder in {cmd}")

            new_cmd.append(word)
        new_cmds.append(new_cmd)

    # Finally, run all the commands
    trr.compile_asm_log = trr.dir_test / 'compile.riscv-dv.log'
    trr.compile_asm_cmds = [format_to_cmd(cmd) for cmd in new_cmds]
    trr.export(write_yaml=True)

    for cmd in trr.compile_asm_cmds:
        ret = run_one(md.verbose, cmd)
        if ret != 0:
            return ret


if __name__ == '__main__':
    sys.exit(_main())
