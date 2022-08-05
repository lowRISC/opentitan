#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shlex
import sys
import tempfile

from scripts_lib import (read_test_dot_seed, start_riscv_dv_run_cmd,
                         get_config, get_isas_for_config, run_one)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--input', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--ibex-config', required=True)

    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed, required=True)

    args = parser.parse_args()

    cfg = get_config(args.ibex_config)
    isa, iss_isa = get_isas_for_config(cfg)
    testname, seed = args.test_dot_seed

    if not args.output.endswith('.bin'):
        raise RuntimeError("Output argument must end with .bin: "
                           f"got {args.output!r}")
    out_base = args.output[:-4]
    out_riscv_dv_path = os.path.join(os.path.dirname(args.output),
                                     'compile.riscv-dv.log')
    out_obj_path = out_base + '.o'

    # Run riscv-dv to get a list of commands that it would run to try to
    # compile and convert the files in question. These will need some massaging
    # to match our paths, but we can't generate the commands by hand because
    # there are several test-specific options that might appear.
    with tempfile.TemporaryDirectory() as td:
        placeholder = os.path.join(td, '@@PLACEHOLDER@@')
        orig_list = os.path.join(td, 'orig-cmds.list')

        dv_ret = run_one(False,
                         start_riscv_dv_run_cmd(args.verbose) +
                         ['--verbose',
                          '--output', placeholder,
                          '--steps=gcc_compile',
                          '--test', testname,
                          '--start_seed', str(seed),
                          '--iterations', '1',
                          '--isa', isa,
                          '--debug', orig_list],
                         redirect_stdstreams=out_riscv_dv_path)
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
    rewrites = [
        (f"{placeholder}/asm_test/{testname}_0.S", args.input),
        (f"{placeholder}/asm_test/{testname}_0.o", out_obj_path),
        (f"{placeholder}/asm_test/{testname}_0.bin", args.output)
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
    for cmd in new_cmds:
        ret = run_one(args.verbose, cmd)
        if ret != 0:
            return ret


if __name__ == '__main__':
    sys.exit(main())
