#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Build software running on OTBN

Each assembly source file is first assembled with otbn-as. All resulting objects
are then linked with otbn-ld. The resulting ELF file is converted into an
embeddable RV32 object file using objcopy.  In this object, all symbols
are prefixed with `_otbn_app_<appname>_` (only global symbols are included).

environment variables:
  This script, and the tools called from it, rely on the following environment
  variables for configuration. All environment variables are optional, and
  sensible default values are provided (tools are generally expected to be in
  the $PATH).

  OTBN_AS            path to otbn-as, the OTBN assembler
  OTBN_LD            path to otbn-ld, the OTBN linker
  RV32_TOOL_LD       path to RV32 ld
  RV32_TOOL_AS       path to RV32 as
  RV32_TOOL_OBJCOPY  path to RV32 objcopy

  The RV32* environment variables are used by both this script and the OTBN
  wrappers (otbn-as and otbn-ld) to find tools in a RV32 toolchain.

outputs:
  The build process produces multiple files inside the output directory.

  <src_file>.o            the compiled source files
  <app_name>.elf          the compiled and linked application targeting OTBN
  <app_name>.rv32embed.o  the application as embeddable object for RV32

"""

import argparse
import logging as log
import os
import shlex
import subprocess
import sys
from pathlib import Path
from typing import List

log.basicConfig(level=log.INFO, format="%(message)s")

REPO_TOP = Path(__file__).parent.parent.resolve()

def cmd_to_str(cmd):
    return ' '.join([shlex.quote(str(a)) for a in cmd])


def run_cmd(cmd, **kwargs):
    log.info(cmd_to_str(cmd))
    subprocess.run(cmd, **kwargs)


def call_otbn_as(src_file: Path, out_file: Path):
    otbn_as_cmd = os.environ.get('OTBN_AS',
                                 str(REPO_TOP / 'hw/ip/otbn/util/otbn-as'))
    run_cmd([otbn_as_cmd, '-o', out_file, src_file], check=True)


def call_otbn_ld(src_files: List[Path], out_file: Path):
    otbn_ld_cmd = os.environ.get('OTBN_LD',
                                 str(REPO_TOP / 'hw/ip/otbn/util/otbn-ld'))
    run_cmd([otbn_ld_cmd, '-o', out_file] + src_files, check=True)


def call_rv32_objcopy(args: List[str]):
    rv32_tool_objcopy = os.environ.get('RV32_TOOL_OBJCOPY',
                                       'riscv32-unknown-elf-objcopy')
    run_cmd([rv32_tool_objcopy] + args, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        '--out-dir',
        '-o',
        required=False,
        default=".",
        help="Output directory (default: %(default)s)")
    parser.add_argument(
        '--app-name',
        '-n',
        required=False,
        help="Name of the application, used as basename for the output. "
             "Default: basename of the first source file.")
    parser.add_argument('src_files', nargs='+', type=str, metavar='SRC_FILE')
    args = parser.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(exist_ok=True)

    src_files = [Path(f) for f in args.src_files]
    for src_file in src_files:
        if not src_file.exists():
            log.fatal("Source file %s not found." % src_file)
            return 1
    obj_files = [out_dir / f.with_suffix('.o').name for f in src_files]

    app_name = args.app_name or str(src_files[0].stem)

    try:
        for src_file, obj_file in zip(src_files, obj_files):
            call_otbn_as(src_file, obj_file)

        out_elf = out_dir / (app_name + '.elf')
        call_otbn_ld(obj_files, out_elf)

        out_embedded_obj = out_dir / (app_name + '.rv32embed.o')
        args = [
            '-O',
            'elf32-littleriscv',
            '--prefix-symbols',
            '_otbn_app_' + app_name + '_',
            out_elf,
            out_embedded_obj,
        ]

        call_rv32_objcopy(args)
    except subprocess.CalledProcessError as e:
        # Show a nicer error message if any of the called programs fail.
        log.fatal("Command {!r} returned non-zero exit code {}".format(
            cmd_to_str(e.cmd), e.returncode))
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
