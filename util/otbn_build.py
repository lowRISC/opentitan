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
import tempfile
from pathlib import Path
from typing import List, Optional

REPO_TOP = Path(__file__).parent.parent.resolve()


def cmd_to_str(cmd: List[str]) -> str:
    return ' '.join([shlex.quote(str(a)) for a in cmd])


def run_cmd(args, display_cmd=None):
    '''Run the command in args.

    If display_cmd is not None, it should be a string that is printed instead
    of the actual arguments that ran (for hiding the details of temporary
    files).

    '''
    str_args = [str(a) for a in args]
    info_msg = cmd_to_str(str_args) if display_cmd is None else display_cmd
    log.info(info_msg)

    subprocess.run(str_args, check=True)


def run_tool(tool: str, out_file: Path, args) -> None:
    '''Run tool to produce out_file (using an '-o' argument)

    This works by writing to a temporary file (in the same directory) and then
    atomically replacing any existing destination file when done. This is
    needed if we need to run multiple otbn_build processes that generate the
    same files in parallel (a requirement because of our current Meson-based
    infrastructure).

    '''
    out_dir, out_base = os.path.split(out_file)
    tmpfile = tempfile.NamedTemporaryFile(prefix=out_base, dir=out_dir,
                                          delete=False)
    try:
        run_cmd([tool, '-o', tmpfile.name] + args,
                cmd_to_str([tool, '-o', out_file] + args))

        # If we get here, the tool ran successfully, producing the output file.
        # Use os.replace to rename appropriately.
        os.replace(tmpfile.name, out_file)
    finally:
        # When we're done, or if something went wrong, close and try to delete
        # the temporary file. The unlink should fail if the os.replace call
        # above succeeded. That's fine.
        tmpfile.close()
        try:
            os.unlink(tmpfile.name)
        except FileNotFoundError:
            pass


def call_otbn_as(src_file: Path, out_file: Path):
    otbn_as_cmd = os.environ.get('OTBN_AS',
                                 str(REPO_TOP / 'hw/ip/otbn/util/otbn-as'))
    run_tool(otbn_as_cmd, out_file, [src_file])


def call_otbn_ld(src_files: List[Path], out_file: Path, linker_script: Optional[Path]):
    otbn_ld_cmd = os.environ.get('OTBN_LD',
                                 str(REPO_TOP / 'hw/ip/otbn/util/otbn-ld'))

    args = []
    if linker_script:
        args += ['-T', linker_script]
    args += src_files
    run_tool(otbn_ld_cmd, out_file, args)


def call_rv32_objcopy(args: List[str]):
    rv32_tool_objcopy = os.environ.get('RV32_TOOL_OBJCOPY',
                                       'riscv32-unknown-elf-objcopy')
    run_cmd([rv32_tool_objcopy] + args)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        '--out-dir',
        '-o',
        required=False,
        default=".",
        help="Output directory (default: %(default)s)")
    parser.add_argument(
        '--verbose',
        '-v',
        action='store_true',
        help='Print commands that are executed.')
    parser.add_argument(
        '--script',
        '-T',
        dest="linker_script",
        required=False,
        help="Linker script")
    parser.add_argument(
        '--app-name',
        '-n',
        required=False,
        help="Name of the application, used as basename for the output. "
             "Default: basename of the first source file.")
    parser.add_argument('src_files', nargs='+', type=str, metavar='SRC_FILE')
    args = parser.parse_args()

    log_level = log.INFO if args.verbose else log.WARNING
    log.basicConfig(level=log_level, format="%(message)s")

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
        call_otbn_ld(obj_files, out_elf, linker_script = args.linker_script)

        # Use objcopy to create an ELF that can be linked into a RISC-V binary
        # (to run on Ibex). This should set flags for all sections to look like
        # rodata (since they're not executable on Ibex, nor does it make sense
        # for Ibex code to manipulate OTBN data sections "in place"). We name
        # them with a .otbn prefix, so end up with e.g. .rodata.otbn.text and
        # .rodata.otbn.data.
        #
        # Symbols that are exposed by the binary (including those giving the
        # start and end of imem and dmem) will be relocated as part of the
        # link, so they'll give addresses in the Ibex address space. So that
        # the RISC-V binary can link multiple OTBN applications, we give them
        # an application-specific prefix. (Note: This prefix is used in
        # sw/device/lib/runtime/otbn.h: so needs to be kept in sync with that).
        sym_pfx = '_otbn_app_{}_'.format(app_name)
        out_embedded_obj = out_dir / (app_name + '.rv32embed.o')
        args = (['-O', 'elf32-littleriscv',
                 '--prefix-sections=.rodata.otbn',
                 '--set-section-flags=*=alloc,load,readonly',
                 '--prefix-symbols', sym_pfx] +
                [out_elf,
                 out_embedded_obj])

        call_rv32_objcopy(args)

        # After objcopy has finished, we have to do a little surgery to
        # overwrite the ELF e_type field (a 16-bit little-endian number at file
        # offset 0x10). It will currently be 0x2 (ET_EXEC), which means a
        # fully-linked executable file. Binutils doesn't want to link with
        # anything of type ET_EXEC (since it usually wouldn't make any sense to
        # do so). Hack the type to be 0x1 (ET_REL), which means an object file.
        with open(out_embedded_obj, 'r+b') as emb_file:
            emb_file.seek(0x10)
            emb_file.write(b'\1\0')

    except subprocess.CalledProcessError as e:
        # Show a nicer error message if any of the called programs fail.
        log.fatal("Command {!r} returned non-zero exit code {}".format(
            cmd_to_str(e.cmd), e.returncode))
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
