#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Build software running on OTBN

Each assembly source file is first assembled with otbn_as.py. All resulting
objects are then linked with otbn_ld.py. The resulting ELF file is converted
into an embeddable RV32 object file using objcopy.  In this object, all symbols
are prefixed with `_otbn_app_<appname>_` (only global symbols are included).

environment variables:
  This script, and the tools called from it, rely on the following environment
  variables for configuration. All environment variables are optional, and
  sensible default values are provided (tools are generally expected to be in
  the $PATH).

  OTBN_TOOLS         path to the OTBN linker and assemler tools
  RV32_TOOL_LD       path to RV32 ld
  RV32_TOOL_AS       path to RV32 as
  RV32_TOOL_AR       path to RV32 ar
  RV32_TOOL_OBJCOPY  path to RV32 objcopy

  The RV32* environment variables are used by both this script and the OTBN
  wrappers (otbn_as.py and otbn_ld.py) to find tools in a RV32 toolchain.

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
from typing import List, Optional, Tuple

import otbn_as
import otbn_ld
from elftools.elf.elffile import ELFFile, SymbolTableSection  # type: ignore


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


def run_tool(tool, out_file: Path, args) -> None:
    '''Run tool to produce out_file (using an '-o' argument)

    This works by writing to a temporary file (in the same directory) and then
    atomically replacing any existing destination file when done. This is
    needed if we need to run multiple otbn_build processes that generate the
    same files in parallel (this was a requirement of our old Meson-based
    infrastructure; it may not be needed now that we use Bazel).

    '''
    out_dir, out_base = os.path.split(out_file)
    tmpfile = tempfile.NamedTemporaryFile(prefix=out_base,
                                          dir=out_dir,
                                          delete=False)
    try:
        if type(tool) == str:
            run_cmd([tool, '-o', tmpfile.name] + args,
                    cmd_to_str([tool, '-o', out_file] + args))
        else:
            tool(['', '-o', tmpfile.name] + list(map(str, args)))

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
    run_tool(otbn_as.main, out_file, [src_file])


def call_otbn_ld(src_files: List[Path], out_file: Path,
                 linker_script: Optional[Path]):

    args = ['-gc-sections', '-gc-keep-exported']
    if linker_script:
        args += ['-T', linker_script]
    args += src_files
    run_tool(otbn_ld.main, out_file, args)


def call_rv32_objcopy(args: List[str]):
    rv32_tool_objcopy = os.environ.get('RV32_TOOL_OBJCOPY',
                                       'riscv32-unknown-elf-objcopy')
    run_cmd([rv32_tool_objcopy] + args)


def call_rv32_ar(args: List[str]):
    rv32_tool_ar = os.environ.get('RV32_TOOL_AR', 'riscv32-unknown-elf-ar')
    run_cmd([rv32_tool_ar] + args)


def get_otbn_syms(elf_path: str) -> List[Tuple[str, int]]:
    '''Get externally-visible symbols from an ELF

    Symbols are returned as a list of triples: (name, address). This
    discards locals and also anything in .scratchpad, since those addresses
    aren't bus-accessible.
    '''
    with tempfile.TemporaryDirectory() as tmpdir:
        # First, run objcopy to discard local symbols and the .scratchpad
        # section. We also use --extract-symbol since we don't care about
        # anything but the symbol data anyway.
        syms_path = os.path.join(tmpdir, 'syms.elf')
        call_rv32_objcopy([
            '-O', 'elf32-littleriscv', '--remove-section=.scratchpad',
            '--extract-symbol'
        ] + [elf_path, syms_path])

        # Load the file and use elftools to grab any symbol table
        with open(syms_path, 'rb') as syms_fd:
            syms_file = ELFFile(syms_fd)
            symtab = syms_file.get_section_by_name('.symtab')
            if symtab is None or not isinstance(symtab, SymbolTableSection):
                # No symbol table found or we did find a section called
                # .symtab, but it isn't actually a symbol table (huh?!). Give
                # up.
                return []

            ret = []
            for sym in symtab.iter_symbols():
                if sym['st_info']['bind'] != 'STB_GLOBAL':
                    continue
                addr = sym['st_value']
                assert isinstance(addr, int)
                ret.append((sym.name, addr))
            return ret


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--out-dir',
                        '-o',
                        required=False,
                        default=".",
                        help="Output directory (default: %(default)s)")
    parser.add_argument('--archive',
                        '-a',
                        action='store_true',
                        help='Archive the rv32embed.o file into a library.')
    parser.add_argument('--verbose',
                        '-v',
                        action='store_true',
                        help='Print commands that are executed.')
    parser.add_argument('--script',
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
    parser.add_argument(
        '--no-assembler',
        '-x',
        action='store_true',
        required=False,
        help="Use when input files have already been assembled into object "
        "files and only linking is required.")
    parser.add_argument('src_files', nargs='+', type=str, metavar='SRC_FILE')
    args = parser.parse_args()

    log_level = log.INFO if args.verbose else log.WARNING
    log.basicConfig(level=log_level, format="%(message)s")

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    src_files = [Path(f) for f in args.src_files]
    for src_file in src_files:
        if not src_file.exists():
            log.fatal("Source file %s not found." % src_file)
            return 1

    obj_files = []
    for f in src_files:
        if f.suffix == '.o':
            obj_files.append(f)
        else:
            obj_files.append(out_dir / f.with_suffix('.o').name)

    app_name = args.app_name or str(src_files[0].stem)
    archive = args.archive

    try:
        if not args.no_assembler:
            for src_file, obj_file in zip(src_files, obj_files):
                call_otbn_as(src_file, obj_file)

        out_elf = out_dir / (app_name + '.elf')
        call_otbn_ld(obj_files, out_elf, linker_script=args.linker_script)

        # out_elf is a fully-linked OTBN binary, but we want to be able to use
        # it from Ibex, the host processor. To make this work, we generate an
        # ELF file that can be linked into the Ibex image.
        #
        # This ELF contains all initialised data (the .text and .data
        # sections). We change the flags to treat them like rodata (since
        # they're not executable on Ibex, nor does it make sense for Ibex code
        # to manipulate OTBN data sections "in place") and add a .rodata.otbn
        # prefix to the section names.
        #
        # The symbols exposed by the binary will be relocated as part of the
        # link, so they'll point into the Ibex address space. To allow linking
        # against multiple OTBN applications, we give the symbols an
        # application-specific prefix. (Note: This prefix is used in driver
        # code: so needs to be kept in sync with that).
        #
        # As well as the initialised data and relocated symbols, we also want
        # to add (absolute) symbols that have the OTBN addresses of the symbols
        # in question. Unfortunately, objcopy doesn't seem to have a "make all
        # symbols absolute" command, so we have to do it by hand. This also
        # means constructing an enormous objcopy command line :-/ If we run out
        # of space, we might have to use elftools to inject the addresses after
        # the objcopy.
        host_side_pfx = '_otbn_local_app_{}_'.format(app_name)
        otbn_side_pfx = '_otbn_remote_app_{}_'.format(app_name)
        out_embedded_obj = out_dir / (app_name + '.rv32embed.o')
        args = [
            '-O', 'elf32-littleriscv',
            '--set-section-flags=*=alloc,load,readonly',
            '--remove-section=.scratchpad', '--remove-section=.bss',
            '--prefix-sections=.rodata.otbn', '--prefix-symbols', host_side_pfx
        ]
        for name, addr in get_otbn_syms(out_elf):
            args += ['--add-symbol', f'{otbn_side_pfx}{name}=0x{addr:x}']

        call_rv32_objcopy(args + [out_elf, out_embedded_obj])

        # After objcopy has finished, we have to do a little surgery to
        # overwrite the ELF e_type field (a 16-bit little-endian number at file
        # offset 0x10). It will currently be 0x2 (ET_EXEC), which means a
        # fully-linked executable file. Binutils doesn't want to link with
        # anything of type ET_EXEC (since it usually wouldn't make any sense to
        # do so). Hack the type to be 0x1 (ET_REL), which means an object file.
        with open(out_embedded_obj, 'r+b') as emb_file:
            emb_file.seek(0x10)
            emb_file.write(b'\1\0')

        if archive:
            out_embedded_a = out_dir / (app_name + '.rv32embed.a')
            call_rv32_ar(['rcs', out_embedded_a, out_embedded_obj])

    except subprocess.CalledProcessError as e:
        # Show a nicer error message if any of the called programs fail.
        log.fatal("Command {!r} returned non-zero exit code {}".format(
            cmd_to_str(e.cmd), e.returncode))
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
