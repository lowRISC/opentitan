#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A wrapper around riscv32-unknown-elf-objdump for OTBN'''

import re
import subprocess
import sys
from typing import List

from shared.insn_yaml import InsnsFile, load_insns_yaml
from shared.toolchain import find_tool


def snoop_disasm_flags(argv: List[str]) -> bool:
    '''Look through objdump's flags for -d, -D etc.'''
    for arg in argv:
        # We're only interested in flags (starting with '-' or '--')
        if not arg.startswith('-'):
            continue

        # If the argument starts with a single hyphen, the following characters
        # explode into multiple flags (so -fhSD is the same as -f -h -S -D).
        # Handle -d and -D here.
        if not arg.startswith('--'):
            if 'd' in arg[1:] or 'D' in arg[1:]:
                return True
            else:
                continue

        # The argument starts with two hyphens.
        if arg in ['--disassemble', '--disassemble-all']:
            return True

        # --disassemble=symbol
        if arg.startswith('--disassemble='):
            return True

    return False


# OTBN instructions are 32 bit wide, so there's just one "word" in the second
# column. The stuff that gets passed through looks like this:
#
#    84:   8006640b                0x8006640b
#
# We don't use a back-ref for the second copy of the data, because if the raw
# part has leading zeros, they don't appear there. For example:
#
#   6d0:   0000418b                0x418b
#
_RAW_INSN_RE = re.compile(r'([\s]*([0-9a-f]+):[\s]+([0-9a-f]{8})[\s]+)'
                          r'0x[0-9a-f]+\s*$')


def transform_disasm_line(line: str, insns_file: InsnsFile) -> str:
    '''Transform filter to insert OTBN disasm as needed'''
    match = _RAW_INSN_RE.match(line)
    if match is None:
        return line

    # match.group(3) is the raw instruction word. Parse it as an integer. It
    # was exactly 8 hex characters, so will fit in a u32.
    raw = int(match.group(3), 16)
    assert 0 <= raw < (1 << 32)

    mnem = insns_file.mnem_for_word(raw)
    if mnem is None:
        # No match for this instruction pattern. Leave as-is.
        return line

    insn = insns_file.mnemonic_to_insn[mnem]

    # match.group(2) is the PC in hex.
    pc = int(match.group(2), 16)

    # Extract the encoded values. We know we have an encoding (otherwise the
    # instruction wouldn't have appeared in the the masks list).
    assert insn.encoding is not None
    enc_vals = insn.encoding.extract_operands(raw)

    # Make sense of these encoded values as "operand values" (doing any
    # shifting, sign interpretation etc.)
    op_vals = insn.enc_vals_to_op_vals(pc, enc_vals)

    # Similarly, we know we have a syntax (again, get_insn_masks requires it).
    # The rendering of the fields is done by the syntax object.
    return match.group(1) + insn.disassemble(pc, op_vals)


def main() -> int:
    args = sys.argv[1:]
    has_disasm = snoop_disasm_flags(args)

    objdump = find_tool('objdump')
    try:
        if not has_disasm:
            cmd = [objdump] + args
            return subprocess.run(cmd).returncode
        else:
            cmd = [objdump, '-M', 'numeric,no-aliases'] + args
            proc = subprocess.run(cmd,
                                  stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE,
                                  universal_newlines=True)
            if proc.returncode:
                # Dump any lines that objdump wrote before it died
                sys.stderr.write(proc.stderr)
                sys.stdout.write(proc.stdout)
                return proc.returncode
    except FileNotFoundError:
        sys.stderr.write('Unknown command: {!r}.\n'
                         .format(objdump))
        return 127

    try:
        insns_file = load_insns_yaml()
    except RuntimeError as err:
        sys.stderr.write('{}\n'.format(err))
        return 1

    # If we get here, we think we're disassembling something, objdump ran
    # successfully and we have its results in proc.stdout
    for line in proc.stdout.split('\n'):
        transformed = transform_disasm_line(line, insns_file)
        sys.stdout.write(transformed + '\n')

    return 0


if __name__ == '__main__':
    sys.exit(main())
