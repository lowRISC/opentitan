# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os


def find_tool(tool_name: str) -> str:
    '''Return a string describing how to invoke the given RISC-V tool

    If TOOLCHAIN_PATH is not set, we resolve FOO to riscv32-unknown-elf-FOO
    (which will be searched for on $PATH). If it is set, we resolve foo to
    $TOOLCHAIN_PATH/bin/riscv32-unknown-elf-FOO.

    In the latter case, we also do a sanity check that the file exists. This
    allows us to print a more helpful error if it doesn't (saying we were
    looking at TOOLCHAIN_PATH).

    '''
    expanded = 'riscv32-unknown-elf-' + tool_name
    toolchain_path = os.environ.get('TOOLCHAIN_PATH')
    if toolchain_path is None:
        return expanded

    tool_path = os.path.join(toolchain_path, 'bin', expanded)
    if not os.path.exists(tool_path):
        raise RuntimeError('No such file: {!r} (derived from the '
                           'TOOLCHAIN_PATH environment variable when trying '
                           'to find the {!r} tool).'
                           .format(tool_path, tool_name))

    return tool_path
