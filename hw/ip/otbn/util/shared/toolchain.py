# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os


def find_tool(tool_name: str) -> str:
    '''Return a string describing how to invoke the given RISC-V tool

    Try to resolve the tool in the following way, stopping after the first
    match:

    1. Use the path set in the RV32_TOOL_<tool_name> environment variable.
    2. Use the path set in $TOOLCHAIN_PATH/bin/riscv32-unknown-elf-<tool_name>.
    3. Use riscv32-unknown-elf-<tool_name> and expect it to be in PATH.

    In cases (1) and (2), the file path is checked if it exists, and if not, an
    error message is printed.
    '''
    tool_env_var = 'RV32_TOOL_' + tool_name.upper()
    configured_tool_path = os.environ.get(tool_env_var)
    if configured_tool_path is not None:
        if not os.path.exists(configured_tool_path):
            raise RuntimeError('No such file: {!r} (derived from the '
                               '{!r} environment variable when trying '
                               'to find the {!r} tool).'.format(
                                   configured_tool_path, tool_env_var,
                                   tool_name))
        return configured_tool_path

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
