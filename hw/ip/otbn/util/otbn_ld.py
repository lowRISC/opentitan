#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''A wrapper around riscv32-unknown-elf-ld for OTBN

This just adds the OTBN linker script and calls the underlying
linker.'''

import os
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from typing import Iterator, List, Optional

from mako import exceptions  # type: ignore
from mako.template import Template  # type: ignore

from shared.mem_layout import get_memory_layout
from shared.toolchain import find_tool


def interpolate_linker_script(in_path: str, out_path: str) -> None:
    mems = get_memory_layout()
    try:
        template = Template(filename=in_path)
        rendered = template.render(imem_lma=mems.imem_address,
                                   imem_length=mems.imem_size_bytes,
                                   dmem_lma=mems.dmem_address,
                                   dmem_length=mems.dmem_size_bytes,
                                   dmem_bus_length=mems.dmem_bus_size_bytes)
    except OSError as err:
        raise RuntimeError(str(err)) from None
    except:  # noqa: 722
        raise RuntimeError(exceptions.text_error_template().render()) from None

    try:
        with open(out_path, 'w') as out_file:
            out_file.write(rendered)
    except FileNotFoundError:
        raise RuntimeError(
            'Failed to open output file at {!r}.'.format(out_path)) from None


@contextmanager
def mk_linker_script() -> Iterator[str]:
    ld_in = os.path.abspath(
        os.path.join(os.path.dirname(__file__), '..', 'data', 'otbn.ld.tpl'))
    with tempfile.TemporaryDirectory(prefix='otbn-ld-') as tmpdir:
        ld_out = os.path.join(tmpdir, 'otbn.ld')
        try:
            interpolate_linker_script(ld_in, ld_out)
        except RuntimeError as err:
            sys.stderr.write(
                'Failed to interpolate linker script: {}\n'.format(err))
            return 1

        yield ld_out


def run_ld(ld_script: Optional[str], args: List[str]) -> int:
    '''Run the underlying linker and return the status code'''
    ld_name = find_tool('ld')
    # The --no-check-sections argument tells ld not to complain when we have
    # more than one section with the same VMA. Since we have a Harvard
    # architecture where data and instructions both start at zero, we expect
    # that to happen.
    cmd = [ld_name, '--no-check-sections']
    if ld_script is not None:
        cmd.append('--script={}'.format(ld_script))
    cmd += args

    try:
        return subprocess.run(cmd).returncode
    except FileNotFoundError:
        sys.stderr.write(
            'Unknown command: {!r}. '
            '(is it installed and on your PATH?)\n'.format(ld_name))
        return 127


def main(argv: List[str]) -> int:
    # Only add the --script argument if the caller isn't supplying one
    # themselves. This argument accumulates (so -T foo -T bar is like
    # concatenating foo and bar), so we mustn't supply our own if the user
    # has one.
    needs_script = True
    for arg in argv[1:]:
        if arg == '-T' or arg.startswith('--script='):
            needs_script = False
            break

    if needs_script:
        with mk_linker_script() as script_path:
            return run_ld(script_path, argv[1:])
    else:
        return run_ld(None, argv[1:])


if __name__ == '__main__':
    sys.exit(main(sys.argv))
