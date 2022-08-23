# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re

from typing import Dict

_REG_RE = re.compile(r'\s*([a-zA-Z0-9_]+)\s*=\s*((:?0x[0-9a-f]+)|([0-9]+))$')


def parse_reg_dump(dump: str) -> Dict[str, int]:
    '''Parse the output from a register dump.

    Expects all non-empty lines of the dump to be in the form <name> = <value>,
    e.g.
      x0 = 0x00000000
      x1 = 0x11111111
      ...

    Registers may appear in any order and values may be hexadecimal or decimal
    integers. Comments use '#'; any content in a line following '#' will be
    ignored.

    Returns a dictionary mapping register names to their integer values.
    '''

    out = {}
    for line in dump.split('\n'):
        # Remove comments and ignore blank lines.
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        m = _REG_RE.match(line)
        if not m:
            raise ValueError(f'Failed to parse reg dump line ({line:!r}).')
        reg = m.group(1)
        value = int(m.group(2), 0)

        if reg in out:
            raise ValueError(f'Register dump contains multiple values '
                             f'for {reg}.')
        out[reg] = value

    return out
