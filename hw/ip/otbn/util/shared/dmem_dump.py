# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import struct
from typing import Dict

from hw.ip.otbn.util.shared.mem_layout import get_memory_layout

_DMEM_RE = re.compile(
    r'\s*(?P<label>[a-zA-Z0-9_]+)\s*:\s*(?P<val>(:?[0-9a-f]+))$')


def parse_dmem_exp(dump: str) -> Dict[str, int]:
    '''Parse the expected dmem.

    Format:
        label: hex_data

    Returns a dictionary mapping labels to the expected bytes.
    '''

    out = {}
    for line in dump.split('\n'):
        # Remove comments and ignore blank lines.
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        m = _DMEM_RE.match(line)
        if not m:
            raise ValueError(f'Failed to parse dmem dump line ({line}).')
        label = m.group('label')
        value = bytes.fromhex(m.group('val'))

        if label in out:
            raise ValueError(f'DMEM dump contains multiple values '
                             f'for {label}.')
        out[label] = value

    return out


def parse_actual_dmem(dump: bytes) -> bytes:
    '''Parse the dmem dump.

    Returns the dmem bytes except integrity info.
    '''
    dmem_bytes = []
    # 8 32-bit data words + 1 byte integrity info per word = 40 bytes
    bytes_w_integrity = 8 * 4 + 8
    for w in struct.iter_unpack(f"<{bytes_w_integrity}s", dump):
        tmp = []
        # discard byte indicating integrity status
        for v in struct.iter_unpack("<BI", w[0]):
            tmp += [x for x in struct.unpack("4B", v[1].to_bytes(4, "big"))]
        dmem_bytes += tmp
    assert len(dmem_bytes) == get_memory_layout().dmem_size_bytes
    return bytes(dmem_bytes)
