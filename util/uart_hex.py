#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""A small utility to convert hex strings to uart_write_imm calls."""

import ast
import sys

s = sys.argv[1]
s = ast.literal_eval("b'''" + s + "'''")
for i in range(0, len(s), 8):
    value = int.from_bytes(s[i: i + 8], "little")
    print(f'uart_write_imm(0x{value:016x});')
