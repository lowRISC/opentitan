# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A copy of the list of bits in the ERR_BITS register. This also appears in the
# documentation and otbn_pkg.sv: we should probably be generating them from the
# hjson every time.
BAD_DATA_ADDR = 1 << 0
BAD_INSN_ADDR = 1 << 1
CALL_STACK = 1 << 2
ILLEGAL_INSN = 1 << 3
LOOP = 1 << 4
FATAL_IMEM = 1 << 5
FATAL_DMEM = 1 << 6
FATAL_REG = 1 << 7
