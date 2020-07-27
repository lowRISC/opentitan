// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// python util/otbnsim/test/programs.py -Ocarray -s random >
// sw/device/examples/hello_otbn/program_random.h
static const uint32_t code[] = {
    0x00000213,  // addi x4, x0, 0
    0x0000420b,  // bn.lid x4, 0(x0)
    0x00100213,  // addi x4, x0, 1
    0x0040420b,  // bn.lid x4, 1(x0)
    0x00200213,  // addi x4, x0, 2
    0x0080420b,  // bn.lid x4, 2(x0)
    0x00300213,  // addi x4, x0, 3
    0x00c0420b,  // bn.lid x4, 3(x0)
    0x00000293,  // addi x5, x0, 0
    0x00600313,  // addi x6, x0, 6
    0x8052f2ab,  // bn.xor w5, w5, w5
    0x005072ab,  // bn.not w5, w5
    0x0020127b,  // loopi 4, 2
    0x0022f30b,  // bn.wsrrs w6, w5, 2
    0x8013628b,  // bn.movr x5+, x6
    0x00000213,  // addi x4, x0, 0
    0x0000520b,  // bn.sid x4, 0(x0)
    0x00100213,  // addi x4, x0, 1
    0x0040520b,  // bn.sid x4, 1(x0)
    0x00200213,  // addi x4, x0, 2
    0x0080520b,  // bn.sid x4, 2(x0)
    0x00300213,  // addi x4, x0, 3
    0x00c0520b,  // bn.sid x4, 3(x0)
};
