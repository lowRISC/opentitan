/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

# OTBN Smoke test, runs various instructions which are expected to produce the
# final register state see in smoke_expected.txt

# x1 = 0xd0beb513
lui x1, 0xd0beb
add x1, x1, 0x513
# x2 = 0xa0be911a
lui x2, 0xa0be9
add x2, x2, 0x11a

# x3 = x1 + x2 = 0x717d462d
add x3, x1, x2

# x4 = x2 - x1 = 0xcfffdc07
sub x4, x2, x1

# x5 = x1 | x2 = 0xf0beb51b
or x5, x1, x2

# x6 = x1 & x2 = 0x80be9112
and x6, x1, x2

# x7 = x1 ^ x2 = 0x70002409
xor x7, x1, x2

# x8 = x1 | 0x123 = 0xd0beb533
or x8, x1, 0x123

# x9 = x1 & 0x7bc = 0x510
and x9, x1, 0x7bc

# x10 = x1 ^ 0x47a = 0xd0beb169
xor x10, x1, 0x47a

# x11 = x1 << 10 = 0xfad44c00
sll x11, x1, 10

# x12 = x1 >> 13 = 0x685f5
srl x12, x1, 13

# x13 = x1 >>> 7 =  0xffa17d6a
sra x13, x1, 7

# x14 = x1 << x2[4:0] = 0x4c000000
sll x14, x1, x2

# x15 = x1 >> x2[4:0] = 0x34
srl x15, x1, x2

# x16 = x1 >>> x2[4:0] = 0xfffffff4
sra x16, x1, x2

ecall
