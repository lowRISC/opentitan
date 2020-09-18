/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

# OTBN Smoke test, runs various instructions which are expected to produce the
# final register state see in smoke_expected.txt

.section .text

# x2 = 0xd0beb513
lui x2, 0xd0beb
add x2, x2, 0x513
# x3 = 0xa0be911a
lui x3, 0xa0be9
add x3, x3, 0x11a

# x4 = x2 + x3 = 0x717d462d
add x4, x2, x3

# x5 = x3 - x2 = 0xcfffdc07
sub x5, x3, x2

# x6 = x2 | x3 = 0xf0beb51b
or x6, x2, x3

# x7 = x2 & x3 = 0x80be9112
and x7, x2, x3

# x8 = x2 ^ x3 = 0x70002409
xor x8, x2, x3

# x9 = x2 | 0x123 = 0xd0beb533
or x9, x2, 0x123

# x10 = x2 & 0x7bc = 0x510
and x10, x2, 0x7bc

# x11 = x2 ^ 0x47a = 0xd0beb169
xor x11, x2, 0x47a

# x12 = x2 << 10 = 0xfad44c00
sll x12, x2, 10

# x13 = x2 >> 13 = 0x685f5
srl x13, x2, 13

# x14 = x2 >>> 7 =  0xffa17d6a
sra x14, x2, 7

# x15 = x2 << x3[4:0] = 0x4c000000
sll x15, x2, x3

# x16 = x2 >> x3[4:0] = 0x34
srl x16, x2, x3

# x17 = x2 >>> x3[4:0] = 0xfffffff4
sra x17, x2, x3

# x18 = dmem[16] = 0xfacefeed
lw x18, 16(x0)

# dmem[4] = x9 = 0xd0beb533
sw x9, 4(x0)

# x19 = dmem[4] = 0xd0beb533
lw x19, 4(x0)

# x20 = 0
li x20, 0

bne x19, x18, test_label_1

# x20 = 0xbaad (shouldn't happen due to branch)
li x20, 0xbaad

test_label_1:

# x20 = x20 + 0x123 = 0x123
add x20, x20, 0x123

jal x1, test_label_2

# x20 = x20 + 0x123 = 0x246 (shouldn't happen due to jump)
add x20, x20, 0x123

test_label_2:

# x21 = x20 + x0 = 0123
add x21, x20, x0

beq x20, x21, test_label_3

# x21 = x21 + 0x123 = 0x246 (shouldn't happen due to branch)
add x21, x21, 0x123

test_label_3:

jal x0, end

# Place end at fixed address so write to x31 by jal doesn't have changing value
# as more is added to smoke test
.org 0x800
end:

# x31 = 0x804
jal x31, test_fn

ecall

test_fn:
  # x21 = 0xcafef00d
  li x22, 0xcafef00d
  jalr x0, x31, 0

.section .data
.word 0x1234abcd
.word 0xbaadf00d
.word 0xcafed00d
.word 0xdeadbeef
.word 0xfacefeed
