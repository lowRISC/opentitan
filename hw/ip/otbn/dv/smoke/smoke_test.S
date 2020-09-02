/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

# OTBN Smoke test, runs various instructions which are expected to produce the
# final register state see in smoke_expected.txt

.section .text

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

# x17 = dmem[16] = 0xfacefeed
lw x17, 16(x0)

# dmem[4] = x8 = 0xd0beb533
sw x8, 4(x0)

# x18 = dmem[4] = 0xd0beb533
lw x18, 4(x0)

# x19 = 0
li x19, 0

bne x18, x17, test_label_1

# x19 = 0xbaad (shouldn't happen due to branch)
li x19, 0xbaad

test_label_1:

# x19 = x19 + 0x123 = 0x123
add x19, x19, 0x123

jal x0, test_label_2

# x19 = x19 + 0x123 = 0x246 (shouldn't happen due to jump)
add x19, x19, 0x123

test_label_2:

# x20 = x19 + x0 = 0123
add x20, x19, x0

beq x19, x20, test_label_3

# x20 = x20 + 0x123 = 0x246 (shouldn't happen due to branch)
add x20, x20, 0x123

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
  li x21, 0xcafef00d
  jalr x0, x31, 0

.section .data
.word 0x1234abcd
.word 0xbaadf00d
.word 0xcafed00d
.word 0xdeadbeef
.word 0xfacefeed
