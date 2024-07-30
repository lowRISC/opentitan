/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone tests for SHA-3 hash computation.
 */

.section .text.start
run_sha3:
  /* Load stack pointer */
  la x2, stack_end

  /* SHA3-224, corner case with 0-length message */

  la x10, context
  li x11, 28 /* mdlen */
  jal x1, sha3_init

  la x10, context
  la x11, test_msg_256_32
  li x12, 0 /* msglen */
  jal x1, sha3_update

  la x10, context
  la x11, test_dst_224
  jal x1, sha3_final

  /* SHA3-256, short message */

  la x10, context
  li x11, 32 /* mdlen */
  jal x1, sha3_init

  la x10, context
  la x11, test_msg_256_32
  li x12, 32 /* msglen */
  jal x1, sha3_update

  la x10, context
  la x11, test_dst_256
  jal x1, sha3_final

  /* SHA3-384, exact block size */

  la x10, context
  li x11, 48 /* mdlen */
  jal x1, sha3_init

  la x10, context
  la x11, test_msg_384_104
  li x12, 104 /* msglen */
  jal x1, sha3_update

  la x10, context
  la x11, test_dst_384
  jal x1, sha3_final

  /* SHA3-512, multiblock message */

  la x10, context
  li x11, 64 /* mdlen */
  jal x1, sha3_init

  la x10, context
  la x11, test_msg_512_255
  li x12, 255 /* msglen */
  jal x1, sha3_update

  la x10, context
  la x11, test_dst_512
  jal x1, sha3_final

/* SHAKE */

/* SHAKE 128 */

  /* SHAKE 128, 0 */
  la x10, context
  li x11, 16 /* mdlen */
  jal x1, sha3_init

  la x10, context
  jal x1, shake_xof

  la x8, context
  la x9, test_dst_shake_128_0
  LOOPI 16, 5
    addi x10, x8, 0
    addi x11, x9, 0
    addi x12, zero, 32
    jal x1, shake_out
    nop

  /* SHAKE 128, message */
  la x10, context
  li x11, 16 /* mdlen */
  jal x1, sha3_init

  la x10, context
  la x11, test_msg_shake
  li x12, 20

  LOOPI 10, 2
    jal x1, sha3_update
    nop

  la x10, context
  jal x1, shake_xof

  la x8, context
  la x9, test_dst_shake_128_1
  LOOPI 16, 5
    addi x10, x8, 0
    addi x11, x9, 0
    addi x12, zero, 32
    jal x1, shake_out
    nop

/* SHAKE 256 */

  /* SHAKE 256, 0 */
  la x10, context
  li x11, 32 /* mdlen */
  jal x1, sha3_init

  la x10, context
  jal x1, shake_xof

  la x8, context
  la x9, test_dst_shake_256_0
  LOOPI 16, 5
    addi x10, x8, 0
    addi x11, x9, 0
    addi x12, zero, 32
    jal x1, shake_out
    nop

  /* SHAKE 256, message */
  la x10, context
  li x11, 32 /* mdlen */
  jal x1, sha3_init

  la x10, context
  la x11, test_msg_shake
  li x12, 20

  LOOPI 10, 2
    jal x1, sha3_update
    nop

  la x10, context
  jal x1, shake_xof

  la x8, context
  la x9, test_dst_shake_256_1
  LOOPI 16, 5
    addi x10, x8, 0
    addi x11, x9, 0
    addi x12, zero, 32
    jal x1, shake_out
    nop

  la x10, test_dst_224
  li x11, 0
  bn.lid x11, 0(x10)

  la x10, test_dst_256
  li x11, 1
  bn.lid x11, 0(x10)

  la x10, test_dst_384
  li x11, 2
  bn.lid x11, 0(x10++)
  li x11, 3
  bn.lid x11, 0(x10)

  la x10, test_dst_512
  li x11, 4
  bn.lid x11, 0(x10++)
  li x11, 5
  bn.lid x11, 0(x10)

  la x10, test_dst_shake_128_0
  li x11, 6
  bn.lid x11, 0(x10)

  la x10, test_dst_shake_128_1
  li x11, 7
  bn.lid x11, 0(x10)

  la x10, test_dst_shake_256_0
  li x11, 8
  bn.lid x11, 0(x10)

  la x10, test_dst_shake_256_1
  li x11, 9
  bn.lid x11, 0(x10)

  ecall

.section .data

.balign 32
test_dst_224:
  .zero 28

.balign 32
test_dst_256:
  .zero 32

.balign 32
test_dst_384:
  .zero 48

.balign 32
test_dst_512:
  .zero 64

.balign 32
test_dst_shake_128_0:
  .zero 32

.balign 32
test_dst_shake_128_1:
  .zero 32

.balign 32
test_dst_shake_256_0:
  .zero 32

.balign 32
test_dst_shake_256_1:
  .zero 32

.global context
context:
.balign 32
.zero 212

.globl rc
.balign 32
rc:
  .balign 32
  .dword 0x0000000000000001
  .balign 32
  .dword 0x0000000000008082
  .balign 32
  .dword 0x800000000000808a
  .balign 32
  .dword 0x8000000080008000
  .balign 32
  .dword 0x000000000000808b
  .balign 32
  .dword 0x0000000080000001
  .balign 32
  .dword 0x8000000080008081
  .balign 32
  .dword 0x8000000000008009
  .balign 32
  .dword 0x000000000000008a
  .balign 32
  .dword 0x0000000000000088
  .balign 32
  .dword 0x0000000080008009
  .balign 32
  .dword 0x000000008000000a
  .balign 32
  .dword 0x000000008000808b
  .balign 32
  .dword 0x800000000000008b
  .balign 32
  .dword 0x8000000000008089
  .balign 32
  .dword 0x8000000000008003
  .balign 32
  .dword 0x8000000000008002
  .balign 32
  .dword 0x8000000000000080
  .balign 32
  .dword 0x000000000000800a
  .balign 32
  .dword 0x800000008000000a
  .balign 32
  .dword 0x8000000080008081
  .balign 32
  .dword 0x8000000000008080
  .balign 32
  .dword 0x0000000080000001
  .balign 32
  .dword 0x8000000080008008

.balign 32
test_msg_256_32:
  /* SHA3-256, short message, len 32 */
  .dword 0x0D09DE907CCC2F9F
  .dword 0xEAC118977ECD876B
  .dword 0xE95D2DFC1811B26C
  .dword 0x109C1EACB65D7EF9

.balign 32
test_msg_384_104:
  /* SHA3-384, exact block size, len 104 */
  .dword 0x4CAD9997EB8057E3
  .dword 0xF33C68DB4D5D5377
  .dword 0x4CCF27537167F33E
  .dword 0x86D4CDBD9CED584A
  .dword 0xA949D58901F869F6
  .dword 0x5426A5512AA84F36
  .dword 0xCE5DB9AAB31B72EC
  .dword 0x6D8293FA6A6AA8B4
  .dword 0xE3338F927E5123B9
  .dword 0x83EF6056D450A8FB
  .dword 0x98A9A2AFCC6A87B9
  .dword 0x0A146E7C134B257A
  .dword 0x48384169101E6921

.balign 32
test_msg_512_255:
  /* SHA3-512, multiblock message, len 255 */
  .dword 0x2ADEEF489C813A3A
  .dword 0x6BAB180EF0FB14D9
  .dword 0xC1D027AB1345F1C4
  .dword 0xF5E73114B688A178
  .dword 0x756734236BB63C62
  .dword 0x3A492C980EB586D3
  .dword 0x83D33C9A4BC5BFDB
  .dword 0x0A15B2A0A1362338
  .dword 0x18AE036D338F3515
  .dword 0xFDC4553D57C766F6
  .dword 0x3EE6FDCCE6291C18
  .dword 0xC0CF8558DF0A5FA3
  .dword 0x44D24D2E2B4AD8A3
  .dword 0xCE7031669E78DB96
  .dword 0x57D4BC1BAA9847F7
  .dword 0x64D78904A4BBA04E
  .dword 0x8B146BC6AD3AF8B2
  .dword 0xD527C14652D90C4A
  .dword 0xA5908641114F1C87
  .dword 0x430AC8A04612F0DD
  .dword 0xDC393618B68800C7
  .dword 0xF4A813D15B12A4FD
  .dword 0x57ACFA06D33EE29E
  .dword 0x1D6756E2C1B03F6C
  .dword 0xB4F5524A53C27F81
  .dword 0xF476E34D422EF739
  .dword 0x9EDD0723A8CC65C5
  .dword 0x087EEBC4B7A56DF7
  .dword 0xD0027C8028E37251
  .dword 0xD778537833BFFF11
  .dword 0xB06BBEA5F666C29D
  .dword 0xB1AEEBCE2EA9E4

.balign 32
test_msg_shake:
  .dword 0xA3A3A3A3A3A3A3A3
  .dword 0xA3A3A3A3A3A3A3A3
  .dword 0xA3A3A3A3

  .zero 512
stack_end:
  .zero 1
