/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Randomizable sha3-{224,256,384,512} test.
 *
 * The following buffers are generated separately by the test infrastructure:
 *   dst_len: {28,32,48,64} output bytes --> choose SHA3 mode
 *   msg    : input message
 *   msg_len: input message's length
 */

.section .text.start
main:
  /* Init all-zero register */
  bn.xor  w31, w31, w31

  /* Start SHA3 */
  la      x10, context
  la      x11, dst_len
  lw      x11, 0(x11)
  jal     x1, sha3_init

  la      x10, context
  la      x11, msg
  la      x12, msg_len
  lw      x12, 0(x12)
  jal     x1, sha3_update

  la      x10, context
  la      x11, dst
  jal     x1, sha3_final

  /* Load results into WDRs */
  la      x2, dst
  li      x3, 0
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2)

  ecall

.data
.balign 32

context:
  .balign 32
  .zero 212

.balign 32
dst:
  .zero 64

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
