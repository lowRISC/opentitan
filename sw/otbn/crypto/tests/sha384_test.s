/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone tests for SHA-384 hash computation.
 *
 * Based on NIST example (one block message sample):
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA384.pdf
 *
 * I.e. hash computation for message "abc".
 */

.section .text.start
run_sha512:

  /* set number of chunks to process */
  li      x2, 1
  la      x3, n_chunks
  sw      x2, 0(x3)

  /* set pointer to state variables */
  la      x2, init_state
  la      x3, dptr_state
  sw      x2, 0(x3)

  /* set pointer to message */
  la      x2, test_msg
  la      x3, dptr_msg
  sw      x2, 0(x3)

  /* run SHA-512 hashing algorithm */
  jal     x1, sha512

  /* copy back result to WDRs */
  la      x3, dptr_state
  lw      x3, 0(x3)
  li      x2, 0
  loopi   20, 2
    bn.lid  x2, 0(x3++)
    addi    x2, x2, 1

  ecall

.section .data
.globl cfg_data
cfg_data:
.balign 32
init_state:
  /* initial hash values h[0] to h[7]*/
  .dword 0xcbbb9d5dc1059ed8
  .balign 32
  .dword 0x629a292a367cd507
  .balign 32
  .dword 0x9159015a3070dd17
  .balign 32
  .dword 0x152fecd8f70e5939
  .balign 32
  .dword 0x67332667ffc00b31
  .balign 32
  .dword 0x8eb44a8768581511
  .balign 32
  .dword 0xdb0c2e0d64f98fa7
  .balign 32
  .dword 0x47b5481dbefa4fa4

.balign 32
test_msg:
  .dword 0x6162638000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000000
  .dword 0x0000000000000018
