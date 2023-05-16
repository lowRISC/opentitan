/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone tests for SHA-512 hash computation.
 *
 * Based on NIST example (one block message sample):
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf
 *
 * I.e. hash computation for message "abc".
 */

.section .text.start
run_sha512_compact:

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
  jal     x1, sha512_compact

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
  .dword 0x6a09e667f3bcc908
  .balign 32
  .dword 0xbb67ae8584caa73b
  .balign 32
  .dword 0x3c6ef372fe94f82b
  .balign 32
  .dword 0xa54ff53a5f1d36f1
  .balign 32
  .dword 0x510e527fade682d1
  .balign 32
  .dword 0x9b05688c2b3e6c1f
  .balign 32
  .dword 0x1f83d9abfb41bd6b
  .balign 32
  .dword 0x5be0cd19137e2179

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
