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


/* expected values
 w0  = 0xf25db4aed5ee31684be79cc019abdd20c380bab56599365cddaf35a193617aba
 w1  = 0xa9ee356ad969da206d0f63f8cce4e8c0c85aedf9e5797653cc417349ae204131
 w2  = 0xf1f076584e7bf62e73210a803211fbee495d95f5c8270f5412e6fa4e89a97ea2
 w3  = 0xca171fdb59f51065f670b675db34a2a042c537d8c90b4a540a9eeee64b55d39a
 w4  = 0x040d950918cee3e8c64b83ac9769c581dcdb92a27dcd45ca2192992a274fc1a8
 w5  = 0x1380dd9fabdcd2fa89f32bdf5fba052b4b66931766e4642c36ba3c23a3feebbd
 w6  = 0xc4dc3dbb6e74ce2233c09dc4c707c22272fc4a221e3157ee454d4423643ce80e
 w7  = 0xb3ee255e1fd3d4211d086c56c8ad7ad6964e089287f6b31d2a9ac94fa54ca49f
 */
