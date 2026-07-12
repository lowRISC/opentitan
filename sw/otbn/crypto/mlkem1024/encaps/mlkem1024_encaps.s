/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-KEM-1024 Encapsulation OTBN application (FIPS 203 Algorithm 17 ML-KEM.Encaps_internal / Algorithm 20 ML-KEM.Encaps). */

.globl mlkem1024_encaps

.text

mlkem1024_encaps:
  jal x1, _encaps
  ecall

/**
 * ML-KEM-1024 Encapsulation Routine (ML-KEM.Encaps).
 *
 * Generates 32-byte shared secret K and ciphertext c = (ct_u || ct_v) from public key ek=(t || rho) and seed m.
 * Computes H(ek), derives (K_bar || r) via SHA3-512, stores shared secret K_bar, and computes ciphertext c.
 */
_encaps:
  la x31, stack
  bn.xor w31, w31, w31

  /* Load MOD CSR with Q = 3329, MU = 0x94570CFF */
  la x2, mlkem1024_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Initialize keygen_scale_const_2988 in DMEM with scalar 16-bit [2988, 0, ...] */
  la    x2, keygen_scale_const_2988
  li    x10, 2988
  loopi 4, 3
    sw   x10, 0(x2)
    sw   x0,  4(x2)
    addi x2,  x2, 8
    /* End of loop */
  la    x2, keygen_scale_const_2988
  addi  x10, x0, 0
  bn.lid x10, 0(x2)
  li    x7, 32
_init_encaps_scale_const_loop:
  bn.sid x10, 0(x2++)
  addi  x7, x7, -1
  bne   x7, x0, _init_encaps_scale_const_loop

  /* 1. Compute H(ek) = SHA3-256(pk_t || pk_rho, 32) into _expand_buf */
  jal  x1, xof_sha3_256_init
  la   x21, mlkem1024_encaps_pk_t
  li   x20, 1536
  li   x22, 0
  jal  x1, xof_absorb
  la   x21, mlkem1024_encaps_pk_rho
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  jal  x1, xof_process

  la   x20, _expand_buf
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20)
  jal  x1, xof_finish

  /* 2. Compute (K_bar || r) = SHA3-512(m || H(ek), 64) into _seed_buf */
  jal  x1, xof_sha3_512_init
  la   x21, mlkem1024_encaps_m
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  la   x21, _expand_buf
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  jal  x1, xof_process

  /* Squeeze 64 bytes into _seed_buf */
  la   x20, _seed_buf
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  jal  x1, xof_finish

  /* Copy K_bar (first 32 bytes of _seed_buf) to mlkem1024_encaps_ss */
  la x2, _seed_buf
  la x3, mlkem1024_encaps_ss
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)

  /* 3. Compute ciphertext (ct_u || ct_v) via K-PKE.Encrypt */
  la x2, mlkem1024_encaps_pk_t
  la x3, mlkem1024_encaps_pk_rho
  la x4, mlkem1024_encaps_m
  la x5, _seed_buf
  addi x5, x5, 32     /* randomness r address */
  la x6, mlkem1024_encaps_ct_u
  la x7, mlkem1024_encaps_ct_v
  jal x1, mlkem1024_encrypt

  ret
