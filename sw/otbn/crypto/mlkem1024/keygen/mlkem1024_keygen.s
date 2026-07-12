/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-KEM-1024 Key Generation OTBN application (FIPS 203 Algorithm 16 ML-KEM.KeyGen_internal / Algorithm 19 ML-KEM.KeyGen). */

.globl mlkem1024_keygen

.text

mlkem1024_keygen:
  jal x1, _keygen
  ecall

/**
 * ML-KEM-1024 Key Generation Routine (FIPS 203 Algorithm 19 ML-KEM.KeyGen / Algorithm 16 ML-KEM.KeyGen_internal).
 *
 * Generates public key pk = (ByteEncode_12(t_hat) || rho) [1568 bytes] and
 * secret key sk = (ByteEncode_12(s_hat) || pk || H(pk) || z) [3168 bytes].
 * In random mode, samples d and z from RND. In deterministic mode, uses DMEM seed shares.
 * Computes (rho || sigma) = G(d || 0x04), samples s and e via SamplePolyCBD_eta (eta = 2),
 * transforms s and e to NTT domain s_hat and e_hat, expands matrix A = SampleNTT(rho),
 * computes t_hat = A * s_hat + e_hat in NTT domain, and stores packed outputs to DMEM.
 */
_keygen:
  la x31, stack
  bn.xor w31, w31, w31

  /* Load the ML-KEM constants into MOD CSR register */
  la x2, mlkem1024_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Initialize keygen_scale_const_2988 in DMEM with constant 2988 (0x0bac) */
  la     x2, const_2988_wdr
  addi   x10, x0, 0
  bn.lid x10, 0(x2)
  la     x2, keygen_scale_const_2988
  loopi  32, 1
    bn.sid x10, 0(x2++)
    /* End of loop */

  /* Mode identifiers */
  li x2, 0x5514edb7 /* Random */
  li x3, 0xfaacd725 /* Deterministic */

  la x4, mlkem1024_keygen_mode
  lw x7, 0(x4)

  beq x3, x7, _keygen_seed_ready
  bne x2, x7, _keygen_fault

  /* Random mode: Sample seed d_share0, d_share1, seed_z_share0, and seed_z_share1 from RND */
  la x5, mlkem1024_keygen_seed_d_share0
  la x6, mlkem1024_keygen_seed_d_share1
  la x10, mlkem1024_keygen_seed_z_share0
  la x11, mlkem1024_keygen_seed_z_share1

  bn.wsrr w0, RND
  bn.sid  x0, 0(x5)
  bn.wsrr w0, RND
  bn.sid  x0, 0(x6)
  bn.wsrr w0, RND
  bn.sid  x0, 0(x10)
  bn.wsrr w0, RND
  bn.sid  x0, 0(x11)

_keygen_seed_ready:
  /* (rho || sigma) = SHA3-512(d_share0 ^ d_share1 || 0x04) */
  la   x21, mlkem1024_keygen_seed_d_share0
  li   x20, 4
  sw   x20, 32(x21)

  jal  x1, xof_sha3_512_init
  addi x20, x0, 33
  la   x21, mlkem1024_keygen_seed_d_share0
  la   x22, mlkem1024_keygen_seed_d_share1
  jal  x1, xof_absorb
  jal  x1, xof_process

  la   x20, _seed_buf
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  jal  x1, xof_finish

  /* Copy 32-byte rho to output DMEM using WDR load/store */
  la   x2, _seed_buf
  la   x3, mlkem1024_keygen_pk_rho
  addi x5, x0, 0
  bn.lid x5, 0(x2)
  bn.sid x5, 0(x3)

  /* Sample s[0..3], convert to NTT domain s_hat[0..3], encode into sk_s_share0,
   * and pre-scale to Montgomery domain in poly_slot_s_hat */
  la   x15, mlkem1024_keygen_sk_s_share0
  la   x14, poly_slot_s_hat
  addi x16, x0, 0     /* j = 0 */
  addi x17, x0, 4

_keygen_sample_s_loop:
  la   x2, _seed_buf
  addi x2, x2, 32     /* sigma address */
  la   x4, poly_slot0
  addi x3, x16, 0     /* N = j */
  jal  x1, expand_prf

  /* Transform s[j] in poly_slot0 to NTT domain s_hat[j] */
  la   x2, poly_slot0
  la   x3, poly_slot0
  jal  x1, ntt

  /* Encode standard NTT domain s_hat[j] into sk_s + j * 384 */
  la   x2, poly_slot0
  addi x3, x15, 0
  jal  x1, encode_12

  /* Scale s_hat[j] in poly_slot0 to Montgomery domain (s_hat[j] * R mod q) and store in poly_slot_s_hat + j * 1024 */
  la   x2, poly_slot0
  la   x3, keygen_scale_const_2988
  la   x4, _basemul_twiddles
  addi x5, x14, 0
  jal  x1, poly_mul

  addi x14, x14, 1024
  addi x15, x15, 384
  addi x16, x16, 1
  bne  x16, x17, _keygen_sample_s_loop

  /* Matrix-Vector Product t = A * s + e (4x4 matrix) */
  li   x18, 0     /* i = 0 (row counter) */

_keygen_row_loop:
  /* Sample e[i] into poly_slot0 and transform to NTT domain */
  la   x2, _seed_buf
  addi x2, x2, 32     /* sigma address */
  la   x4, poly_slot0
  addi x3, x18, 4     /* N = 4 + i */
  jal  x1, expand_prf

  la   x2, poly_slot0
  la   x3, poly_slot0
  jal  x1, ntt

  /* Inner column loop: accumulate A[i][j] * s_hat[j] into poly_slot0 (which holds e_hat[i]) */
  li   x19, 0     /* j = 0 (col counter) */

_keygen_col_loop:
  la   x2, mlkem1024_keygen_pk_rho
  addi x3, x19, 0   /* j */
  addi x4, x18, 0   /* i */
  la   x5, poly_slot2
  jal  x1, expand_a

  /* poly_slot2 (A[i][j]) * poly_slot_s_hat[j] + poly_slot0 (accumulator) -> poly_slot0 */
  la   x2, poly_slot2
  la   x3, poly_slot_s_hat
  slli x7, x19, 10    /* j * 1024 */
  add  x3, x3, x7
  la   x4, _basemul_twiddles
  la   x5, poly_slot0
  la   x6, poly_slot0
  jal  x1, poly_mul_add

  addi x19, x19, 1
  li   x7, 4
  bne  x19, x7, _keygen_col_loop

  /* poly_slot0 now holds t_hat[i] in NTT domain. Encode t_hat[i] into pk_t + i * 384 */
  la   x2, poly_slot0
  la   x3, mlkem1024_keygen_pk_t
  slli x7, x18, 8     /* i * 256 */
  add  x3, x3, x7
  slli x7, x18, 7     /* i * 128 */
  add  x3, x3, x7    /* x3 = pk_t + i * 384 */
  jal  x1, encode_12

  addi x18, x18, 1
  li   x7, 4
  bne  x18, x7, _keygen_row_loop

  /* Copy pk_t (1536 bytes) to sk_pk_t */
  la   x2, mlkem1024_keygen_pk_t
  la   x3, mlkem1024_keygen_sk_pk_t
  loopi 48, 2
    bn.lid x0, 0(x2++)
    bn.sid x0, 0(x3++)
    /* End of loop */

  /* Copy pk_rho (32 bytes) to sk_pk_rho */
  la   x2, mlkem1024_keygen_pk_rho
  la   x3, mlkem1024_keygen_sk_pk_rho
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)

  /* Compute H(pk) = SHA3-256(pk_t || pk_rho, 1568 bytes) -> sk_hpk */
  jal  x1, xof_sha3_256_init
  li   x20, 1536
  la   x21, mlkem1024_keygen_pk_t
  li   x22, 0
  jal  x1, xof_absorb
  li   x20, 32
  la   x21, mlkem1024_keygen_pk_rho
  li   x22, 0
  jal  x1, xof_absorb
  jal  x1, xof_process

  la   x20, mlkem1024_keygen_sk_hpk
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20)
  jal  x1, xof_finish

  /* Copy seed_z_share0 -> sk_z_share0 and seed_z_share1 -> sk_z_share1 */
  la   x2, mlkem1024_keygen_seed_z_share0
  la   x3, mlkem1024_keygen_sk_z_share0
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)

  la   x2, mlkem1024_keygen_seed_z_share1
  la   x3, mlkem1024_keygen_sk_z_share1
  bn.lid x0, 0(x2)
  bn.sid x0, 0(x3)

  ret

  unimp
_keygen_fault:
  unimp
  unimp
  unimp
