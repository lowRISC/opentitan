/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-KEM-1024 Decapsulation OTBN application (FIPS 203 Algorithm 18 ML-KEM.Decaps_internal / Algorithm 21 ML-KEM.Decaps). */

.globl mlkem1024_decaps

.text

/**
 * ML-KEM-1024 Decapsulation Application Entry Point (FIPS 203 Algorithm 21 ML-KEM.Decaps / Algorithm 18 ML-KEM.Decaps_internal).
 *
 * Decapsulates ciphertext c = (ct_u || ct_v) using secret key sk = (s || pk || H(pk) || z).
 * Re-encrypts candidate message m' via K-PKE.Encrypt to obtain candidate ciphertext c', performs constant-time
 * 256-bit comparison of c == c', and conditionally selects shared secret K = (c == c') ? K_bar' : K_fail.
 */
mlkem1024_decaps:
  la x31, stack

  /* Set MOD CSR with Q = 3329, MU = 0x94570CFF */
  la x2, mlkem1024_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* 1. Run K-PKE.Decrypt: m' = K-PKE.Decrypt(s, (ct_u || ct_v)) */
  la x2, mlkem1024_decaps_ct_u
  la x3, mlkem1024_decaps_ct_v
  la x4, mlkem1024_decaps_sk_s_share0
  la x5, _seed_buf                    /* output m' at _seed_buf[0..31] */
  jal x1, mlkem1024_decrypt

  /* 2. Compute (K' || r') = SHA3-512(m' || H(ek), 64) into _seed_buf + 32 */
  jal  x1, xof_sha3_512_init
  la   x21, _seed_buf                /* m' is at _seed_buf[0..31] */
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  la   x21, mlkem1024_decaps_sk_hpk   /* H(ek) */
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  jal  x1, xof_process

  /* Squeeze 64 bytes into _seed_buf + 32 (K_bar' at +32, r' at +64) */
  la   x20, _seed_buf
  addi x20, x20, 32
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x20++)
  jal  x1, xof_finish

  /* 3. Re-encrypt: uncompressed c' = (u' || v') = K-PKE.Encrypt(ek, m', r') */
  la   x2, mlkem1024_decaps_sk_pk_t
  la   x3, mlkem1024_decaps_sk_pk_rho
  la   x4, _seed_buf                  /* m' address is _seed_buf[0..31] */
  la   x5, _seed_buf
  addi x5, x5, 64                     /* r' address is _seed_buf[64..95] */
  la   x6, re_enc_u
  la   x7, re_enc_v
  jal  x1, mlkem1024_encrypt_uncompressed

  /* 4. Constant-time comparison between input c and re-encrypted uncompressed c' */
  bn.xor w12, w12, w12                /* w12 = overall mismatch accumulator */

  /* Compare candidate u' against input ct_u (4 polynomials) */
  la x14, re_enc_u
  la x15, mlkem1024_decaps_ct_u
  loopi 4, 24
    /* Copy re_enc_u[i] (1024 bytes) into poly_slot1 for scratch compression */
    addi x2, x14, 0
    la   x3, poly_slot1
    loopi 32, 2
      bn.lid x0, 0(x2++)
      bn.sid x0, 0(x3++)

    /* Compress poly_slot1 into poly_slot0 (352 bytes) */
    la   x2, poly_slot1
    la   x3, poly_slot0
    jal  x1, compress_11

    /* Compare poly_slot0 (11 WDRs) against mlkem1024_decaps_ct_u + i * 352 */
    la   x2, poly_slot0
    addi x3, x15, 0
    li   x25, 1
    bn.xor w11, w11, w11
    loopi 11, 4
      bn.lid x0, 0(x2++)
      bn.lid x25, 0(x3++)
      bn.xor w2, w0, w1
      bn.or  w11, w11, w2
      /* End of loop */

    /* Accumulate mismatch into w12 */
    bn.or w12, w12, w11

    addi x14, x14, 1024
    addi x15, x15, 352
    /* End of loop */

  /* Compare candidate v' against input ct_v (1 polynomial) */
  /* Copy re_enc_v (1024 bytes) into poly_slot1 */
  la x2, re_enc_v
  la x3, poly_slot1
  loopi 32, 2
    bn.lid x0, 0(x2++)
    bn.sid x0, 0(x3++)

  /* Compress poly_slot1 into poly_slot0 (160 bytes) */
  la x2, poly_slot1
  la x3, poly_slot0
  jal x1, compress_5

  /* Compare poly_slot0 (5 WDRs) against mlkem1024_decaps_ct_v */
  la x2, poly_slot0
  la x3, mlkem1024_decaps_ct_v
  li x25, 1
  bn.xor w11, w11, w11
  loopi 5, 4
    bn.lid x0, 0(x2++)
    bn.lid x25, 0(x3++)
    bn.xor w2, w0, w1
    bn.or  w11, w11, w2
    /* End of loop */

  /* Accumulate final mismatch into w12 */
  bn.or w12, w12, w11

  /* 5. Compute rejection key K_fail = SHAKE256(z || c, 32) */
  jal  x1, xof_shake256_init
  la   x21, mlkem1024_decaps_sk_z_share0
  la   x22, mlkem1024_decaps_sk_z_share1
  li   x20, 32
  jal  x1, xof_absorb
  la   x21, mlkem1024_decaps_ct_u
  li   x20, 1408
  li   x22, 0
  jal  x1, xof_absorb
  la   x21, mlkem1024_decaps_ct_v
  li   x20, 160
  li   x22, 0
  jal  x1, xof_absorb
  jal  x1, xof_process

  jal  x1, xof_squeeze32
  bn.xor w11, w29, w30                /* w11 = K_fail */
  jal  x1, xof_finish

  /* Constant-time select:
     OR all 8 32-bit words of w12 together into x20
  */
  la   x2, poly_slot0
  li   x25, 12
  bn.sid x25, 0(x2)

  lw    x20, 0(x2)
  addi  x3, x2, 4
  loopi 7, 3
    lw   x21, 0(x3)
    or   x20, x20, x21
    addi x3,  x3, 4
    /* End of loop */

  /* Read K_bar' from _seed_buf[32..63] into w10 */
  la   x2, _seed_buf
  addi x2, x2, 32
  li   x25, 10
  bn.lid x25, 0(x2)                   /* w10 = K_bar' */

  /* Select: if x20 == 0 (match), select w10 (K_bar'); else select w11 (K_fail) */
  bn.mov w0, w10
  beq   x20, x0, _decaps_select_done
  bn.mov w0, w11
_decaps_select_done:

  /* Store final shared secret K into mlkem1024_decaps_ss */
  la x3, mlkem1024_decaps_ss
  bn.sid x0, 0(x3)

  ecall
