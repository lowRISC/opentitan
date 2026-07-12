/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* ML-KEM-1024 Decapsulation OTBN application (FIPS 203 Algorithm 18 ML-KEM.Decaps_internal / Algorithm 21 ML-KEM.Decaps). */

.globl mlkem1024_decaps

.text

/**
 * ML-KEM-1024 Decapsulation Application Entry Point (ML-KEM.Decaps).
 *
 * Decapsulates ciphertext c = (ct_u || ct_v) using secret key sk = (s || pk || H(pk) || z).
 * Re-encrypts candidate message m' to obtain candidate ciphertext c', performs constant-time
 * comparison c == c', and conditionally selects between K_bar' and K_fail.
 */
mlkem1024_decaps:
  la x31, stack
  bn.xor w31, w31, w31

  /* Set MOD CSR with Q = 3329, MU = 0x94570CFF */
  la x2, mlkem1024_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* 1. Run K-PKE.Decrypt: m' = K-PKE.Decrypt(s, (ct_u || ct_v)) */
  la x2, mlkem1024_decaps_ct_u
  la x3, mlkem1024_decaps_ct_v
  la x4, mlkem1024_decaps_sk_s
  la x5, _seed_buf                    /* output m' at _seed_buf[0..31] */
  jal x1, mlkem1024_decrypt

  /* 2. Compute (K_bar' || r') = SHA3-512(m' || H(ek), 64) into _seed_buf + 32 */
  jal  x1, xof_sha3_512_init
  la   x21, _seed_buf                /* m' is at _seed_buf[0..31] */
  li   x20, 32
  li   x22, 0
  bn.xor w31, w31, w31
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

  /* 3. Re-encrypt: c' = K-PKE.Encrypt(ek, m', r') */
  la x2, mlkem1024_decaps_sk_pk_t
  la x3, mlkem1024_decaps_sk_pk_rho
  la x4, _seed_buf                    /* m' address is _seed_buf[0..31] */
  la x5, _seed_buf
  addi x5, x5, 64                     /* r' address is _seed_buf[64..95] */
  la x6, re_enc_ct_u
  la x7, re_enc_ct_v
  jal x1, mlkem1024_encrypt

  /* 4. Constant-time comparison between input c and re-encrypted c' */
  la x2, mlkem1024_decaps_ct_u
  la x3, re_enc_ct_u
  addi x16, x0, 44
  li   x25, 1
  bn.xor w31, w31, w31
_cmp_ct_u_loop:
  bn.lid x0, 0(x2++)
  bn.lid x25, 0(x3++)
  bn.xor w2, w0, w1
  bn.or  w31, w31, w2
  addi x16, x16, -1
  bne  x16, x0, _cmp_ct_u_loop

  la x2, mlkem1024_decaps_ct_v
  la x3, re_enc_ct_v
  addi x16, x0, 5
_cmp_ct_v_loop:
  bn.lid x0, 0(x2++)
  bn.lid x25, 0(x3++)
  bn.xor w2, w0, w1
  bn.or  w31, w31, w2
  addi x16, x16, -1
  bne  x16, x0, _cmp_ct_v_loop

  /* 5. Compute rejection key K_fail = SHAKE256(z || c, 32) */
  /* Read K_bar' from _seed_buf[32..63] into w10 before KMAC clobbers WDRs */
  la   x2, _seed_buf
  addi x2, x2, 32
  li   x25, 10
  bn.lid x25, 0(x2)                   /* w10 = K_bar' */

  /* Preserve comparison accumulator w31 in w12 before KMAC clobbers w31 */
  bn.mov w12, w31

  jal  x1, xof_shake256_init
  la   x21, mlkem1024_decaps_sk_z
  li   x20, 32
  li   x22, 0
  bn.xor w31, w31, w31
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
     OR bits of w12 into single word x20
  */
  la   x2, poly_slot0
  li   x25, 12
  bn.sid x25, 0(x2)

  /* OR all 8 32-bit words of w12 together into x20 */
  lw    x20, 0(x2)
  addi  x3, x2, 4
  loopi 7, 3
    lw   x21, 0(x3)
    or   x20, x20, x21
    addi x3,  x3, 4
    /* End of loop */

  sub  x21, x0, x20                    /* x21 = -x20 */
  or   x20, x20, x21                   /* x20 = x20 | -x20 (MSB=1 if x20!=0, 0 if x20==0) */
  srai x20, x20, 31                    /* x20 = 0xFFFFFFFF if mismatch, 0 if match */

  /* Fill 32-byte mask into poly_slot0 */
  addi  x3, x2, 0
  loopi 8, 2
    sw   x20, 0(x3)
    addi x3,  x3, 4
    /* End of loop */

  li x25, 20
  bn.lid x25, 0(x2)                   /* w20 = mask */

  /* w0 = (w10 & ~w20) | (w11 & w20) */
  bn.not w21, w20
  bn.and w0, w10, w21
  bn.and w1, w11, w20
  bn.or  w0, w0, w1

  /* Store final shared secret K into mlkem1024_decaps_ss */
  la x3, mlkem1024_decaps_ss
  bn.sid x0, 0(x3)

  ecall
