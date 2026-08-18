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
 * ML-KEM-1024 Encapsulation Routine (FIPS 203 Algorithm 20 ML-KEM.Encaps / Algorithm 17 ML-KEM.Encaps_internal).
 *
 * Generates 32-byte shared secret K and ciphertext c = (ct_u || ct_v) from public key ek=(t || rho) and seed m.
 * Computes H(ek), derives (K_bar || r) via SHA3-512, stores shared secret K_bar, and computes ciphertext c via K-PKE.Encrypt.
 */
_encaps:
  la x31, stack
  bn.xor w31, w31, w31

  /* Load MOD CSR with Q = 3329, MU = 0x94570CFF */
  la x2, mlkem1024_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  /* Verify that all 1,024 coefficients of pk_t are < q = 3329 (FIPS 203 Section 7.2) */
  la   x14, mlkem1024_encaps_pk_t
  bn.xor w27, w27, w27            /* w27 accumulates overflow sign bits */
  la     x2, mlkem1024_const_3328_vec
  li     x20, 28
  bn.lid x20, 0(x2)               /* w28 = [3328, 3328, ..., 3328] */

  la     x15, poly_slot2
  loopi 4, 10
    addi x2, x14, 0
    addi x3, x15, 0               /* 1-inst copy: x3 = poly_slot2 */
    jal  x1, decode_12
    addi x2, x15, 0               /* 1-inst copy: x2 = poly_slot2 */
    loopi 32, 4
      bn.lid x0, 0(x2++)
      bn.subv.8S w0, w28, w0      /* w0[k] = 3328 - t_i */
      bn.shv.8S  w0, w0 >> 31     /* MSB is 1 if t_i >= 3329, 0 if t_i <= 3328 */
      bn.or      w27, w27, w0     /* OR overflow bits into w27 */
    addi x14, x14, 384
    /* End of loop */

  bn.cmp w27, w31, FG0            /* Check if w27 == 0 */
  csrrs  x2, FG0, x0
  andi   x2, x2, 8                /* Extract Z (zero) bit (bit 3): 8 if w1 == 0, 0 if w1 != 0 */
  bne    x2, x0, _pk_bounds_ok

  /* Overflow detected (t_i >= 3329): write 0xc5618e4b to mlkem1024_encaps_res_ok and return to ecall */
  la   x2, mlkem1024_encaps_res_ok
  li   x3, 0xc5618e4b
  sw   x3, 0(x2)
  ret

_pk_bounds_ok:
  /* Write 0x3a9e71b4 (OK) to mlkem1024_encaps_res_ok */
  la   x2, mlkem1024_encaps_res_ok
  li   x3, 0x3a9e71b4
  sw   x3, 0(x2)

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
  addi x8, x0, 0     /* x8 = 0: compressed mode */
  jal x1, mlkem1024_encrypt

  ret
