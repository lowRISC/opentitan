/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test runner for ML-KEM-1024 Decryption. */

.globl main

.section .text.start

main:
  la x31, stack
  bn.xor w31, w31, w31

  /* Set MOD CSR with Q = 3329, MU = 0x94570CFF */
  la x2, mlkem1024_const_params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, mlkem1024_decrypt_ct_u
  la x3, mlkem1024_decrypt_ct_v
  la x4, mlkem1024_decrypt_sk_s
  la x5, _seed_buf
  jal x1, mlkem1024_decrypt

  /* Compute derived shared key K' = SHA3-512(m' || hpk, 64)[:32] */
  jal  x1, xof_sha3_512_init
  la   x21, _seed_buf
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  la   x21, mlkem1024_decrypt_sk_hpk
  li   x20, 32
  li   x22, 0
  jal  x1, xof_absorb
  jal  x1, xof_process

  jal  x1, xof_squeeze32
  bn.xor w0, w29, w30
  jal  x1, xof_finish

  la   x3, mlkem1024_decrypt_ss
  bn.sid x0, 0(x3)

  ecall
