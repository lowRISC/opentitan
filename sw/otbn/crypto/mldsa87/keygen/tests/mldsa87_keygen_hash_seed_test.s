/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that keygen seed Xi hash is correctly hashed. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _hash_seed_xi_share0
  la x3, _hash_seed_xi_share1
  la x4, _hash_seed_rho
  la x5, _hash_seed_rho_prime_share0
  la x6, _hash_seed_rho_prime_share1
  la x7, _hash_seed_k_share0
  la x8, _hash_seed_k_share1
  jal x1, hash_seed

  la x20, _hash_seed_rho_prime_share0
  la x21, _hash_seed_rho_prime_share1
  addi x22, x0, 2
  jal x1, unmask_boolean

  la x20, _hash_seed_k_share0
  la x21, _hash_seed_k_share1
  addi x22, x0, 1
  jal x1, unmask_boolean

  ecall

.data
.balign 32

_hash_seed_xi_share0:
.zero 34
.zero 30 /* Padding */
_hash_seed_xi_share1:
.zero 34
.zero 30 /* Padding */

_hash_seed_rho:
.zero 32
_hash_seed_rho_prime_share0:
.zero 64
_hash_seed_rho_prime_share1:
.zero 64
_hash_seed_k_share0:
.zero 32
_hash_seed_k_share1:
.zero 32

_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* n^-1 * R^3 mod q */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_stack:
.zero 256
