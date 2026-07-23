/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Memory layout for ML-KEM-1024 Decryption. */

.data
.balign 32

.globl mlkem1024_decrypt_ct_u
.globl mlkem1024_decrypt_ct_v
.globl mlkem1024_decrypt_sk_s
.globl mlkem1024_decrypt_sk_hpk
.globl mlkem1024_decrypt_sk_z
.globl mlkem1024_decrypt_ss
.globl mlkem1024_const_params

mlkem1024_decrypt_ct_u:
.zero 1408
mlkem1024_decrypt_ct_v:
.zero 160
mlkem1024_decrypt_sk_s:
.zero 1536
mlkem1024_decrypt_sk_hpk:
.zero 32
mlkem1024_decrypt_sk_z:
.zero 32
mlkem1024_decrypt_ss:
.zero 32

/* MOD CSR constants: q = 3329 (0x00000D01), mu = 3327 (0x00000CFF) */
mlkem1024_const_params:
.word 0x00000d01
.word 0x94570cff
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

.globl _compress_recip_m
.globl _compress_offset_1664
.globl _compress_modulus_3329
.globl _decompress_offset_1024
.globl _decompress_offset_16
.globl _decompress_const_1665

_compress_recip_m:
.word 1290168, 0, 1290168, 1290168, 1290168, 1290168, 1290168, 1290168

_compress_offset_1664:
.word 1664, 1664, 1664, 1664, 1664, 1664, 1664, 1664

_compress_modulus_3329:
.word 3329, 0x94570cff, 0, 0, 0, 0, 0, 0

_decompress_offset_1024:
.word 1024, 1024, 1024, 1024, 1024, 1024, 1024, 1024

_decompress_offset_16:
.word 16, 16, 16, 16, 16, 16, 16, 16

_decompress_const_1665:
.word 1665, 1665, 1665, 1665, 1665, 1665, 1665, 1665

.globl stack
stack:
.zero 256

.globl poly_slot0
.globl poly_slot1
.globl poly_slot2
.globl vector_u
.globl vector_s
.globl _seed_buf

.balign 32
.globl keygen_scale_const_2988
keygen_scale_const_2988:
  .rept 32
    .word 2988, 0, 2988, 0, 2988, 0, 2988, 0
  .endr

.section .scratchpad
.balign 32

.globl _expand_buf
_expand_buf:
.zero 512

.globl poly_slot0
poly_slot0:
.zero 1024

poly_slot1:
.zero 1024

poly_slot2:
.zero 1024

vector_u:
.zero 4096

vector_s:
.zero 4096

_seed_buf:
.zero 96
