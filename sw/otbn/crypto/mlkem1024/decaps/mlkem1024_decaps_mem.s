/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Memory layout for ML-KEM-1024 Decapsulation. */

.data
.balign 32

.globl mlkem1024_decaps_ct_u
.globl mlkem1024_decaps_ct_v
.globl mlkem1024_decaps_sk_s_share0
.globl mlkem1024_decaps_sk_s_share1
.globl mlkem1024_decaps_sk_pk_t
.globl mlkem1024_decaps_sk_pk_rho
.globl mlkem1024_decaps_sk_hpk
.globl mlkem1024_decaps_sk_z_share0
.globl mlkem1024_decaps_sk_z_share1
.globl mlkem1024_decaps_ss
.globl mlkem1024_const_params

mlkem1024_decaps_ct_u:
.zero 1408
mlkem1024_decaps_ct_v:
.zero 160
mlkem1024_decaps_sk_s_share0:
.zero 1536

mlkem1024_decaps_sk_s_share1:
.zero 1536
mlkem1024_decaps_sk_pk_t:
.zero 1536
mlkem1024_decaps_sk_pk_rho:
.zero 64
mlkem1024_decaps_sk_hpk:
.zero 32
mlkem1024_decaps_sk_z_share0:
.zero 32

mlkem1024_decaps_sk_z_share1:
.zero 32
mlkem1024_decaps_ss:
.zero 32

/* MOD CSR constants: q = 3329 (0x00000D01), mu = 0x94570CFF */
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
.globl _decompress_const_1665

_compress_recip_m:
.word 1290168, 0, 1290168, 1290168, 1290168, 1290168, 1290168, 1290168

_compress_offset_1664:
.word 1664, 1664, 1664, 1664, 1664, 1664, 1664, 1664

_compress_modulus_3329:
.word 3329, 0x94570cff, 0, 0, 0, 0, 0, 0

_decompress_const_1665:
.word 1665, 1665, 1665, 1665, 1665, 1665, 1665, 1665

.balign 32
.globl const_2988_wdr
const_2988_wdr:
.word 0x00000bac, 0x00000000, 0x00000bac, 0x00000000, 0x00000bac, 0x00000000, 0x00000bac, 0x00000000

.globl stack
stack:
.zero 256

.globl poly_slot_y_hat

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
.zero 672

.globl poly_slot0
poly_slot0:
.zero 1024

.globl poly_slot1
poly_slot1:
.zero 1024

.globl poly_slot2
poly_slot2:
.zero 1024

.globl poly_slot_y_hat
poly_slot_y_hat:
.zero 4096

.globl vector_u
.globl re_enc_v
re_enc_v:
vector_u:
.zero 4096

.globl vector_s
.globl re_enc_u
re_enc_u:
vector_s:
.zero 4096

.globl _seed_buf
_seed_buf:
.zero 128
