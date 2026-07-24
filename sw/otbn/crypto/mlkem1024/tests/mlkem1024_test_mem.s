/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Memory buffers for unit testing ML-KEM-1024 subroutines. */

.data
.balign 32

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

.globl _stack
_stack:
.zero 256

.section .scratchpad
.balign 32

.globl _expand_buf
_expand_buf:
  .zero 512
