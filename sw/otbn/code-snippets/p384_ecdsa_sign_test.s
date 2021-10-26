/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 ECDSA signature generation
 *
 * Computes P-384 ECDSA signature for message, nonce and private key
 * contained in the .data section.
 *
 * See comment at the end of the file for expected values of signature.
 */

.section .text.start

p384_ecdsa_sign_test:

  /* set dmem pointer to nonce k */
  la       x2, nonce_k
  la       x3, dptr_k
  sw       x2, 0(x3)

  /* set dmem pointer to point to blinding parameter */
  la       x2, blinding_param
  la       x3, dptr_rnd
  sw       x2, 0(x3)

  /* set dmem pointer to point to message */
  la       x2, msg
  la       x3, dptr_msg
  sw       x2, 0(x3)

  /* set dmem pointer to point to nonce k */
  la       x2, nonce_k
  la       x3, dptr_k
  sw       x2, 0(x3)

  /* set dmem pointer to point to private key d */
  la       x2, priv_key_d
  la       x3, dptr_d
  sw       x2, 0(x3)

  /* set dmem pointer to point to signature */
  la       x2, sig_r
  la       x3, dptr_r
  sw       x2, 0(x3)
  la       x2, sig_s
  la       x3, dptr_s
  sw       x2, 0(x3)

  /* call ECDSA signing subroutine in P-384 lib */
  jal      x1, p384_sign

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, sig_r
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)
  li        x2, 2
  la        x3, sig_s
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall


.data

/* nonce k */
nonce_k:
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .word 0x99999999
  .zero 16

/* blinding parameter rnd */
 blinding_param:
  .word 0xa82c85b0
  .word 0x163ce1c8
  .word 0x32518fd7
  .word 0xf8a428cd
  .word 0xf5b9d867
  .word 0x00906f5f
  .word 0x7387b4f2
  .word 0xa2d3da7a
  .word 0xebe0a647
  .word 0xfb2ef7ca
  .word 0x74249432
  .word 0x230e5ff6
  .zero 16

/* message */
msg:
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .word 0x55555555
  .zero 16

/* private key d */
priv_key_d:
  .word 0xe8791ba3
  .word 0xf549e1f7
  .word 0x893be358
  .word 0x100794fe
  .word 0xbc9db95d
  .word 0xfd7ed624
  .word 0xc60ebab6
  .word 0x97ba9586
  .word 0xa026b431
  .word 0x37112316
  .word 0x8b26eef1
  .word 0xc1a0cf66
  .zero 16

/* signature R */
sig_r:
  .zero 64

/* signature S */
sig_s:
  .zero 64


/* Expected values in wide register file (x- and y-coordinates of result):
   [w1, w0] is R; [w3, w2] is S.
 w0  = 0x49d29eef0235d77ec16c09de12d35b3856e186cf9a1a30fc2b23ce3ab68c28d8
 w1  = 0x00000000000000000000000000000000b2fcf95c7c0d8125b45990dbd3c43053
 w2  = 0x80eb391d3e7f68950016f9c3a78101eb77e415a198144c27752042f524bc1bf9
 w3  = 0x000000000000000000000000000000001a72ebdde34d88c1fa9554e0f19a653d
*/
