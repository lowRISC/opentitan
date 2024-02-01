/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Large test for GCD (numbers the size of RSA-3072 cofactors).
 */

.section .text.start

/* Entry point. */
.globl main
main:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Input/output limb count (6). */
  li      x30, 6

  /* dmem[y] <= gcd(dmem[x], dmem[y]) */
  la      x10, x
  la      x11, y
  jal     x1, gcd

  /* Load result into w0 through w5.
       [w0..w5] <= dmem[y] */
  la      x2, y
  li      x3, 0
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2++)
  addi    x3, x3, 1
  bn.lid  x3, 0(x2)

  ecall


.data

/* First input x (6*256 = 1536 bits):

0x69502200a9a8e20c69d4134cde1ad22d5c968df227a2bc1899209a7df07e84599b8e728af15777a2f4723ca730c5ad6c53ced31654a05c39941063e2941d0243b471ee7d76869c490cddf64b705fcb3c0d507cbd6d1b136e363074ac6d9806f6f96798eebeec2c24ab6a72ed5ab03d578bd88bab066c3d112962a488a7000da24700a8f6976338369f5badfd673165a7d6af515d7fddf1b684e48de6ab11e4a70593ac50d04cad2b3e16a7caa878929faad46fe32a0ea6a5cfb4bab23d1743b1
*/
x:
  .word 0x3d1743b1
  .word 0xcfb4bab2
  .word 0x2a0ea6a5
  .word 0xaad46fe3
  .word 0xa878929f
  .word 0x3e16a7ca
  .word 0xd04cad2b
  .word 0x0593ac50
  .word 0xab11e4a7
  .word 0x84e48de6
  .word 0x7fddf1b6
  .word 0xd6af515d
  .word 0x673165a7
  .word 0x9f5badfd
  .word 0x97633836
  .word 0x4700a8f6
  .word 0xa7000da2
  .word 0x2962a488
  .word 0x066c3d11
  .word 0x8bd88bab
  .word 0x5ab03d57
  .word 0xab6a72ed
  .word 0xbeec2c24
  .word 0xf96798ee
  .word 0x6d9806f6
  .word 0x363074ac
  .word 0x6d1b136e
  .word 0x0d507cbd
  .word 0x705fcb3c
  .word 0x0cddf64b
  .word 0x76869c49
  .word 0xb471ee7d
  .word 0x941d0243
  .word 0x941063e2
  .word 0x54a05c39
  .word 0x53ced316
  .word 0x30c5ad6c
  .word 0xf4723ca7
  .word 0xf15777a2
  .word 0x9b8e728a
  .word 0xf07e8459
  .word 0x99209a7d
  .word 0x27a2bc18
  .word 0x5c968df2
  .word 0xde1ad22d
  .word 0x69d4134c
  .word 0xa9a8e20c
  .word 0x69502200

/* Second input y (6 * 256 = 1536 bits):

0x650d63ff6da9e368b23dd056cbd0c35270a00c9bcb6f074cfbda695414aa0d84e2e773057cf1ae4cfd856592690171901147af31c655cbfb3f6907d4f91843b6eb1ad44fe1dde52d3131b4a333f6737c7116231649cf4afa40a44f881c46a3cb85cad497e95cd7b6a54bd7d80cade524a8d599400de21254e91552bb6d0e98afa112512a20edc7674392996b1dec30545844304204ccc909096ef54355f6458714cc3af7d9d3dc7d24758d2904422ac9790b30a69a47f401012ae8478eaaac09
*/
y:
  .word 0x8eaaac09
  .word 0x012ae847
  .word 0x9a47f401
  .word 0x790b30a6
  .word 0x04422ac9
  .word 0x24758d29
  .word 0xd9d3dc7d
  .word 0x14cc3af7
  .word 0x55f64587
  .word 0x096ef543
  .word 0x04ccc909
  .word 0x58443042
  .word 0x1dec3054
  .word 0x4392996b
  .word 0x20edc767
  .word 0xa112512a
  .word 0x6d0e98af
  .word 0xe91552bb
  .word 0x0de21254
  .word 0xa8d59940
  .word 0x0cade524
  .word 0xa54bd7d8
  .word 0xe95cd7b6
  .word 0x85cad497
  .word 0x1c46a3cb
  .word 0x40a44f88
  .word 0x49cf4afa
  .word 0x71162316
  .word 0x33f6737c
  .word 0x3131b4a3
  .word 0xe1dde52d
  .word 0xeb1ad44f
  .word 0xf91843b6
  .word 0x3f6907d4
  .word 0xc655cbfb
  .word 0x1147af31
  .word 0x69017190
  .word 0xfd856592
  .word 0x7cf1ae4c
  .word 0xe2e77305
  .word 0x14aa0d84
  .word 0xfbda6954
  .word 0xcb6f074c
  .word 0x70a00c9b
  .word 0xcbd0c352
  .word 0xb23dd056
  .word 0x6da9e368
  .word 0x650d63ff
