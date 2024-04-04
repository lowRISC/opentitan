/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for a subcomponent of the Miller-Rabin primality test.
 *
 * Testing the test_witness subroutine in isolation can be helpful for
 * debugging and quick feedback.
 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Set number of limbs (n=2).
       x30 <= n
       x31 <= n - 1 */
  li        x30, 2
  li        x31, 1

  /* Test the witness.
       w21 <= all 1s if dmem[input] is possibly prime, otherwise 0 */
  la         x14, witness
  la         x15, tmp
  la         x16, input
  la         x17, mont_m0inv
  la         x18, mont_rr
  jal        x1, test_witness

  /* Load the value from the working buffer into registers. Since the candidate
     is prime and the test should have processed all bits of (w-1) without any
     early exit, we expect that the final value will be equal to
     (witness^(input-1) * R) mod input.
       w0,w1 <= dmem[tmp:tmp+n*32] */
  li         x8, 0
  la         x15, tmp
  loop       x30, 2
    bn.lid     x8, 0(x15++)
    addi       x8, x8, 1

  ecall

.data

/* Candidate prime (true prime, randomly generated using pycryptodome) =
0x8d1c0da1ce6567c69d6bce68028081e582089688137149491c26e47e660463930ea957af990577b9f0cddcbab3a74f47873a9f41a6f40ea9c9c6ca41293edc0b
*/
.balign 32
input:
.word 0x293edc0b
.word 0xc9c6ca41
.word 0xa6f40ea9
.word 0x873a9f41
.word 0xb3a74f47
.word 0xf0cddcba
.word 0x990577b9
.word 0x0ea957af
.word 0x66046393
.word 0x1c26e47e
.word 0x13714949
.word 0x82089688
.word 0x028081e5
.word 0x9d6bce68
.word 0xce6567c6
.word 0x8d1c0da1

/* Random witness for testing. */
.balign 32
witness:
.word 0x4080769c
.word 0x1262ef4d
.word 0x98b11168
.word 0xd0f601d0
.word 0x4387fc64
.word 0x8ab79fd2
.word 0xf7252c67
.word 0xe8a0ed3c
.word 0x72a5ce33
.word 0x082fb7fd
.word 0x9d7863bb
.word 0x80ea393b
.word 0x4e4e9575
.word 0x09455e2a
.word 0x81a24e55
.word 0x256943a7

/* Precomputed Montgomery constant m0' (256 bits). */
.balign 32
mont_m0inv:
.word 0x19b8305d
.word 0x62b7e8e7
.word 0x641931c6
.word 0xd0d2fa8c
.word 0x09f82d11
.word 0xc6fea5cb
.word 0x85db6e31
.word 0x3da16a04

/* Precomputed Montgomery constant RR (512 bits). */
.balign 32
mont_rr:
.word 0x7cace161
.word 0x05dbf569
.word 0x4abf6945
.word 0x67ee4a0e
.word 0x6f17717a
.word 0x403da1b4
.word 0x28cc1d74
.word 0x6424c41f
.word 0xc1edcb01
.word 0x5f4d0e22
.word 0x1e3966f1
.word 0x6be6c4a8
.word 0xc33f14ed
.word 0xc8277904
.word 0x084be9c3
.word 0x2bd6414c

.section .scratchpad

/* Temporary working buffer (512 bits). */
.balign 32
tmp:
.zero 64
