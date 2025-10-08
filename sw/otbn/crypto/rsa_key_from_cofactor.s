/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl rsa_key_from_cofactor

/**
 * Construct an RSA key pair from a modulus and cofactor.
 *
 * This routine does not check the validity of the RSA key pair; it does not
 * ensure that the factors are prime or check any other properties, simply
 * divides the modulus by the cofactor and derives the private exponent. The
 * only public exponent supported is e=65537.
 *
 * This routine will recompute the public modulus n after deriving the factors;
 * the caller may want to check that the value matches. If the modulus is not
 * in fact divisible by the cofactor, or the cofactor is much too small, it
 * will not match.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x30: n, number of 256-bit limbs for p and q
 * @param[in]  w31: all-zero
 * @param[in] dmem[rsa_n..rsa_n+(n*2*32)] RSA public key modulus (n)
 * @param[in] dmem[rsa_cofactor..rsa_cofactor+(n*32)] Cofactor (p or q)
 * @param[out] dmem[rsa_n..rsa_n+(n*2*32)] Recomputed public key modulus (n)
 * @param[out] dmem[rsa_d..rsa_d+(n*2*32)] RSA private exponent (d)
 *
 * clobbered registers: x2 to x8, x10 to x15, x20 to x26, x31, w3, w20 to w28
 * clobbered flag groups: FG0, FG1
 */
rsa_key_from_cofactor:
  /* Initialize wide-register pointers.
       x20 <= 20
       x21 <= 21 */
  li       x20, 20
  li       x21, 21

  /* Get a pointer to the middle of the cofactor.
       x2 <= rsa_cofactor + n*32 */
  slli     x2, x30, 5
  la       x3, rsa_cofactor
  add      x2, x2, x3

  # Set the second half of the cofactor buffer to zero, so the cofactor is the
  #    same size as the modulus for division.
  #     dmem[rsa_cofactor+n*32..rsa_cofactor+n*2*32] <= 0
  li       x3, 31
  loop     x30, 1
    bn.sid   x3, 0(x2++)

  /* Update the number of limbs for division.
       x30 <= n*2 */
  add     x30, x30, x30

  /* Compute (n / cofactor) and store the result in `rsa_pq`. The quotient will
     only occupy the first half (`rsa_p`) if the input is valid.
       dmem[rsa_n..rsa_n+n*2*32] <= n % cofactor
       dmem[rsa_pq..rsa_pq+n*2*32] <= n / cofactor */
  la       x10, rsa_n
  la       x11, rsa_cofactor
  la       x12, rsa_pq
  jal      x1, div

  /* Reset the limb count.
       x30 <= (n*2) >> 1 = n */
  srli     x30, x30, 1

  /* Copy the original cofactor into `rsa_q` and compute
     the private exponent.
      dmem[rsa_q..rsa_q+n*32] <= dmem[rsa_cofactor..rsa_cofactor+n*32] */
  la       x11, rsa_cofactor
  la       x2, rsa_q
  li       x3, 3
  loop     x30, 2
    bn.lid   x3, 0(x11++)
    bn.sid   x3, 0(x2++)

  /* Multiply p and q to get the public modulus n.
       dmem[rsa_n..rsa_n+(n*2*32)] <= p * q */
  la       x10, rsa_p
  la       x11, rsa_q
  la       x12, rsa_n
  addi     x31, x30, 0
  jal      x1, bignum_mul

  # Derive the private exponent d from p and q (tail-call).
  jal      x0, derive_d

/**
 * Derive the private RSA exponent d.
 *
 * Returns d = (65537^-1) mod LCM(p-1, q-1).
 *
 * This function overwrites p and q, and requires that they are continuous in
 * memory. Specifically, it expects to be able to use 512 bytes of space
 * following the label `rsa_pq`.
 *
 * Important: This routine uses `rsa_cofactor` as a second 512-byte work buffer
 * and clobbers the contents.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] dmem[rsa_p..rsa_p+(n*32)]: first prime p
 * @param[in] dmem[rsa_q..rsa_q+(n*32)]: second prime q
 * @param[in]  x20: 20, constant
 * @param[in]  x21: 21, constant
 * @param[in]  x30: n, number of 256-bit limbs for p and q
 * @param[in]  w31: all-zero
 * @param[out] dmem[rsa_d..rsa_d+(n*2*32)]: result, private exponent d
 *
 * clobbered registers: x2 to x8, x10 to x15, x20 to x26, x31, w20 to w28
 * clobbered flag groups: FG0, FG1
 */
derive_d:
  /* Load pointers to p, q, and the result buffer. */
  la       x10, rsa_p
  la       x11, rsa_q

  # Subtract 1 from p in-place (no carry from lowest limb since p is odd).
  #      dmem[rsa_p..rsa_p+(n*32)] <= p - 1
  bn.lid   x20, 0(x10)
  bn.subi  w20, w20, 1
  bn.sid   x20, 0(x10)

  /* Subtract 1 from q in-place (no carry from lowest limb since p is odd).
       dmem[rsa_q..rsa_q+(n*32)] <= q - 1 */
  bn.lid   x20, 0(x11)
  bn.subi  w20, w20, 1
  bn.sid   x20, 0(x11)

  /* Compute the LCM of (p-1) and (q-1) and store in the scratchpad.
       dmem[tmp_scratchpad] <= LCM(p-1,q-1) */
  la       x12, tmp_scratchpad
  jal      x1, lcm

  /* Update the number of limbs for modinv.
       x30 <= n*2 */
  add      x30, x30, x30

  /* Compute d = (65537^-1) mod LCM(p-1,q-1). The modular inverse
     routine requires two working buffers, which we construct from
     `rsa_cofactor` and the required-contiguous `rsa_p` and `rsa_q` buffers.
       dmem[rsa_d..rsa_d+(n*2*32)] <= (65537^-1) mod dmem[x12..x12+(n*2*32)] */
  la       x12, tmp_scratchpad
  la       x13, rsa_d0
  la       x14, rsa_cofactor
  la       x15, rsa_pq
  jal      x1, modinv_f4

  # Reset the limb count.
  #      x30 <= (n*2) >> 1 = n
  srli     x30, x30, 1
  ret
