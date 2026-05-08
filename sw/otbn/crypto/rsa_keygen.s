/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

# RSA public and private key generation. The routines in this file are
# structured around `modexp` an make use of pre-defined memory location in
# `run_rsa_mem`.

# RSA key generation is a notoriously slow algorithm due to the probabilistic
# nature of deriving the secret primes that compose the public modulus. By the
# prime number theorem, we know that the distribution of primes approaches
# 1/n for large n-bit numbers, i.e., a random, odd n-bit number (as is generated
# by `gen_prime_candidate`) is prime with probability 2/n, thus on average n/2
# repetitions are necessary until a prime is picked. One half of the composite
# candidates are rejected by the Fermat test while the other half will be
# rejected with high probability by subsequent Miller-Rabin test. This means
# that with probability 1/2 only one exponentiation will be executed and with
# probability 1/2 there will be 2 exponentiations (assuming that the first
# Miller-Rabin exponentiation will reject the composite number), hence on
# average 1.5 exponentiations are executed for each composite number.
# For example, for RSA-2048 the generation of a single 1024-bit prime number
# will result in on average several hundred exponentiations
# (~ 1.5 * (n=1024)/2) with high probability.
#
# Note that a popular way of reducing the number of exponentiations during the
# prime generation consists in performing trial divisions with small prime
# numbers, which efficiently filters out a significant amount of composite
# candidiates before the first exponentiation. It is however not clear how such
# trial division can be implemented without causing leakage on the individual
# bits of the candidate prime.
#
# A running time experiment for a device with a clock frequency of 100 MHz:
#
# 1024-bit exponentiation: 2'770'580 cycles -> ~0.028s
# RSA-2048 key generation: 10-60s (extrapolated from a CW340 at 24MHz).

.text
.globl rsa_keygen
.globl gen_d

# Exposed for testing only.
.globl distance_test

/**
 * Compute the RSA public key (n, e=F4) and secret key (n, d).
 *
 * This implementation of the RSA keygen is compliant with FIPS 186-5.
 *
 * @param[in] x30: n, number of limbs in the modulus and key.
 * @param[out] dmem[rsa_n]: rsa_n, modulus
 * @param[out] dmem[rsa_d0]: rsa_d0, first share of secret exponent
 * @param[out] dmem[rsa_d1]: rsa_d1, second share of secret exponent
 */
rsa_keygen:
  # Temporarily store the limb count in DMEM.
  la x16, nlimbs_tmp
  sw x30, 0(x16)

  # Generate the RSA primes.
  # dmem[rsa_p] <= p.
  # dmem[rsa_q] <= q.
  srl x30, x30, 1
  jal x1, gen_p
  jal x1, gen_q

  # Generate the 512-bit auxiliary primes.
  # dmem[rsa_g] <= g.
  # dmem[rsa_h] <= h.
  li x30, 2
  la x16, rsa_g
  jal x1, gen_prime
  la x16, rsa_h
  jal x1, gen_prime

  # Restore limb count.
  la x16, nlimbs_tmp
  lw x30, 0(x16)

  jal x1, gen_d

  ret

/**
 * Generate the secret key d and the public modulus n.
 *
 * This routine computes d = e^-1 mod LCM(p - 1, q - 1) where the modulus is
 * given by LCM(p - 1, q - 1) = (p - 1) * (q - 1) / gcd(p - 1, q - 1).
 *
 * @param[in] dmem[rsa_p]: RSA prime p
 * @param[in] dmem[rsa_q]: RSA prime q
 * @param[in] dmem[rsa_g]: g, auxiliary 512-bit prime
 * @param[in] dmem[rsa_h]: h, auxiliary 512-bit prime
 * @param[in] x30: n, number of 256-bits limbs in key and modulus
 * @param[in] w31: all-zero
 * @param[out] dmem[rsa_d0..rsa_d0+(n*32)]: d0, first share of d
 * @param[out] dmem[rsa_d1..rsa_d1+(n*32)]: d1, second share of d
 * @param[out] dmem[rsa_n..rsa_n+(n*32)]: n, public modulus
 */
gen_d:
  # Save the limb count.
  addi x27, x30, 0

  # Calculate the n-limbed modulus n.
  # dmem[n] = p * q
  la   x10, rsa_p
  la   x11, rsa_q
  la   x12, rsa_n
  srli x30, x30, 1
  addi x31, x30, 0
  jal  x1, bignum_mul

  li x8, 2

  # dmem[rsa_p] <= p - 1.
  bn.lid  x8, 0(x10)
  bn.subi w2, w2, 1
  bn.sid  x8, 0(x10)

  # dmem[rsa_p] <= q - 1.
  bn.lid  x8, 0(x11)
  bn.subi w2, w2, 1
  bn.sid  x8, 0(x11)

  # dmem[r0] <=  (p - 1) * (q - 1).
  la   x10, rsa_p
  la   x11, rsa_q
  la   x12, r0
  addi x31, x30, 0
  jal  x1, bignum_mul

  # dmem[rsa_g] <= (p - 1) * g
  la x10, rsa_p
  la x11, rsa_g
  la x12, RR
  li x31, 2
  jal x1, bignum_mul

  # Check that gcd(g * (p - 1), F4) == 1.
  la x16, RR
  addi x31, x30, 2
  jal x1, mod_f4

  bn.cmp w22, w31, FG0
  csrrs x16, FG0, x0
  andi x16, x16, 0x8
  bne x16, x0, rsa_keygen

  # dmem[rsa_h] <= (q - 1) * h
  la  x10, rsa_q
  la  x11, rsa_h
  la  x12, work_buf
  li  x31, 2
  jal x1, bignum_mul

  # Check that gcd(h * (q - 1), F4) == 1.
  la x16, work_buf
  addi x31, x30, 2
  jal x1, mod_f4

  bn.cmp w22, w31, FG0
  csrrs x16, FG0, x0
  andi x16, x16, 0x8
  bne x16, x0, rsa_keygen

  # Compute gcd(g * (p - 1), h * (q - 1)).
  # dmem[RR] <= 0.
  # dmem[work_buf] <= gcd(g * (p - 1), h * (q - 1)).
  la   x10, RR
  la   x11, work_buf
  addi x30, x30, 2
  jal  x1, gcd

  # Check that gcd(g * (p - 1), h * (q - 1)) = gcd(p - 1, q - 1) by verifying
  # that 0 < gcd(g * (p - 1), h * (q - 1)) < 2^256. The probability that this
  # check fails is very low, if it does simply restart the entire key
  # generation.
  li x8, 2
  li x9, 3

  # Check that gcd(g * (p - 1), h * (q - 1)) > 0.
  la     x10, work_buf
  bn.lid x8, 0(x10++)
  bn.cmp w2, w31
  csrrs  x2, FG0, x0
  andi   x2, x2, 8
  xori   x2, x2, 8

  # Check that gcd(g * (p - 1), h * (q - 1)) < 2^256.
  addi x31, x30, -1
  loop x31, 5
    bn.lid x8, 0(x10++)
    bn.cmp w2, w31
    csrrs  x3, FG0, x0
    andi   x3, x3, 8
    and    x2, x2, x3

  addi x30, x27, 0
  beq  x2, x0, rsa_keygen

  # For the division (p - 1)*(q - 1)/gcd(p - 1 , q - 1), the denominator
  # gcd(p - 1, q - 1) needs to be inverted modulo 2^256 which requires the
  # removal of even factors in both nominator and denominator.
  # This is not constant-time, however only non-secret values are involved.
_remove_even_factors:

  # Extract the LSB of gcd(p - 1, q - 1).
  # x2 <= gcd(p - 1, q - 1) & 1.
  la   x10, work_buf # (p - 1) * (q - 1)
  la   x11, r0       # gcd(p - 1, q - 1)
  lw   x2, 0(x10)
  andi x2, x2, 1
  # If it the LSB is 1, we are done since the gcd(p - 1, q - 1) is odd.
  bne x2, x0, _remove_even_factors_end

  # The MSB is zero, shift the denominator by one position to right.
  # dmem[work_buf] <= gcd(p - 1, q - 1) >> 1.
  bn.lid  x8, 0(x10)
  bn.rshi w2, w31, w2 >> 1
  bn.sid  x8, 0(x10)

  # Shift the numerator by one position to the right.
  # dmem[work_buf] <= (p - 1) * (q - 1) >> 1.
  addi x31, x30, -1
  addi x12, x11, 32
  loop x31, 4
    bn.lid  x8, 0(x11)
    bn.lid  x9, 0(x12++)
    bn.rshi w2, w3, w2 >> 1
    bn.sid  x8, 0(x11++)

  bn.lid  x8, 0(x11)
  bn.rshi w2, w31, w2 >> 1
  bn.sid  x8, 0(x11)

  # Start from the top to check the next MSB of gcd(p - 1, q - 1).
  beq x0, x0, _remove_even_factors

_remove_even_factors_end:

  # Calculate gcd(p - 1, q - 1)^-1 mod 2^256.
  # w21 <= gcd(p - 1, q - 1)^-1 mod 2^256.
  li x8, 20
  la x10, work_buf
  bn.lid x8, 0(x10)
  jal x1, nr_inv

  # Calculate LCM(p - 1, q - 1) = (p - 1) * (q - 1) / gcd(p - 1, q - 1).
  # dmem[r0] <= LCM(p - 1, q - 1).
  la x16, r0
  jal x1, div_word

  # Calculate the secret key d = e^-1 mod LCM(p - 1, q - 1).
  # dmem[d0] <= d.
  la x24, r0
  la x25, rsa_d0
  la x26, r1
  addi x27, x30, 0
  jal x1, modinv_f4

  # The secret exponent d must not be too small. Make sure that it respects
  # d > 2^(32*n/2), i.e., the upper half of words must be non-zero (see FIPS
  # 186-5 Section A.1.1). The probability that d comes out as too small is
  # exceedingly low.

  # Get a pointer to the second half of d.
  # x3 <= rsa_d0 + 16*n
  slli x2, x30, 4
  la   x3, rsa_d0
  add  x3, x3, x2

  # Check the upper half of words.
  # FG0.Z <= (d >> (n/2*256)) == 0
  bn.mov   w23, w31
  srli     x31, x30, 1
  loop     x31, 2
   bn.lid  x20, 0(x3++)  # w20 <= d[n+i]
   bn.or   w23, w23, w20 # w23 <= w23 | w20

  # If x2 != 0, then d is too small and we need to restart key generation.
  csrrs x2, FG0, x0
  andi  x2, x2, 8
  bne   x2, x0, rsa_keygen

  # Boolean-mask d0 and d1.
  la x12, rsa_d0
  la x13, rsa_d1
  li x8, 2
  li x9, 3
  loop x30, 6
    bn.lid  x8, 0(x12)
    bn.wsrr w3, URND
    bn.xor  w2, w2, w3
    bn.sid  x8, 0(x12++)
    bn.xor  w31, w31, w31 # dummy instruction
    bn.sid  x9, 0(x13++)

  ret

/**
 * Generate n-limbed RSA prime p.
 *
 * Probabilistic prime generation algorithm performing a Fermat test followed
 * by a Miller-Rabin test in accordance with Section A.1.3 of FIPS 186-5 for
 * the usage as the prime p in RSA where gcd(F4, p-1) = 1.
 *
 * This routine is constant-time relative to p if p is possibly prime.
 *
 * @param[in]  x30: n, number of 256-bit limbs in the candidate prime
 * @param[in]  w31: all-zero
 * @param[out] dmem[rsa_p..rsa_p+(n*32)]: result, probable RSA prime p.
 *
 * Clobbered registers: x2 to x27, x31
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * Clobbered flag groups: FG0, FG1
 */
gen_p:
  # Compute nlen, the bit length of the prime.
  # x16 <= n << 8 = n * 256 = nlen
  slli x26, x30, 8

  # Initialize the attempt counter.
  # x26 <= (((x26 << 2) + x26) << 2) = 10 * nlen
  slli x27, x26, 2
  add  x26, x26, x27
  slli x26, x26, 1

_gen_p_loop:
  # Retry the prime generation as long as the attempt counter is non-zero.
  bne x26, x0, _gen_p_body
  unimp

_gen_p_body:
  # Decrement attempt counter.
  addi x26, x26, -1

  # Generate a FIPS-compliant, n-limbed prime candidate p.
  # dmem[n] <= p
  la x16, rsa_n
  jal x1, gen_prime_candidate

  jal x1, fermat_test
  beq x2, x0, _gen_p_loop

  # Set up Miller-Rabin loop counter.
  addi x28, x0, 0

  jal x1, miller_rabin_test
  beq x2, x0, _gen_p_loop

  # Store the number of executed Miller-Rabin rounds in the scratchpad.
  la x29, mr_iter_p_tmp
  sw x28, 0(x29)

  # Move the generate prime into dmem[rsa_p].
  li x8, 2
  la x16, rsa_n
  la x17, rsa_p
  loop x30, 2
    bn.lid x8, 0(x16++)
    bn.sid x8, 0(x17++)

  # If we get here, the check succeeded and p is OK.
  ret

/**
 * Generate n-limbed RSA prime q.
 *
 * Probabilistic prime generation algorithm performing a Fermat test followed
 * by a Miller-Rabin test in accordance with Section A.1.3 of FIPS 186-5 for
 * the usage as the prime q in RSA with gcd(F4, q-1) = 1 and
 * | p - q | > 2^(256*n/2 - 100). This routine must be called after having
 * generated suitable prime p (for example with `gen_p`).
 *
 * This routine is constant-time relative to q if q is possibly prime.
 *
 * @param[in]  dmem[rsa_p]: RSA prime p
 * @param[in]  x30: n, number of 256-bit limbs in the candidate prime
 * @param[in]  w31: all-zero
 * @param[out] dmem[rsa_q..rsa_q+(n*32)]: result, probable RSA prime q
 *
 * Clobbered registers: x2 to x27, x31
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * Clobbered flag groups: FG0, FG1
 */
gen_q:
  # Compute nlen, the bit length of the prime.
  # x16 <= n << 8 = n * 256 = nlen
  slli x26, x30, 8

  # Initialize the attempt counter.
  # x26 <= (((x26 << 2) + x26) << 2) = 10 * nlen
  slli x27, x26, 2
  add  x26, x26, x27
  slli x26, x26, 1

_gen_q_loop:
  # Retry the prime generation as long as the attempt counter is non-zero.
  bne x26, x0, _gen_q_body_outer
  unimp

_gen_q_body_outer:
  # Decrement attempt counter.
  addi x26, x26, -1

_gen_q_body_inner:
  # Generate a FIPS-compliant, n-limbed prime candidate q.
  # dmem[n] <= q
  la x16, rsa_n
  jal x1, gen_prime_candidate

  # Distance test
  jal x1, distance_test
  beq x2, x0, _gen_q_body_inner

  jal x1, fermat_test
  beq x2, x0, _gen_q_loop

  # Set up Miller-Rabin loop counter.
  addi x28, x0, 0

  jal x1, miller_rabin_test
  beq x2, x0, _gen_q_loop

  # Store the number of executed Miller-Rabin rounds in the scratchpad.
  la x29, mr_iter_q_tmp
  sw x28, 0(x29)

  # Move the generate prime into dmem[rsa_q].
  li x8, 2
  la x16, rsa_n
  la x17, rsa_q
  loop x30, 2
    bn.lid x8, 0(x16++)
    bn.sid x8, 0(x17++)

  # If we get here, the check succeeded and p is OK.
  ret

/**
 * Generate n-limbed prime number.
 *
 * Probabilistic prime generation algorithm performing a Fermat test followed
 * by a Miller-Rabin test in accordance with Section A.1.3 of FIPS 186-5.
 *
 * This routine is constant-time relative to p if p is possibly prime.
 *
 * @param[in]  x16: dptr_p: location of the probable prime p in DMEM.
 * @param[in]  x30: n, number of 256-bit limbs in the candidate prime
 * @param[in]  w31: all-zero
 * @param[out] dmem[p..p+(n*32)]: result, probable prime
 *
 * Clobbered registers: x2 to x27, x31
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * Clobbered flag groups: FG0, FG1
 */
gen_prime:
  # Compute nlen, the bit length of the prime.
  # x16 <= n << 8 = n * 256
  slli x26, x30, 8

  # Initialize the attempt counter.
  # x26 <= (((x26 << 2) + x26) << 2) = 10 * nlen
  slli x27, x26, 2
  add  x26, x26, x27
  slli x26, x26, 1

  addi x27, x16, 0

_gen_prime_loop:
  # Retry the prime generation as long as the attempt counter is non-zero. The
  # probability that the counter reaches is exceedingly low.
  bne x26, x0, _gen_prime_body
  unimp

_gen_prime_body:
  # Decrement attempt counter.
  addi x26, x26, -1

  # Generate a FIPS-186-5-compliant, n-limbed prime candidate p.
  # dmem[n] <= p
  la x16, rsa_n
  jal x1, gen_prime_candidate

  # Compute both Fermat and Miller-Rabin test.
  jal x1, fermat_test
  beq x2, x0, _gen_prime_loop

  jal x1, miller_rabin_test
  beq x2, x0, _gen_prime_loop

  # Move the generate prime into dmem[x16].
  li   x8, 2
  la   x16, rsa_n
  addi x17, x27, 0
  loop x30, 2
    bn.lid x8, 0(x16++)
    bn.sid x8, 0(x17++)

  # At this point, we have generated a probable prime.
  ret

/**
 * Check that the generated primes p and q have a large enough distance.
 *
 * FIPS 186-5 requires | p - q | > 2^(256*n/2 - 100). For simplicity, q is
 * assumed to reside in DMEM[n] as is the case the beginning of the generation
 * of q.
 *
 * @param[in] DMEM[rsa_p]: prime p
 * @param[in] DMEM[n]: prime q
 * @param[in] x30: N, number of limbs of the prime
 * @param[in] w31: all-zero
 * @param[out] x2: result, 1 if w^(p-1) = 1 mod p else 0.
 *
 * Clobbered registers: x7, x8, x20, x21, w20, w21, w22, w23
 * Clobbered flag groups: FG0, FG1
 */
distance_test:
  # Clear flags for both groups.
  bn.sub w31, w31, w31, FG0
  bn.sub w31, w31, w31, FG1

  # Constant wide register pointers.
  li x20, 20
  li x21, 21

  # Compute the last limbs of (p-q) and (q-p).
  # w22 <= (p - q) mod (2^(256*n)) >> (256*(n-1))
  # w23 <= (q - p) mod (2^(256*n)) >> (256*(n-1))
  la   x7, rsa_p
  la   x8, rsa_n
  loop x30, 4
    bn.lid  x20, 0(x7++)       # w20 <= p[i]
    bn.lid  x21, 0(x8++)       # w21 <= q[i]
    bn.subb w22, w20, w21, FG0 # w22, FG0.C <= p[i] - q[i] - FG0.C
    bn.subb w23, w21, w20, FG1 # w23, FG1.C <= q[i] - p[i] - FG1.C

  # If p < q, then FG0.C will be set. Use the flag to select the last limb
  # that matches |p-q|.
  # w20 <= FG0.C ? w23 : w22 = (p - q) ? (q - p)[n-1] : (p - q)[n-1]
  bn.sel w20, w23, w22, FG0.C

  # Get the highest 100 bits of |p - q|.
  # w20 <= w20 >> 156 = |p-q| >> (256*n - 100)
  bn.rshi w20, w31, w20 >> 156

  # Check if the highest 100 bits are 0 (we will need to fail if so).
  # FG0.Z <= (w20 == 0)
  bn.addi w20, w20, 0

  # Get the FG0.Z flag into a register.
  # x2 <= CSRs[FG0] & 8 = FG0.Z << 3
  csrrs x2, FG0, x0
  andi  x2, x2, 8
  srli  x2, x2, 3
  xori  x2, x2, 1
  ret

/**
 * Calculate x^-1 mod 2^256, for x < x^256 and x % 2 == 1.
 *
 * This function computes the inversion of a single 256-bit word modulo 2^256
 * using the Newton-Raphson algorithm.
 *
 * The key identity is the follwing:
 *
 *   x * y = 1 mod 2^k ==> x * y * (2 - x * y) mod 2^(2 * k)
 *
 * Hence by setting k = y = 1, we can invert x in 8 iterations with 2
 * multiplications and 1 subtraction per iteration.

 * @param[in]  w20: x, an odd value to be inverted modulo 2^256
 * @param[int] w31: all-zero
 * @param[out] w21: y, the result y = x^-1 mod 2^256
 *
 * Clobbered registers: w22, w23, w24, w25, w26, w27
 * Clobbered flag groups: FG0
 */
nr_inv:

  # We compute the following algorithm:
  #
  # w21 = y = 1
  # w22 = x
  # w23 = 2
  # for i = 0 to 7 do
  #     [w27, w26] = w21 * w22 = x * y
  #     w26 = w23 - w26 = 2 - x * y
  #     [w27, w26] = w21 * 26 = x * (2 - x * y)
  #     w21 = w26
  # endfor
  # return w21

  # w21 = y = 1
  # w22 = x
  # w23 = 2
  bn.addi w21, w31, 1
  bn.mov  w22, w20
  bn.addi w23, w31, 2

  loopi 8, 8
    # x * y
    bn.mov w24, w21
    bn.mov w25, w22
    jal x1, mul256_w24xw25

    # 2 - x * y.
    bn.sub w26, w23, w26

    # x * (2 - x * y)
    bn.mov w24, w21
    bn.mov w25, w26
    jal x1, mul256_w24xw25
    bn.mov w21, w26

  ret

/**
 * Unrolled 512=256x256 bit multiplication.
 *
 * Returns c = a * b.
 *
 * Flags: No flags are set in this subroutine.
 *
 * @param[in] w24: a, first operand
 * @param[in] w25: b, second operand
 * @param[out] [w26, w27]: c, result
 *
 * clobbered registers: w26, w27
 * clobbered flag groups: None
 */
mul256_w24xw25:
  bn.mulqacc.z          w24.0, w25.0,  0
  bn.mulqacc            w24.1, w25.0, 64
  bn.mulqacc.so  w26.L, w24.0, w25.1, 64
  bn.mulqacc            w24.2, w25.0,  0
  bn.mulqacc            w24.1, w25.1,  0
  bn.mulqacc            w24.0, w25.2,  0
  bn.mulqacc            w24.3, w25.0, 64
  bn.mulqacc            w24.2, w25.1, 64
  bn.mulqacc            w24.1, w25.2, 64
  bn.mulqacc.so  w26.U, w24.0, w25.3, 64
  bn.mulqacc            w24.3, w25.1,  0
  bn.mulqacc            w24.2, w25.2,  0
  bn.mulqacc            w24.1, w25.3,  0
  bn.mulqacc            w24.3, w25.2, 64
  bn.mulqacc.so  w27.L, w24.2, w25.3, 64
  bn.mulqacc.so  w27.U, w24.3, w25.3,  0
  ret
