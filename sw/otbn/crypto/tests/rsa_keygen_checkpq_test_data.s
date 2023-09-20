/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Data to test checks on RSA keygen p and q values.
 *
 * See FIPS 186-5 section A.1.3 for the full specification of requirements on p
 * and q. The value for p must satisfy:
 *   - p % 2 = 1
 *   - p >= sqrt(2)*(2^(nlen/2 - 1)), where nlen = RSA public key length
 *   - GCD(p-1,65537) = 1
 *   - p is probably prime
 *
 * For q, we need to satisfy the same requirements as p plus one more: q must
 * not be too close to p.  Specifically, we need to reject the value if:
 *   |p-q| < 2^(nlen/2 - 100).
 *
 * This test data includes values of p and q that each fail exactly one
 * condition, as well as two "good" values of p and q that are compatible with
 * each other.
 *
 * This test data uses 4-limb (1024-bit) values for p and q, which correspond
 * to RSA-2048.
 */

.data

/* Note: Some of the Python scripts shown below reference the lower bound for
   p/q as a Python variable called lower_bound. This value was generated and
   checked for RSA-4096 as specified in BoringSSL:
     https://boringssl.googlesource.com/boringssl/+/dcabfe2d8940529a69e007660fa7bf6c15954ecc/crypto/fipsmodule/rsa/rsa_impl.c#1006

   The value for RSA-2048, as used in these tests, is simply the value for
   RSA-4096 shifted right by 1024 bits. We can check it using:
   >> lower_bound**2 < 2**2047 < (lower_bound+1)**2
   True

   For reference, the hex value of the RSA-2048 lower bound is:
   0xb504f333f9de6484597d89b3754abe9f1d6f60ba893ba84ced17ac85833399154afc83043ab8a2c3a8b1fe6fdc83db390f74a85e439c7b4a780487363dfa2768d2202e8742af1f4e53059c6011bc337bcab1bc911688458a460abc722f7c4e33c6d5a8a38bb7e9dccb2a634331f3c84df52f120f836e582eeaa4a0899040ca4a
*/

/**
 * An odd 1024-bit value that is too small to be used for p or q.
 *
 * Specifically, this value is the highest prime number below the lower bound.
 *
 * Python script for generating the test data (using PyCryptoDome's
 * Crypto.Util.number package for the primality check):
too_small = lower_bound - 1
while True:
  if math.gcd(too_small-1, 65537) != 1:
    continue
  if number.isPrime(too_small):
    break
  too_small -= 2
 *
 * Hex value for reference:
 * 0xb504f333f9de6484597d89b3754abe9f1d6f60ba893ba84ced17ac85833399154afc83043ab8a2c3a8b1fe6fdc83db390f74a85e439c7b4a780487363dfa2768d2202e8742af1f4e53059c6011bc337bcab1bc911688458a460abc722f7c4e33c6d5a8a38bb7e9dccb2a634331f3c84df52f120f836e582eeaa4a0899040c619
 */
.balign 32
.globl too_small
too_small:
  .word 0x9040c619
  .word 0xeaa4a089
  .word 0x836e582e
  .word 0xf52f120f
  .word 0x31f3c84d
  .word 0xcb2a6343
  .word 0x8bb7e9dc
  .word 0xc6d5a8a3
  .word 0x2f7c4e33
  .word 0x460abc72
  .word 0x1688458a
  .word 0xcab1bc91
  .word 0x11bc337b
  .word 0x53059c60
  .word 0x42af1f4e
  .word 0xd2202e87
  .word 0x3dfa2768
  .word 0x78048736
  .word 0x439c7b4a
  .word 0x0f74a85e
  .word 0xdc83db39
  .word 0xa8b1fe6f
  .word 0x3ab8a2c3
  .word 0x4afc8304
  .word 0x83339915
  .word 0xed17ac85
  .word 0x893ba84c
  .word 0x1d6f60ba
  .word 0x754abe9f
  .word 0x597d89b3
  .word 0xf9de6484
  .word 0xb504f333

/**
 * An 1024-bit value that doesn't satisfy relative primality with 65537.
 *
 * This number is selected to be larger than the lower bound and prime, so it
 * doesn't fail any other checks than GCD(p-1,e)=1.
 *
 * Python script for generating the test data (using PyCryptoDome's
 * Crypto.Util.number package for the primality check):
while True:
  y = random.randrange(lower_bound, (1 << 1024))
  y -= (y % 65537)
  if (y & 1 == 0) and number.isPrime(y+1):
    break
not_relprime = y+1
 *
 * Hex value for reference:
 * 0xf36b245b0051285df9f46be79c821a95584a00007b907c4102578d6c8c5d459c4328a174859c703e66bc706a9224e20f387da68e80a362fb1f0f36a912df95c26dc8b40902bff546d3aff671eea79a86df507180e0fba265c0ab601e582580f9fb18a62f9ff4e92d8d698408be08d7c24507244c6d3859be3804f2a7d9f16867
 */
.balign 32
.globl not_relprime
not_relprime:
  .word 0xd9f16867
  .word 0x3804f2a7
  .word 0x6d3859be
  .word 0x4507244c
  .word 0xbe08d7c2
  .word 0x8d698408
  .word 0x9ff4e92d
  .word 0xfb18a62f
  .word 0x582580f9
  .word 0xc0ab601e
  .word 0xe0fba265
  .word 0xdf507180
  .word 0xeea79a86
  .word 0xd3aff671
  .word 0x02bff546
  .word 0x6dc8b409
  .word 0x12df95c2
  .word 0x1f0f36a9
  .word 0x80a362fb
  .word 0x387da68e
  .word 0x9224e20f
  .word 0x66bc706a
  .word 0x859c703e
  .word 0x4328a174
  .word 0x8c5d459c
  .word 0x02578d6c
  .word 0x7b907c41
  .word 0x584a0000
  .word 0x9c821a95
  .word 0xf9f46be7
  .word 0x0051285d
  .word 0xf36b245b

/**
 * An 1024-bit value that passes other checks but isn't prime.
 *
 * Python script for generating the test data (using PyCryptoDome's
 * Crypto.Util.number package for the primality check):
while True:
  not_prime = random.randrange(lower_bound, (1 << 1024))
  not_prime |= 1
  if math.gcd(not_prime, 65537) != 1:
    continue
  if not number.isPrime(not_prime):
    break
 *
 * Hex value for reference:
 * 0xecbbd72477e406de8ff72a93afbe19ed4258d3dd8cfa5b2a8b5c76d22053504710a8460c30c5141fc581df484e58a2bd019c03a1acab6c7fd70f9865ac6dcdcce4cca95266e4d2dea9a408b8ded6591daa4416bb7ca78357cad5c7d527d46a06807337d6845484589c8010eb6b674194608e1b9732db4e8cee053d2572158cf5
 */
.balign 32
.globl not_prime
not_prime:
  .word 0x72158cf5
  .word 0xee053d25
  .word 0x32db4e8c
  .word 0x608e1b97
  .word 0x6b674194
  .word 0x9c8010eb
  .word 0x84548458
  .word 0x807337d6
  .word 0x27d46a06
  .word 0xcad5c7d5
  .word 0x7ca78357
  .word 0xaa4416bb
  .word 0xded6591d
  .word 0xa9a408b8
  .word 0x66e4d2de
  .word 0xe4cca952
  .word 0xac6dcdcc
  .word 0xd70f9865
  .word 0xacab6c7f
  .word 0x019c03a1
  .word 0x4e58a2bd
  .word 0xc581df48
  .word 0x30c5141f
  .word 0x10a8460c
  .word 0x20535047
  .word 0x8b5c76d2
  .word 0x8cfa5b2a
  .word 0x4258d3dd
  .word 0xafbe19ed
  .word 0x8ff72a93
  .word 0x77e406de
  .word 0xecbbd724

/**
 * An acceptable value for p.
 *
 * To make sure the checks on q are being tested, this value is specifically
 * chosen to be far enough away from the "bad" values of q that they wouldn't
 * be rejected on that basis.
 *
 * Python script for generating p (using PyCryptoDome's Crypto.Util.number
 * package for the primality check):
while True:
  p = random.randrange(lower_bound, 1 << 1024)
  p |= 1
  if abs(p - too_small) < (1 << 924):
    continue
  if abs(p - not_relprime) < (1 << 924):
    continue
  if abs(p - not_prime) < (1 << 924):
    continue
  if math.gcd(p-1, 65537) != 1:
    continue
  if number.isPrime(p):
    break
 *
 * Hex value for reference:
 * 0xe85547c5336579f83a2d50a611f489a4f2c3a918d2027fbc3f25c2de2dd36cdedc8901266de144a223b2c78a5a11024488a4aa2f4ef71f0fb93dfdbb2280b4d99dc9b3b77b039fd9fefcc3fe439e2bcb3db3ee3c0378a4d1297c1a5eebcd0d4ab3c0b50eb1511605c7c0907af31564ec5cc635e3de465e99cf6169c933ca0ab5
 */
.balign 32
.globl good_p
good_p:
  .word 0x33ca0ab5
  .word 0xcf6169c9
  .word 0xde465e99
  .word 0x5cc635e3
  .word 0xf31564ec
  .word 0xc7c0907a
  .word 0xb1511605
  .word 0xb3c0b50e
  .word 0xebcd0d4a
  .word 0x297c1a5e
  .word 0x0378a4d1
  .word 0x3db3ee3c
  .word 0x439e2bcb
  .word 0xfefcc3fe
  .word 0x7b039fd9
  .word 0x9dc9b3b7
  .word 0x2280b4d9
  .word 0xb93dfdbb
  .word 0x4ef71f0f
  .word 0x88a4aa2f
  .word 0x5a110244
  .word 0x23b2c78a
  .word 0x6de144a2
  .word 0xdc890126
  .word 0x2dd36cde
  .word 0x3f25c2de
  .word 0xd2027fbc
  .word 0xf2c3a918
  .word 0x11f489a4
  .word 0x3a2d50a6
  .word 0x336579f8
  .word 0xe85547c5

/**
 * A value for q that is too close to p, but meets other requirements.
 *
 * Python script for generating test data (using PyCryptoDome's
 * Crypto.Util.number package for the primality check):
while True:
  too_close = random.randrange(p - (1 << 924), p + (1 << 924))
  if too_close & 1 == 0:
    continue
  if too_close < lower_bound:
    continue
  if math.gcd(too_close - 1, 65537) != 1:
    continue
  if number.isPrime(too_close):
    break
 *
 * Hex value for reference:
 * 0xe85547c5336579f83a2d50a60364d13462f8746c6177f91a902b276464b8c39d0ffeb8d77af899a932ed3198d0d3ca66948d678bf7e95f30e95014fdb0a3b13c56927a70b14191134664a3374ada1d0a3d3dfb0a8fbf3704ef0e8588eafebd9e81f0dca5b7b5cca8b753862a472ed36b8c820c618110ca8936e79789e4ec8b71
 */
.balign 32
.globl too_close
too_close:
  .word 0xe4ec8b71
  .word 0x36e79789
  .word 0x8110ca89
  .word 0x8c820c61
  .word 0x472ed36b
  .word 0xb753862a
  .word 0xb7b5cca8
  .word 0x81f0dca5
  .word 0xeafebd9e
  .word 0xef0e8588
  .word 0x8fbf3704
  .word 0x3d3dfb0a
  .word 0x4ada1d0a
  .word 0x4664a337
  .word 0xb1419113
  .word 0x56927a70
  .word 0xb0a3b13c
  .word 0xe95014fd
  .word 0xf7e95f30
  .word 0x948d678b
  .word 0xd0d3ca66
  .word 0x32ed3198
  .word 0x7af899a9
  .word 0x0ffeb8d7
  .word 0x64b8c39d
  .word 0x902b2764
  .word 0x6177f91a
  .word 0x62f8746c
  .word 0x0364d134
  .word 0x3a2d50a6
  .word 0x336579f8
  .word 0xe85547c5

/**
 * An acceptable value for q.
 *
 * Python script for generating q (using PyCryptoDome's Crypto.Util.number
 * package for the primality check):
while True:
  q = random.randrange(lower_bound, 1 << 1024)
  q |= 1
  if abs(p - q) < (1 << 924):
    continue
  if math.gcd(q-1, 65537) != 1:
    continue
  if number.isPrime(q):
    break
 *
 * Hex value for reference:
 * 0xb863a172d3d5562b582f38e251e540b424d4cbadd5da0ce64cb755227227b9535e0ab2437c1522415a70211eaa1dc4b4192b33148b1226da2ed107b64beeac72b112d99b960df54e21336a13aef97b5ec8646752af38385314a81a531bced7da5a781f6b19d119805941c47777a7aa9580a35b9f75c7dd97545d70790d7e8e9d
 */
.balign 32
.globl good_q
good_q:
  .word 0x0d7e8e9d
  .word 0x545d7079
  .word 0x75c7dd97
  .word 0x80a35b9f
  .word 0x77a7aa95
  .word 0x5941c477
  .word 0x19d11980
  .word 0x5a781f6b
  .word 0x1bced7da
  .word 0x14a81a53
  .word 0xaf383853
  .word 0xc8646752
  .word 0xaef97b5e
  .word 0x21336a13
  .word 0x960df54e
  .word 0xb112d99b
  .word 0x4beeac72
  .word 0x2ed107b6
  .word 0x8b1226da
  .word 0x192b3314
  .word 0xaa1dc4b4
  .word 0x5a70211e
  .word 0x7c152241
  .word 0x5e0ab243
  .word 0x7227b953
  .word 0x4cb75522
  .word 0xd5da0ce6
  .word 0x24d4cbad
  .word 0x51e540b4
  .word 0x582f38e2
  .word 0xd3d5562b
  .word 0xb863a172
