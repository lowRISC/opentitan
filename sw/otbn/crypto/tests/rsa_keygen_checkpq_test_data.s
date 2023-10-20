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
  not_prime |= 3
  if math.gcd(not_prime, 65537) != 1:
    continue
  if not number.isPrime(not_prime):
    break
 *
 * Hex value for reference:
 * 0xecbbd72477e406de8ff72a93afbe19ed4258d3dd8cfa5b2a8b5c76d22053504710a8460c30c5141fc581df484e58a2bd019c03a1acab6c7fd70f9865ac6dcdcce4cca95266e4d2dea9a408b8ded6591daa4416bb7ca78357cad5c7d527d46a06807337d6845484589c8010eb6b674194608e1b9732db4e8cee053d2572158cf7
 */
.balign 32
.globl not_prime
not_prime:
  .word 0x72158cf7
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
  p |= 3
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
 * 0xd10b3338d7d2cca85be7b76c5497f2fe89a9f9b73e613262565636dbc5901c386b1df3c7b8eb3ac8548a9062a5958b33c84dfe0fa9e2c61250d75683be1585008f926d5cfc4d3a3f003746a3beefcc71d287133768fc0268e1f84cb791be8e6dfc48b706ee0515089ff618c0a648854d6a93e9a0452552e93720ffa2021fd53b
 */
.balign 32
.globl good_p
good_p:
  .word 0x021fd53b
  .word 0x3720ffa2
  .word 0x452552e9
  .word 0x6a93e9a0
  .word 0xa648854d
  .word 0x9ff618c0
  .word 0xee051508
  .word 0xfc48b706
  .word 0x91be8e6d
  .word 0xe1f84cb7
  .word 0x68fc0268
  .word 0xd2871337
  .word 0xbeefcc71
  .word 0x003746a3
  .word 0xfc4d3a3f
  .word 0x8f926d5c
  .word 0xbe158500
  .word 0x50d75683
  .word 0xa9e2c612
  .word 0xc84dfe0f
  .word 0xa5958b33
  .word 0x548a9062
  .word 0xb8eb3ac8
  .word 0x6b1df3c7
  .word 0xc5901c38
  .word 0x565636db
  .word 0x3e613262
  .word 0x89a9f9b7
  .word 0x5497f2fe
  .word 0x5be7b76c
  .word 0xd7d2cca8
  .word 0xd10b3338

/**
 * A value for q that is too close to p, but meets other requirements.
 *
 * Python script for generating test data (using PyCryptoDome's
 * Crypto.Util.number package for the primality check):
while True:
  too_close = random.randrange(p - (1 << 924), p + (1 << 924))
  too_close |= 3
  if too_close < lower_bound:
    continue
  if math.gcd(too_close - 1, 65537) != 1:
    continue
  if number.isPrime(too_close):
    break
 *
 * Hex value for reference:
 * 0xd10b3338d7d2cca85be7b76c479a213a2646058cc86df4e6fb59ec553c4e93bcf9eab3ddcf6caf42e690294667a03e9bc11a94f9b78df5311f5ea7890eb161e7067d759143ff20425120197025aac542ca2cfd1dcfe3ebddeae1f19ece50583c83597856830a0827333d1b67d6d887a16c3f8fe156d119ee6a0b2ca6ba4f62fb
 */
.balign 32
.globl too_close
too_close:
  .word 0xba4f62fb
  .word 0x6a0b2ca6
  .word 0x56d119ee
  .word 0x6c3f8fe1
  .word 0xd6d887a1
  .word 0x333d1b67
  .word 0x830a0827
  .word 0x83597856
  .word 0xce50583c
  .word 0xeae1f19e
  .word 0xcfe3ebdd
  .word 0xca2cfd1d
  .word 0x25aac542
  .word 0x51201970
  .word 0x43ff2042
  .word 0x067d7591
  .word 0x0eb161e7
  .word 0x1f5ea789
  .word 0xb78df531
  .word 0xc11a94f9
  .word 0x67a03e9b
  .word 0xe6902946
  .word 0xcf6caf42
  .word 0xf9eab3dd
  .word 0x3c4e93bc
  .word 0xfb59ec55
  .word 0xc86df4e6
  .word 0x2646058c
  .word 0x479a213a
  .word 0x5be7b76c
  .word 0xd7d2cca8
  .word 0xd10b3338

/**
 * An acceptable value for q.
 *
 * Python script for generating q (using PyCryptoDome's Crypto.Util.number
 * package for the primality check):
while True:
  q = random.randrange(lower_bound, 1 << 1024)
  q |= 3
  if abs(p - q) < (1 << 924):
    continue
  if math.gcd(q-1, 65537) != 1:
    continue
  if number.isPrime(q):
    break
 *
 * Hex value for reference:
 * 0xf83da3592c89b3b8972d1a8dd1de78d7b64a0b1cce4a54ca5125bfc16105ce43ebe4bc6b5e0088e37281d264d2081cf1097671eb3299e91a6c571e4b71cdd1144ca96ad7c45bd05e8e25e371ca8e2043cf73a30ba5e9c979f259bbc9476c1ab3693136e403ebe4e47542c7a6f4164d1a7e2938e65191c9aee6a3534a87c3f1ff
 */
.balign 32
.globl good_q
good_q:
  .word 0x87c3f1ff
  .word 0xe6a3534a
  .word 0x5191c9ae
  .word 0x7e2938e6
  .word 0xf4164d1a
  .word 0x7542c7a6
  .word 0x03ebe4e4
  .word 0x693136e4
  .word 0x476c1ab3
  .word 0xf259bbc9
  .word 0xa5e9c979
  .word 0xcf73a30b
  .word 0xca8e2043
  .word 0x8e25e371
  .word 0xc45bd05e
  .word 0x4ca96ad7
  .word 0x71cdd114
  .word 0x6c571e4b
  .word 0x3299e91a
  .word 0x097671eb
  .word 0xd2081cf1
  .word 0x7281d264
  .word 0x5e0088e3
  .word 0xebe4bc6b
  .word 0x6105ce43
  .word 0x5125bfc1
  .word 0xce4a54ca
  .word 0xb64a0b1c
  .word 0xd1de78d7
  .word 0x972d1a8d
  .word 0x2c89b3b8
  .word 0xf83da359
