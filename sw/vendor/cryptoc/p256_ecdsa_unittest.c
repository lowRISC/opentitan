// Copyright 2016 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <ctype.h>

#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/obj_mac.h>

#include "cryptoc/p256.h"
#include "cryptoc/p256_ecdsa.h"
#include "cryptoc/p256_prng.h"

// Turn p256 point into ossl compatible binary array.
// Returns # total bytes.
static int to_oct(const p256_int* x, const p256_int* y, uint8_t* buf) {
  buf[0] = 4;
  p256_to_bin(x, buf + 1);
  p256_to_bin(y, buf + 1 + 32);
  return 65;
}

// Turn p256 r,s into ossl compatible signature array.
// r and s are encoded as mpi ints:
//  - leading zeros are stripped.
//  - if high bit is set, a leading zero is added (i.e. positive numbers only).
// Returns # total bytes.
static int to_sig(const p256_int* r, const p256_int* s, uint8_t* buf) {
  uint8_t* p = buf;
  uint8_t tmp_r[32 + 1], tmp_s[32 + 1];
  int size_r = sizeof(tmp_r), size_s = sizeof(tmp_s);
  int i;

  tmp_r[0] = 0;
  p256_to_bin(r, tmp_r + 1);
  tmp_s[0] = 0;
  p256_to_bin(s, tmp_s + 1);

  for (i = 0; !tmp_r[i] && i < sizeof(tmp_r); ++i) --size_r;
  if (tmp_r[i] & 0x80) ++size_r;
  for (i = 0; !tmp_s[i] && i < sizeof(tmp_s); ++i) --size_s;
  if (tmp_s[i] & 0x80) ++size_s;

  *p++ = 0x30;  // sequence tag
  *p++ = 2 + size_r + 2 + size_s;

  *p++ = 0x02;  // int tag
  *p++ = size_r;
  memcpy(p, &tmp_r[sizeof(tmp_r) - size_r], size_r);
  p += size_r;

  *p++ = 0x02;  // int tag
  *p++ = size_s;
  memcpy(p, &tmp_s[sizeof(tmp_s) - size_s], size_s);
  p += size_s;

  return p - buf;
}

// Load public key into openssl and verify signature on message.
// Returns 0 on fail.
static int ossl_verify(const p256_int* Gx, const p256_int* Gy,
                       uint8_t* message,
                       const p256_int* r, const p256_int* s) {
  int result = 0;

  uint8_t pk[65];
  uint8_t sig[72];

  int siglen, pklen;

  EC_KEY* key = EC_KEY_new();
  EC_GROUP* group = EC_GROUP_new_by_curve_name(NID_X9_62_prime256v1);
  EC_POINT* point = EC_POINT_new(group);

  EC_KEY_set_group(key, group);

  pklen = to_oct(Gx, Gy, pk);

  EC_POINT_oct2point(group, point, pk, pklen, 0);
  EC_KEY_set_public_key(key, point);

  siglen = to_sig(r, s, sig);

  result = (ECDSA_verify(0, message, 32, sig, siglen, key) == 1);

  EC_POINT_free(point);
  EC_GROUP_free(group);
  EC_KEY_free(key);

  return result;
}

// Create and verify some random signatures against openssl.
// time(NULL) is used as prng seed so repeat runs test different values.
static void random_sigs_test() {
  int n;
  P256_PRNG_CTX prng;
  uint8_t tmp[P256_PRNG_SIZE];
  uint32_t boot_count = time(NULL);

  // Setup deterministic prng.
  p256_prng_init(&prng, "random_sigs_test", 16, boot_count);

  for (n = 0; n < 100; ++n) {
    p256_int a, b, Gx, Gy;
    p256_int r, s;

    // Make up private key
    do {
      // Pick well distributed random number 0 < a < n.
      p256_int p1, p2;
      p256_prng_draw(&prng, tmp);
      p256_from_bin(tmp, &p1);
      p256_prng_draw(&prng, tmp);
      p256_from_bin(tmp, &p2);
      p256_modmul(&SECP256r1_n, &p1, 0, &p2, &a);
    } while (p256_is_zero(&a));

    // Compute public key; a is our secret key.
    p256_base_point_mul(&a, &Gx, &Gy);

    // Pick random message to sign.
    p256_prng_draw(&prng, tmp);
    p256_from_bin(tmp, &b);

    // Compute signature on b.
    p256_ecdsa_sign(&a, &b, &r, &s);

    if (!p256_ecdsa_verify(&Gx, &Gy, &b, &r, &s)) {
      printf("random_sigs_test()"
             ": p256_ecdsa_verify fail at %d! (boot_count %d)\n",
             n, boot_count);
      exit(1);
    }

    if (!ossl_verify(&Gx, &Gy, tmp, &r, &s)) {
      printf("random_sigs_test()"
             ": ossl_verify fail at %d! (boot_count %d)\n",
             n, boot_count);
      exit(1);
    }
  }
}

// Test signature parameter validation.
static void invalid_sigs_test() {
  P256_PRNG_CTX prng;
  uint8_t tmp[P256_PRNG_SIZE];
  uint32_t boot_count = time(NULL);

  p256_prng_init(&prng, "invalid_sigs_test", 17, boot_count);

  {
    p256_int a, b, Gx, Gy;
    p256_int r, s;
    p256_int one = P256_ONE;
    p256_int zero = P256_ZERO;

    (void)one;
    (void)zero;

    // Make up private key.
    do {
      // Pick well distributed random number 0 < a < n.
      p256_int p1, p2;
      p256_prng_draw(&prng, tmp);
      p256_from_bin(tmp, &p1);
      p256_prng_draw(&prng, tmp);
      p256_from_bin(tmp, &p2);
      p256_modmul(&SECP256r1_n, &p1, 0, &p2, &a);
    } while (p256_is_zero(&a));

    // Compute public key; a is our secret key.
    p256_base_point_mul(&a, &Gx, &Gy);

    // Pick random message to sign.
    p256_prng_draw(&prng, tmp);
    p256_from_bin(tmp, &b);

    // Compute signature on b.
    p256_ecdsa_sign(&a, &b, &r, &s);

    if (!p256_ecdsa_verify(&Gx, &Gy, &b, &r, &s)) {
      printf("invalid_sigs_test()"
             ": p256_ecdsa_verify fail! (boot_count %d)\n",
             boot_count);
      exit(1);
    }

    // Case 1: r = 0 % n, s = m
    if (p256_ecdsa_verify(&Gx, &Gy, &b, &SECP256r1_n, &b)) {
      printf("invalid_sigs_test()"
             ": p256_ecdsa_verify didn't fail case 1! (boot_count %d)\n",
             boot_count);
      exit(1);
    }
  }
}

int main(int argc, char* argv[]) {
  random_sigs_test();
  invalid_sigs_test();
  return 0;
}
