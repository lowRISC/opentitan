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
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>

#include "cryptoc/p256.h"

#define _TOSTR(x) #x
#define TOSTR(x) _TOSTR(x)
#define CHECK(x) \
    do { if (!(x)) { \
      errno = EADV; \
      perror(#x " @ line " TOSTR(__LINE__)); exit(1); }} while(0)

static int count_bits(const p256_int* a) {
  int i, n = 0;
  for (i = 0; i < 256; ++i) {
    n += p256_get_bit(a, i);
  }
  return n;
}

// Confirm the CPU's right shift is an arithmetic shift
void test_cpu_behavior() {
  int32_t i;
  volatile int32_t val = -1;
  uint32_t one = 1;

  for (i = 0; i < 32; i++) {
    CHECK((val>>i) == (-1));
  }

  for (i = 0; i < 32; i++) {
    CHECK(0 != (((uint32_t)(val>>i)) & (one<<i)));
  }
}

void test_shifts() {
  p256_int a = {{1}};
  p256_int b;
  int i;

  // First shift bit up one step at a time.
  for (i = 0; i < 255; ++i) {
    CHECK(p256_get_bit(&a, i) == 1);
    CHECK(!p256_is_zero(&a));
    CHECK(p256_shl(&a, 1, &a) == 0);
    CHECK(p256_get_bit(&a, i) == 0);
    CHECK(count_bits(&a) == 1);
  }
  CHECK(p256_get_bit(&a, i) == 1);
  CHECK(!p256_is_zero(&a));

  // Shift bit out top.
  CHECK(p256_shl(&a, 1, &b) == 1);
  CHECK(p256_get_bit(&b, i) == 0);
  CHECK(p256_is_zero(&b));

  // Shift bit back down.
  for (; i > 0; --i) {
    CHECK(p256_get_bit(&a, i) == 1);
    CHECK(!p256_is_zero(&a));
    p256_shr(&a, 1, &a);
    CHECK(p256_get_bit(&a, i) == 0);
    CHECK(count_bits(&a) == 1);
  }

  CHECK(p256_get_bit(&a, i) == 1);
  CHECK(!p256_is_zero(&a));

  // Shift bit out bottom.
  p256_shr(&a, 1, &a);
  CHECK(p256_is_zero(&a));
}

void test_add_sub_cmp() {
  p256_int a = {{1}};
  p256_int b;
  p256_int one = {{1}};
  int i;

  for (i = 0; i < 255; ++i) {
    CHECK(count_bits(&a) == 1);
    CHECK(p256_sub(&a, &one, &b) == 0);
    CHECK(p256_cmp(&a, &b) == 1);
    CHECK(p256_cmp(&b, &a) == -1);
    CHECK(count_bits(&b) == i);
    CHECK(p256_add(&b, &one, &b) == 0);
    CHECK(count_bits(&b) == 1);
    CHECK(p256_cmp(&b, &a) == 0);

    CHECK(p256_shl(&a, 1, &a) == 0);
  }

  CHECK(p256_add(&a, &a, &b) == 1);  // expect carry
  CHECK(p256_is_zero(&b));
  CHECK(p256_cmp(&b, &a) == -1);
  CHECK(p256_sub(&b, &one, &b) == -1);  // expect borrow
  CHECK(p256_cmp(&b, &a) == 1);
}

void test_mul_inv() {
  p256_int a = {{1}};
  p256_int one = {{1}};
  p256_int b, c;
  int i;

  for (i = 0; i < 255; ++i) {
    p256_modinv(&SECP256r1_n, &a, &b);  // b = 1/a
    p256_modmul(&SECP256r1_n, &a, 0, &b, &c);  // c = b * a = 1/a * a = 1
    CHECK(p256_cmp(&c, &one) == 0);

    p256_modinv_vartime(&SECP256r1_n, &b, &c);  // c = 1/b = 1/1/a = a
    CHECK(p256_cmp(&a, &c) == 0);

    CHECK(p256_shl(&a, 1, &a) == 0);
  }
}

void test_valid_point() {
  // Constructed x where p < x^3-3x+b < 2^256, unreduced.
  // Computed matching y to make valid point.
  p256_int x = {{0x3de86868, 0x1c4c6c08, 0x22d79c, 0, 0, 0, 0, 0}};
  p256_int y = {{0xf7cc27ae, 0x29181e9d, 0xcb78ccd6, 0x43800616,
                 0x86508edc, 0x13f5f534, 0x138ffcd1, 0x6b1c4fae}};

  CHECK(p256_is_valid_point(&x, &y) == 1);
}

int main(int argc, char* argv[]) {
  test_cpu_behavior();
  test_shifts();
  test_add_sub_cmp();
  test_mul_inv();
  test_valid_point();
  return 0;
}
