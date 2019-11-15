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
#include <stdio.h>
#include <string.h>

#include "cryptoc/p256_prng.h"

static const uint8_t expected[P256_PRNG_SIZE] = {
  0x3c,0x0a,0x3f,0xdc,0x53,0x13,0xde,0x17,
  0x5f,0xad,0xc5,0x53,0xd7,0x6b,0xc6,0x28,
  0x40,0x37,0x23,0x3c,0x26,0x80,0xe0,0xcd,
  0x4c,0xf6,0xfd,0x11,0x28,0x18,0xfe,0x31
};

int main(int argc, char* argv[]) {
  P256_PRNG_CTX ctx;
  uint8_t rnd[P256_PRNG_SIZE];
  int i;

  p256_prng_init(&ctx, "p256_prng_test", 14, 0);

  if (ctx.instance_count != 0) return 1;
  if (ctx.call_count != 0) return 1;

  p256_prng_draw(&ctx, rnd);

  if (ctx.instance_count != 0) return 1;
  if (ctx.call_count != 1) return 1;

  p256_prng_draw(&ctx, rnd);

  if (ctx.instance_count != 0) return 1;
  if (ctx.call_count != 2) return 1;

  // Compare prng output against known good output.
  // This catches endianess issues and algorigthm changes.
  if (memcmp(rnd, expected, P256_PRNG_SIZE)) {
    // Print failed output in case it is to be the new known good output.
    printf("{");
    for (i = 0; i < P256_PRNG_SIZE; ++i) {
      if (i) printf(",");
      printf("0x%02x", rnd[i]);
    }
    printf("}\n");

    return 1;
  }

  return 0;
}
