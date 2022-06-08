// Copyright lowRISC contributors.
// Copyright (C) 1997 - 2002, Makoto Matsumoto and Takuji Nishimura,
// All rights reserved.
// SPDX-License-Identifier: BSD-3-Clause
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//   1. Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//
//   2. Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//
//   3. The names of its contributors may not be used to endorse or promote
//      products derived from this software without specific prior written
//      permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT OWNER
// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "third_party/xoshiro/splitmix64.h"
#include "third_party/xoshiro/xoshiro128pp.h"

/**
 * TODO(alphan): Using MT for now as a proof of concept to minimize host-side
 * changes. We should probably replace this with a PRNG from xoshiro* family
 * for PRNGs, e.g. xoshiro128++, for better performance and less overhead.
 */

static uint32_t state[4];

void prng_seed(uint32_t seed) {
  uint64_t s = seed;
  uint64_t value;

  value = splitmix64_next(&s);
  memcpy(&state[0], &value, 8);

  value = splitmix64_next(&s);
  memcpy(&state[2], &value, 8);
}

uint8_t prng_rand_byte(void) {
  // xoshiro128's low bits tend to be of lower quality.
  return xoshiro128pp_next(state) >> 24;
}

void prng_rand_bytes(uint8_t *buffer, size_t buffer_len) {
  for (size_t i = 0; i < buffer_len; ++i) {
    buffer[i] = prng_rand_byte();
  }
}
