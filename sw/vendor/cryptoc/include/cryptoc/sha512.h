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
#ifndef SECURITY_UTIL_LITE_SHA512_H__
#define SECURITY_UTIL_LITE_SHA512_H__

#include <stddef.h>
#include <stdint.h>
#include "cryptoc/hash-internal.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef HASH_CTX LITE_SHA512_CTX;

void SHA512_init(LITE_SHA512_CTX* ctx);
void SHA512_update(LITE_SHA512_CTX* ctx, const void* data, size_t len);
const uint8_t* SHA512_final(LITE_SHA512_CTX* ctx);

// Convenience method. Returns digest address.
const uint8_t* SHA512_hash(const void* data, size_t len, uint8_t* digest);

#define SHA512_DIGEST_SIZE 64

#ifdef __cplusplus
}
#endif  // __cplusplus

#endif  // SECURITY_UTIL_LITE_SHA512_H__
