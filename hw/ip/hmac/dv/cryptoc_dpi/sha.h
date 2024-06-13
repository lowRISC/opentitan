// Copyright 2016 Google Inc.
// SPDX-License-Identifier: Apache-2.0
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
#ifndef OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_SHA_H_
#define OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_SHA_H_

#include <stdint.h>

#include "hash-internal.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef HASH_CTX SHA_CTX;

void SHA_init(SHA_CTX *ctx);
void SHA_update(SHA_CTX *ctx, const void *data, size_t len);
const uint8_t *SHA_final(SHA_CTX *ctx);

// Convenience method. Returns digest address.
// NOTE: *digest needs to hold SHA_DIGEST_SIZE bytes.
const uint8_t *SHA_hash(const void *data, size_t len, uint8_t *digest);

#ifndef SHA_DIGEST_SIZE
#define SHA_DIGEST_SIZE 20
#endif

#ifdef __cplusplus
}
#endif  // __cplusplus

#endif  // OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_SHA_H_
