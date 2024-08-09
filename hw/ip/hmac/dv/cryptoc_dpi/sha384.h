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
#ifndef OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_SHA384_H_
#define OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_SHA384_H_

#include <stddef.h>
#include <stdint.h>

#include "hash-internal.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef HASH_CTX LITE_SHA384_CTX;

void SHA384_init(LITE_SHA384_CTX *ctx);
void SHA384_update(LITE_SHA384_CTX *ctx, const void *data, size_t len);
const uint8_t *SHA384_final(LITE_SHA384_CTX *ctx);

// Convenience method. Returns digest address.
const uint8_t *SHA384_hash(const void *data, size_t len, uint8_t *digest);

#define SHA384_DIGEST_SIZE 48

#ifdef __cplusplus
}
#endif  // __cplusplus

#endif  // OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_SHA384_H_
