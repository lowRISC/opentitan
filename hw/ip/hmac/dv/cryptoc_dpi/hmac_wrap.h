// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_HMAC_WRAP_H_
#define OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_HMAC_WRAP_H_

#ifdef __cplusplus
extern "C" {
#endif

// Compute HMAC using arbitrary length key and msg with SHA. Returns digest
// address.
const uint8_t *HMAC_SHA(const void *key, size_t key_len, const void *msg,
                        size_t msg_len, uint8_t *hmac);

// Compute HMAC using arbitrary length key and msg with SHA256. Returns digest
// address.
const uint8_t *HMAC_SHA256(const void *key, size_t key_len, const void *msg,
                           size_t msg_len, uint8_t *hmac);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_HW_IP_HMAC_DV_CRYPTOC_DPI_HMAC_WRAP_H_
