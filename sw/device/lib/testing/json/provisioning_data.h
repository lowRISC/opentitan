// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_

#include "sw/device/lib/ujson/ujson_derive.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Wrapped (encrypted) RMA unlock token.
 *
 * The RMA unlock token is encrypted with AES-ECB using an ECDH emphemeral key.
 * The key wrapping process works as follows:
 *
 * - An HSM generates an ECDH-P256 keypair (`sk_hsm`, `pk_hsm`), where the
 *   public component, `pk_hsm`, is baked into the provisioning test program.
 * - During provisioning, the device generates an additional ECDH-P256 keypair
 *   (`sk_device`, `pk_device`).
 * - The device then generates an emphemeral shared AES key (`k_shared`) using
 *   `sk_device` and `pk_hsm`.
 * - The device encrypts the raw RMA unlock token using AES and the shared
 *   secret key, `k_shared`.
 * - The device transmits the encrypted RMA unlock token, along with the
 *   device-generated `pk_device`, to the host (e.g. ATE), allowing the RMA
 *   unlock token to be decrypted using the shared secret (`k_shared`) derived
 *   by the HSM.
 */
// clang-format off
#define STRUCT_WRAPPED_RMA_UNLOCK_TOKEN(field, string) \
    field(data, uint32_t, 4) \
    field(ecc_pk_device_x, uint32_t, 8) \
    field(ecc_pk_device_y, uint32_t, 8)
UJSON_SERDE_STRUCT(WrappedRmaUnlockToken, \
                   wrapped_rma_unlock_token_t, \
                   STRUCT_WRAPPED_RMA_UNLOCK_TOKEN);

#define STRUCT_MANUF_PROVISIONING(field, string) \
    field(wrapped_rma_unlock_token, wrapped_rma_unlock_token_t)
UJSON_SERDE_STRUCT(ManufProvisioning, \
                   manuf_provisioning_t, \
                   STRUCT_MANUF_PROVISIONING);
// clang-format on

#ifdef __cplusplus
}

#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_
