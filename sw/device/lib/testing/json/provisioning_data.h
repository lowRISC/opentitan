// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_

#include "sw/device/lib/ujson/ujson_derive.h"

#ifdef __cplusplus
extern "C" {
#endif

#define MODULE_ID MAKE_MODULE_ID('j', 'p', 'd')

/**
 * Ephemeral HSM ECC public key used to derive ECDH shared secret key for
 * wrapping the RMA unlock token.
 */
// clang-format off
#define STRUCT_ECC_P256_PUBLIC_KEY(field, string) \
    field(x, uint32_t, 8) \
    field(y, uint32_t, 8)
UJSON_SERDE_STRUCT(EccP256PublicKey, \
                   ecc_p256_public_key_t, \
                   STRUCT_ECC_P256_PUBLIC_KEY);
// clang-format on

/**
 * Data imported during device personalization.
 */
// clang-format off
#define STRUCT_MANUF_RMA_TOKEN_PERSO_DATA_IN(field, string) \
    field(host_pk, ecc_p256_public_key_t)
UJSON_SERDE_STRUCT(ManufRmaTokenPersoDataIn, \
                   manuf_rma_token_perso_data_in_t, \
                   STRUCT_MANUF_RMA_TOKEN_PERSO_DATA_IN);
// clang-format on

/**
 * Data imported during device certificate personalization.
 */
// clang-format off
#define STRUCT_MANUF_CERT_PERSO_DATA_IN(field, string) \
    field(rom_ext_measurement, uint32_t, 8) \
    field(rom_ext_measurement_valid, bool) \
    field(owner_manifest_measurement, uint32_t, 8) \
    field(owner_manifest_measurement_valid, bool) \
    field(owner_measurement, uint32_t, 8) \
    field(owner_measurement_valid, bool)
UJSON_SERDE_STRUCT(ManufCertPersoDataIn, \
                   manuf_cert_perso_data_in_t, \
                   STRUCT_MANUF_CERT_PERSO_DATA_IN);
// clang-format on

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
    field(device_pk, ecc_p256_public_key_t)
UJSON_SERDE_STRUCT(WrappedRmaUnlockToken, \
                   wrapped_rma_unlock_token_t, \
                   STRUCT_WRAPPED_RMA_UNLOCK_TOKEN);
// clang-format on

/**
 * Data exported during device personalization.
 */
// clang-format off
#define STRUCT_MANUF_RMA_TOKEN_PERSO_DATA_OUT(field, string) \
    field(wrapped_rma_unlock_token, wrapped_rma_unlock_token_t)
UJSON_SERDE_STRUCT(ManufRmaTokenPersoDataOut, \
                   manuf_rma_token_perso_data_out_t, \
                   STRUCT_MANUF_RMA_TOKEN_PERSO_DATA_OUT);
// clang-format on

/**
 * Provisioning data imported onto the device in CP.
 */
// clang-format off
#define STRUCT_MANUF_CP_PROVISIONING_DATA(field, string) \
    field(device_id, uint32_t, 8) \
    field(manuf_state, uint32_t, 8) \
    field(wafer_auth_secret, uint32_t, 8) \
    field(test_unlock_token, uint32_t, 4) \
    field(test_exit_token, uint32_t, 4)
UJSON_SERDE_STRUCT(ManufCpProvisioningData, \
                   manuf_cp_provisioning_data_t, \
                   STRUCT_MANUF_CP_PROVISIONING_DATA);
// clang-format on

/**
 * Provisioning data imported onto the device in FT during individualization.
 */
// clang-format off
#define STRUCT_MANUF_FT_INDIVIDUALIZE_DATA(field, string) \
    field(device_id, uint32_t, 8)
UJSON_SERDE_STRUCT(ManufFtIndividualizeData, \
                   manuf_ft_individualize_data_t, \
                   STRUCT_MANUF_FT_INDIVIDUALIZE_DATA);
// clang-format on

#undef MODULE_ID
// clang-format on

#ifdef __cplusplus
}

#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_
