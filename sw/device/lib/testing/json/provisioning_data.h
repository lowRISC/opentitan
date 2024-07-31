// Copyright lowRISC contributors (OpenTitan project).
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
 * Provisioning data imported onto the device in CP.
 */
// clang-format off
#define STRUCT_MANUF_CP_PROVISIONING_DATA(field, string) \
    field(device_id, uint32_t, 8) \
    field(manuf_state, uint32_t, 8) \
    field(wafer_auth_secret, uint32_t, 8) \
    field(test_unlock_token_hash, uint64_t, 2) \
    field(test_exit_token_hash, uint64_t, 2)
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

/**
 * ECC P256 public key.
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
 * Wrapped (encrypted) RMA unlock token.
 *
 * The RMA unlock token is encrypted with AES-ECB using an ECDH emphemeral key.
 * The key wrapping process works as follows:
 *
 * - The host generates an ECDH-P256 keypair (`sk_host`, `pk_host`), where the
 *   public component, `pk_host`, is sent to the device over the console.
 * - During provisioning, the device generates its own ECDH-P256 keypair
 *   (`sk_device`, `pk_device`).
 * - The device then generates an emphemeral, shared, AES key (`k_shared`) using
 *   `sk_device` and `pk_host`.
 * - The device encrypts the raw RMA unlock token using AES and the shared
 *   secret key, `k_shared`.
 * - The device transmits the encrypted RMA unlock token, along with the
 *   device-generated `pk_device`, to the host (e.g. ATE), allowing the RMA
 *   unlock token to be decrypted using the shared secret (`k_shared`) derived
 *   by the host.
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
 * Inputs needed to generate certificates during personalization.
 */
// clang-format off
#define STRUCT_MANUF_CERTGEN_INPUTS(field, string) \
    field(rom_ext_measurement, uint32_t, 8) \
    field(rom_ext_security_version, uint32_t) \
    field(owner_manifest_measurement, uint32_t, 8) \
    field(owner_measurement, uint32_t, 8) \
    field(owner_security_version, uint32_t) \
    field(auth_key_key_id, uint8_t, 20)
UJSON_SERDE_STRUCT(ManufCertgenInputs, \
                   manuf_certgen_inputs_t, \
                   STRUCT_MANUF_CERTGEN_INPUTS);
// clang-format on

/**
 * All certificates exported during personalization.
 *
 * This struct may hold up to eight different certificate blobs, the cumulative
 * size of which must be <= 4k. The layout is such that the first three slots
 * contain the following DICE certificates, and the remaining slots may be used
 * by provisioning extensions.
 *
 * First three slots:
 * 1. UDS TBS certificate.
 * 2. CDI_0 certificate.
 * 3. CDI_1 certificate.
 */
// clang-format off
#define STRUCT_MANUF_CERTS(field, string) \
    field(sizes, uint32_t, 8) \
    field(offsets, uint32_t, 8) \
    field(certs, uint8_t, 4096)
UJSON_SERDE_STRUCT(ManufCerts, \
                   manuf_certs_t, \
                   STRUCT_MANUF_CERTS);
// clang-format on

/**
 * All endorsed certificates imported during personalization.
 *
 * This struct may hold up to eight different certificate blobs, the cumulative
 * size of which must be <= 4k. The layout is such that the first slot contains
 * the endorsed UDS certificate, and the remaining slots may be used by
 * provisioning extensions.
 */
// clang-format off
#define STRUCT_MANUF_ENDORSED_CERTS(field, string) \
    field(sizes, uint32_t, 8) \
    field(offsets, uint32_t, 8) \
    field(certs, uint8_t, 4096)
UJSON_SERDE_STRUCT(ManufEndorsedCerts, \
                   manuf_endorsed_certs_t, \
                   STRUCT_MANUF_ENDORSED_CERTS);
// clang-format on

/**
 * Sha256 hash digest.
 */
// clang-format off
#define STRUCT_SHA256_HASH(field, string) \
    field(data, uint32_t, 8)
UJSON_SERDE_STRUCT(SerdesSha256Hash, \
                   serdes_sha256_hash_t, \
                   STRUCT_SHA256_HASH);
// clang-format on

#undef MODULE_ID
// clang-format on

#ifdef __cplusplus
}

#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PROVISIONING_DATA_H_
