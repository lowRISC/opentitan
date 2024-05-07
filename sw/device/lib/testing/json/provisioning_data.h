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
 * DICE certificates exported during personalization.
 *
 * See the `OT_ASSERT_MEMBER_SIZE_AS_ENUM` calls in
 * `sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/ft_personalize.c`
 * for how these sizes are chosen.
 */
// clang-format off
#define STRUCT_MANUF_PERSO_CERTS(field, string) \
    field(uds_tbs_certificate, uint8_t, 728) \
    field(uds_tbs_certificate_size, size_t) \
    field(cdi_0_certificate, uint8_t, 580) \
    field(cdi_0_certificate_size, size_t) \
    field(cdi_1_certificate, uint8_t, 632) \
    field(cdi_1_certificate_size, size_t) \
    field(tpm_ek_tbs_certificate, uint8_t, 844) \
    field(tpm_ek_tbs_certificate_size, size_t) \
    field(tpm_cek_tbs_certificate, uint8_t, 456) \
    field(tpm_cek_tbs_certificate_size, size_t) \
    field(tpm_cik_tbs_certificate, uint8_t, 456) \
    field(tpm_cik_tbs_certificate_size, size_t)
UJSON_SERDE_STRUCT(ManufCerts, \
                   manuf_certs_t, \
                   STRUCT_MANUF_PERSO_CERTS);
// clang-format on

/**
 * Endorsed certificates imported during personalization.
 *
 * See the `OT_ASSERT_MEMBER_SIZE_AS_ENUM` calls in
 * `sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/ft_personalize.c`
 * for how these sizes are chosen.
 */
// clang-format off
#define STRUCT_MANUF_ENDORSED_CERTS(field, string) \
    field(uds_certificate, uint8_t, 820) \
    field(uds_certificate_size, size_t) \
    field(tpm_ek_certificate, uint8_t, 936) \
    field(tpm_ek_certificate_size, size_t) \
    field(tpm_cek_certificate, uint8_t, 548) \
    field(tpm_cek_certificate_size, size_t) \
    field(tpm_cik_certificate, uint8_t, 548) \
    field(tpm_cik_certificate_size, size_t)
UJSON_SERDE_STRUCT(ManufEndorsedCerts, \
                   manuf_endorsed_certs_t, \
                   STRUCT_MANUF_ENDORSED_CERTS);
// clang-format on

/**
 * Sha256 hash
 *
 * A 32 byte binary.
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
