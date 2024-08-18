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
 *  A CShake hash used for storing various LC tokens (test lock/unlock, RMA
 *  unlock, etc).
 */
// clang-format off
#define STRUCT_LC_TOKEN_HASH(field, string) \
    field(hash, uint64_t, 2)
UJSON_SERDE_STRUCT(LcTokenHash, \
                   lc_token_hash_t, \
                   STRUCT_LC_TOKEN_HASH);
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
 * Container of data exported/imported during personalization.
 *
 * The data is passed as a set of LTV objects concatenated in the 'body' field.
 *
 * See details of LTV objects' structure in
 * sw/device/silicon_creator/manuf/base/perso_tlv_data.h
 *
 * The header of the container includes the number of stored objects and the
 * index of the next free location in the container body.
 */
// clang-format off
#define STRUCT_PERSO_BLOB(field, string) \
    field(num_objs, size_t) \
    field(next_free, size_t) \
    field(body, uint8_t, 4096)
UJSON_SERDE_STRUCT(PersoBlob, \
                   perso_blob_t, \
                   STRUCT_PERSO_BLOB);
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
