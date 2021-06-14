// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// TODO(opentitan/#5955): Update parameters when the manifest struct is ready.
/**
 * Verifies the signature of a ROM_EXT manifest.
 *
 * @param signed_region Pointer to the start of the signed region.
 * @param signed_region_len Length of the signed region in bytes.
 * @param signature An RSA signature.
 * @param key_id ID of the key to use for verifying the signature.
 * @return Result of the operation.
 */
rom_error_t sigverify_rom_ext_signature_verify(
    const void *signed_region, size_t signed_region_len,
    const sigverify_rsa_buffer_t *signature, uint32_t key_id);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_SIGVERIFY_H_
