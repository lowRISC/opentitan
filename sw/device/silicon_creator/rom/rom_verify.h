// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_VERIFY_H_

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Verifies a ROM_EXT.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * its `identifier` and `security_version` fields, and verifies its signature.
 *
 * @param Manifest of the ROM_EXT to be verified.
 * @param Life cycle state of the chip.
 * @param Boot data from flash.
 * @param First stage (ROM-->ROM_EXT) secure boot keys loaded from OTP.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rom_verify(const manifest_t *manifest,
                       const lifecycle_state_t lc_state,
                       const boot_data_t *boot_data,
                       const sigverify_otp_key_ctx_t *sigverify_ctx,
                       uint32_t *flash_exec);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_ROM_VERIFY_H_
