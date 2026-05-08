// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_SERVICES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_SERVICES_H_

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_verify.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

OT_WARN_UNUSED_RESULT
rom_error_t boot_svc_handler(boot_svc_msg_t *boot_svc_msg,
                             boot_data_t *boot_data, boot_log_t *boot_log,
                             lifecycle_state_t lc_state,
                             owner_application_keyring_t *keyring,
                             size_t *verify_key, owner_config_t *owner_config,
                             uint32_t *isfb_check_count);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_ROM_EXT_BOOT_SERVICES_H_
