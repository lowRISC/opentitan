// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_ACTIVATE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_ACTIVATE_H_

#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Process a boot_svc OwnershipActivate message.
 *
 * @param msg The boot_svc OwnershipActivate message to process.
 * @param bootdata A pointer to the current boot_data in RAM.
 * @return rom_error_t
 */
rom_error_t ownership_activate_handler(boot_svc_msg_t *msg,
                                       boot_data_t *bootdata);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNERSHIP_ACTIVATE_H_
