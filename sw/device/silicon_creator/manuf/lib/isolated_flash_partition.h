// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_ISOLATED_FLASH_PARTITION_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_ISOLATED_FLASH_PARTITION_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

/**
 * Reads the wafer authentication secret to the isolated flash partition.
 *
 * @param flash_ctrl_state Stateful flash controller handle.
 * @param num_words Number of 32-bit words to read from the partition.
 * @param[out] wafer_auth_secret Buffer to hold wafer authentication secret
 *                               words read.
 * @return OK_STATUS on success.
 */
status_t isolated_flash_partition_read(dif_flash_ctrl_state_t *flash_ctrl_state,
                                       size_t num_wafer_auth_secret_words,
                                       uint32_t *wafer_auth_secret);

/**
 * Writes the wafer authentication secret to the isolated flash partition.
 *
 * @param flash_ctrl_state Stateful flash controller handle.
 * @param wafer_auth_secret Buffer containing the wafer authentication secret
 *                          words to write to the partition.
 * @param num_words Number of 32-bit words to write to the partition.
 * @return OK_STATUS on success.
 */
status_t isolated_flash_partition_write(
    dif_flash_ctrl_state_t *flash_ctrl_state, const uint32_t *wafer_auth_secret,
    size_t num_words);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_ISOLATED_FLASH_PARTITION_H_
