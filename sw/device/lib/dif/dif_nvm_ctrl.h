// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_NVM_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_NVM_CTRL_H_

// Abstraction layer over the underlying NVM controller DIF.
//
// Code that needs to work with NVM storage should use dif_nvm_ctrl_* names
// exclusively.  The mapping to the physical controller (currently flash) is
// confined to dif_nvm_ctrl.c.  Swapping to a different NVM technology only
// requires updating that file.

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"

/**
 * NVM controller state handle.
 *
 * Holds the MMIO base address and any cached controller state.
 * Callers should treat the contents as opaque and only inspect them
 * through dif_nvm_ctrl_* functions.
 */
typedef dif_flash_ctrl_state_t dif_nvm_ctrl_state_t;

/**
 * NVM info-region access properties.
 *
 * Specifies read, program, erase, scramble, ECC and high-endurance
 * settings for a single info region.
 */
typedef dif_flash_ctrl_region_properties_t dif_nvm_ctrl_region_properties_t;

/** Partition types (data vs. info). */
typedef dif_flash_ctrl_partition_type_t dif_nvm_ctrl_partition_type_t;
#define kDifNvmCtrlPartitionTypeData kDifFlashCtrlPartitionTypeData
#define kDifNvmCtrlPartitionTypeInfo kDifFlashCtrlPartitionTypeInfo

/**
 * Initialise an NVM controller state handle.
 *
 * @param nvm       Handle to initialise.
 * @param base_addr MMIO base address of the NVM controller.
 * @return Standard DIF result.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_nvm_ctrl_init_state(dif_nvm_ctrl_state_t *nvm,
                                     mmio_region_t base_addr);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_NVM_CTRL_H_
