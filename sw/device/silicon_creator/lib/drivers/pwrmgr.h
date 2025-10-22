// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PWRMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PWRMGR_H_

#include <stdint.h>

#include "hw/top/dt/api.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  pwrmgr_all_resets_enable();
 *  SEC_MMIO_WRITE_INCREMENT(kPwrmgrSecMmioAllResetsEnable);
 * ```
 */
enum {
  kPwrmgrSecMmioAllResetsEnable = 1,
};

/**
 * A power manager request type.
 */
typedef enum pwrmgr_req_type {
  kPwrmgrReqTypeWakeup,
  kPwrmgrReqTypeReset,
} pwr_mgr_req_type_t;

/**
 * Obtain a bit index of wakeup/reset request for a device and a signal.
 *
 * Given a module instance (identified by its instance ID) and a wakeup
 * or reset request index from this module, return the source bit index
 * that, once shifted into a bitmask, can be programmed into the pwrmgr
 * `RESET_EN` register.
 *
 * @param req_type Request type (wake up or reset request).
 * @param inst_id A DT instance ID.
 * @param signal_idx Signal index.
 * @param[out] source_idx The source index corresponding to the wakeup or reset
 * requested.
 * @return `kErrorOk` if a signal matches, or a `kErrorPwrmgr` error otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t pwrmgr_find_request_source(pwr_mgr_req_type_t req_type,
                                       dt_instance_id_t inst_id,
                                       size_t signal_idx, size_t *source_idx);

/**
 * Synchronize across clock domain.
 *
 * Synchronizes across clock domains by setting the CDC_SYNC register and
 * waiting for it to clear.
 *
 * @param n Number of synchronizations to perform.
 */
void pwrmgr_cdc_sync(uint32_t n);

/**
 * Enable all resets.
 */
void pwrmgr_all_resets_enable(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PWRMGR_H_
