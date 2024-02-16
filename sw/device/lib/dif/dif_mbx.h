// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_MBX_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_MBX_H_

/**
 * @file
 * @brief <a href="/hw/ip/mbx/doc/">DOE Mailbox</a> Device Interface
 * Functions
 */
#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_mbx_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Inbound and outbound range for DOE Mailbox.
 */
typedef struct dif_mbx_range_config {
  uint32_t imbx_base_addr;
  uint32_t imbx_limit_addr;
  uint32_t ombx_base_addr;
  uint32_t ombx_limit_addr;
} dif_mbx_range_config_t;

/**
 * A DOE transaction is allowed to have at maximum 1024 double words (32-bit
 * each).
 */
#define DOE_MAILBOX_MAX_OBJECT_SIZE 1024

/**
 * DOE object transferred on the inbound or outbound mailbox.
 */
typedef struct dif_mbx_transaction {
  uint32_t *data_dwords;
  uint32_t nr_dwords;
} dif_mbx_transaction_t;

/**
 * Configures the mailbox inbound and outbound ranges and validates them.
 *
 * @param mbx A DOE Mailbox handle.
 * @param config Mailbox inbound and outbound range configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_range_set(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t config);

/**
 * Returns whether the mailbox is busy or not.
 *
 * @param mbx A DOE Mailbox handle.
 * @param[out] is_busy True if the mailbox is busy, false if not.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_is_busy(const dif_mbx_t *mbx, bool *is_busy);

/**
 * Reads the mailbox range configuration.
 *
 * @param mbx A DOE Mailbox handle.
 * @param[out] config Mailbox inbound and outbound range configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_range_get(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t *config);

/**
 * Reads the DOE interrupt configuration for inter-processor interrupts (IPI).
 *
 * @param mbx A DOE Mailbox handle.
 * @param[out] doe_intr_addr Mailbox interrupt address.
 * @param[out] doe_intr_data Mailbox interrupt value.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_ipi_configuration_get(const dif_mbx_t *mbx,
                                           uint32_t *doe_intr_addr,
                                           uint32_t *doe_intr_data);

/**
 * Host reads the DoE Mailbox request from internal SRAM.
 *
 * @param mbx A DOE Mailbox handle.
 * @param[out] request DOE object read from the internal SRAM.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_process_request(const dif_mbx_t *mbx,
                                     dif_mbx_transaction_t *request);

/**
 * Host writes the DoE Mailbox response to the internal SRAM.
 *
 * @param mbx A DOE Mailbox handle.
 * @param response DOE object written to the the internal SRAM.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_generate_response(const dif_mbx_t *mbx,
                                       const dif_mbx_transaction_t response);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_MBX_H_
