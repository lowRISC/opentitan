// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * otbn.fi.char.hardware.dmem.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Initialize register x3=0
 * - Perform 10000 x3 = x3 + 1 additions using hardware loop instructions.
 *   Load loop counter from memory and write back after increment.
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_hardware_dmem_op_loop(ujson_t *uj);

/**
 * otbn.fi.char.hardware.reg.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Initialize register x3=0
 * - Perform 10000 x3 = x3 + 1 additions using hardware loop instructions
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_hardware_reg_op_loop(ujson_t *uj);

/**
 * otbn.fi.char.unrolled.dmem.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Perform 100 times:
 *  - Load loop counter from memory
 *  - Increment loop counter
 *  - Store back to memory
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_unrolled_dmem_op_loop(ujson_t *uj);

/**
 * otbn.char.unrolled.reg.op.loop command handler.
 *
 * This FI penetration tests executes the following instructions on OTBN:
 * - Initialize register x2=0
 * - Perform 100 x2 = x2 + 1 additions
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_unrolled_reg_op_loop(ujson_t *uj);

/**
 * Initializes the OTBN FI test.
 *
 * Setup the trigger and alert handler. Disable dummy instructions and the
 * iCache.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_init(ujson_t *uj);

/**
 * OTBN FI command handler.
 *
 * Command handler for the OTBN FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_
