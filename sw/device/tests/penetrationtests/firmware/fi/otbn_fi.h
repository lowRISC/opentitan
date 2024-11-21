// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_OTBN_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * otbn.fi.char_dmem_access command handler.
 *
 * OTBN loads WDRs with words from DMEM. These values are stored in different
 * data sections.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_dmem_access(ujson_t *uj);

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
 * otbn.fi.char.jal command handler.
 *
 * The goal of this test is to fault to JAL instruction such that the jump is
 * not performed. Then, a counter gets incremented. When no effective fault
 * occurs, the counter is 0.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_jal(ujson_t *uj);

/**
 * otbn.fi.char_mem command handler.
 *
 * Initializes IMEM and DMEM of OTBN with a fixed pattern. Inject a fault and
 * check whether the data in memory got corrupted.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_mem(ujson_t *uj);

/**
 * otbn.fi.char_rf command handler.
 *
 * Init GPRs and WDRs of OTBN with reference values. Inject faults during 10000
 * NOPS. Read back GPRs and WDRs and compare against reference values. Report
 * faulty values back to host.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_char_register_file(ujson_t *uj);

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
 * Initializes the key manager.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_init_keymgr(ujson_t *uj);

/**
 * otbn.fi.key_sideload command handler.
 *
 * Injects a fault when a key is sideloaded from the key manager into OTBN.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_key_sideload(ujson_t *uj);

/**
 * otbn.fi.load_integrity command handler.
 *
 * Tests, whether a fault during loading the OTBN app can manipulate data in
 * DMEM without changing the CRC-32 checksum that is used to check the
 * integrity of the DMEM and IMEM.
 *
 * As the OTBN app itself is not the target of this FI analysis, it only
 * consists of NOPs. The DMEM is initialized with reference values that
 * are checked.
 *
 * Faults are injected during the trigger_high & trigger_low.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_otbn_fi_load_integrity(ujson_t *uj);

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
