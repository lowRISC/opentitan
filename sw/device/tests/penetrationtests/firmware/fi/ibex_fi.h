// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_IBEX_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_IBEX_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * ibex.fi.address_translation command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Configure the address translation for slot 0 and 1.
 * - increment_100x1 gets remapped to increment_100x10 and
 *   increment_100x10 gets remapped to increment_100x1 using the address
 *   translation unit
 * - Set the trigger.
 * - Add 100 NOPs to delay the trigger.
 * - Execute the increment_100x10 function.
 * - Unset the trigger.
 * - Check if instead of the expected function the target function was called.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_address_translation(ujson_t *uj);

/**
 * ibex.fi.address_translation_config command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Configure the address translation for DMEM and IMEM.
 * - Set the trigger.
 * - Add 1000 NOPs.
 * - Unset the trigger.
 * - Read address translation config.
 * - Compare the values.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_address_translation_config(ujson_t *uj);

/**
 * ibex.fi.char.csr_write command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Write reference values into CSR.
 * - Unset the trigger.
 * - Read value from CSR.
 * - Compare the values.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_csr_write(ujson_t *uj);

/**
 * ibex.fi.char.csr_read command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Write reference values into CSRs.
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Read values from CSRs.
 * - Unset the trigger.
 * - Compare the values.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_csr_read(ujson_t *uj);

/**
 * ibex.fi.char.flash_read command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Write reference values into flash.
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Read values from flash.
 * - Unset the trigger.
 * - Compare the values.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_flash_read(ujson_t *uj);

/**
 * ibex.fi.char.flash_write command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Write 32 values into flash.
 * - Unset the trigger.
 * - Read back values and compare.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_flash_write(ujson_t *uj);

/**
 * ibex.fi.char.sram_static command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Write ref_values[0] to the 4kB retention SRAM.
 * - Set the trigger.
 * - Add 1000 NOPs to give the setup the chance to inject faults.
 * - Unset the trigger.
 * - Read back content of the ret. SRAM and compare against reference value.
 * - If faulty words are detected, transmit addresses back to host.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_sram_static(ujson_t *uj);

/**
 * ibex.fi.char.sram_read command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Write reference values into SRAM.
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Read values from SRAM.
 * - Unset the trigger.
 * - Compare the values.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_sram_read(ujson_t *uj);

/**
 * ibex.fi.char.sram_write_static_unrolled command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Write 64 static values into SRAM using an unrolled instruction sequence.
 * - Unset the trigger.
 * - Read back values and compare.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_sram_write_static_unrolled(ujson_t *uj);

/**
 * ibex.fi.char.sram_write command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Set the trigger.
 * - Add 10 NOPs to delay the trigger
 * - Write 32 values into SRAM.
 * - Unset the trigger.
 * - Read back values and compare.
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_sram_write(ujson_t *uj);

/**
 * ibex.fi.char.unconditional_branch command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Add 10 NOPs to delay the trigger
 * - 10000 iterations with a for loop:
 *  - Execute an unconditional branch instruction
 *  - Increment variable
 * - Return the values over UART.
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_unconditional_branch(ujson_t *uj);

/**
 * ibex.fi.char.conditional_branch command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Add 10 NOPs to delay the trigger
 * - 10000 iterations with a for loop:
 *  - Execute a branch instruction
 *  - Increment variable if branch is taken or not
 * - Return the values over UART.
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_conditional_branch(ujson_t *uj);

/**
 * ibex.fi.char.mem_op_loop command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Add 100 NOPs to delay the trigger
 * - 10000 iterations with a for loop:
 *  - Load loop_counter1 value into x5: lw x5, (&loop_counter1)
 *  - Increment loop counter1: addi x5, x5, 1
 *  - Store loop counter1 back to loop_counter1: sw x5, (&loop_counter1)
 *  - Load loop_counter2 value into x6: lw x6, (&loop_counter2)
 *  - Decrement loop counter2: addi x6, x6, -1
 *  - Store loop counter2 back to loop_counter2: sw x6, (&loop_counter2)
 * - Return the values over UART.
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_mem_op_loop(ujson_t *uj);

/**
 * ibex.fi.char.reg_op_loop command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Initialize register x5=0 & x6=10000
 * - Add 100 NOPs to delay the trigger
 * - Perform 10000 x5 = x5 + 1 additions and x6 = x6 - 1 subtractions
 * - Return the values over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_reg_op_loop(ujson_t *uj);

/**
 * ibex.fi.char.unrolled_mem_op_loop command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Add 100 NOPs to delay the trigger
 * - 10000 iterations:
 *  - Load loop_counter value into x5: lw x5, (&loop_counter)
 *  - Increment loop counter: addi x5, x5, 1
 *  - Store loop counter back to loop_counter: sw x5, (&loop_counter)
 * - Return the value over UART.
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_unrolled_mem_op_loop(ujson_t *uj);

/**
 * ibex.fi.char.unrolled_reg_op_loop command handler.
 *
 * This FI penetration tests executes the following instructions:
 * - Initialize register x5=0
 * - Add 100 NOPs to delay the trigger
 * - Perform 10000 x5 = x5 + 1 additions
 * - Return the value over UART.
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_unrolled_reg_op_loop(ujson_t *uj);

/**
 * Initializes the trigger and configures the device for the Ibex FI test.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_init(ujson_t *uj);

/**
 * ibex.fi.char.register_file command handler.
 *
 * This FI penetration test executes the following instructions:
 * - Initialize temp. registers with reference values
 * - Execute 1000 NOPs
 * - Read back temp. register values and compare against reference values
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_register_file(ujson_t *uj);

/**
 * ibex.fi.char.register_file_read command handler.
 *
 * This FI penetration test executes the following instructions:
 * - Initialize temp. registers with reference values
 * - Read these registers.
 * - Compare against reference values
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi_char_register_file_read(ujson_t *uj);

/**
 * Ibex FI command handler.
 *
 * Command handler for the Ibex FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_ibex_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_IBEX_FI_H_
