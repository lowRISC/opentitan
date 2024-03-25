// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/ibex_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/firmware/sca_lib.h"
#include "sw/device/tests/crypto/cryptotest/firmware/status.h"
#include "sw/device/tests/crypto/cryptotest/json/ibex_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[8];

/**
 * ibex.sca.tl_write
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write data over TL-UL into SRAM.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_write(ujson_t *uj) {
  // Get data to write into SRAM.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Write provided data into SRAM.
    for (int i = 0; i < 8; i++) {
      mmio_region_write32(sram_region_main_addr,
                          i * (ptrdiff_t)sizeof(uint32_t), uj_data.data[i]);
    }
    sca_set_trigger_low();
  }

  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.tl_read
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from SRAM over TL-UL.
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_tl_read(ujson_t *uj) {
  // Get data to write into SRAM.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write provided data into SRAM.
  for (int i = 0; i < 8; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        uj_data.data[i]);
  }

  uint32_t read_data[8];

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Fetch data from SRAM.
    for (int i = 0; i < 8; i++) {
      read_data[i] = mmio_region_read32(sram_region_main_addr,
                                        i * (ptrdiff_t)sizeof(uint32_t));
    }
    sca_set_trigger_low();
  }
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_write
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Write provided data to registers in RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_write(ujson_t *uj) {
  // Get data to write into RF.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));
  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Write provided data into register file.
    asm volatile("mv x5, %0" : : "r"(uj_data.data[0]));
    asm volatile("mv x6, %0" : : "r"(uj_data.data[1]));
    asm volatile("mv x7, %0" : : "r"(uj_data.data[2]));
    asm volatile("mv x28, %0" : : "r"(uj_data.data[3]));
    asm volatile("mv x29, %0" : : "r"(uj_data.data[4]));
    asm volatile("mv x30, %0" : : "r"(uj_data.data[5]));
    asm volatile("mv x31, %0" : : "r"(uj_data.data[6]));
    sca_set_trigger_low();
  }
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.sca.register_file_read
 *
 * This SCA penetration test executes the following instructions:
 * - Loop num_iterations:
 *  - Set trigger
 *  - Read data from RF
 *  - Unset trigger
 *
 * SCA traces are captured during trigger_high & trigger_low.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_register_file_read(ujson_t *uj) {
  // Get data to write into RF.
  ibex_sca_test_data_t uj_data;
  TRY(ujson_deserialize_ibex_sca_test_data_t(uj, &uj_data));
  // Initialize temporary registers with reference values.
  asm volatile("mv x5, %0" : : "r"(uj_data.data[0]));
  asm volatile("mv x6, %0" : : "r"(uj_data.data[1]));
  asm volatile("mv x7, %0" : : "r"(uj_data.data[2]));
  asm volatile("mv x28, %0" : : "r"(uj_data.data[3]));
  asm volatile("mv x29, %0" : : "r"(uj_data.data[4]));
  asm volatile("mv x30, %0" : : "r"(uj_data.data[5]));

  // SCA code target.
  for (int it = 0; it < uj_data.num_iterations; it++) {
    sca_set_trigger_high();
    // Copy registers.
    asm volatile("mv x28, x5");
    asm volatile("mv x29, x6");
    asm volatile("mv x30, x7");
    sca_set_trigger_low();
  }
  // Acknowledge test.
  ibex_sca_result_t uj_output;
  uj_output.result = 0;
  RESP_OK(ujson_serialize_ibex_sca_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * Initializes the Ibex SCA test.
 *
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca_init(ujson_t *uj) {
  // Setup trigger and enable peripherals needed for the test.
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes, kScaPeripheralIoDiv4);

  // Disable the instruction cache and dummy instructions for SCA.
  sca_configure_cpu();

  return OK_STATUS(0);
}

/**
 * Ibex SCA command handler.
 *
 * Command handler for the Ibex SCA command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_sca(ujson_t *uj) {
  ibex_sca_subcommand_t cmd;
  TRY(ujson_deserialize_ibex_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kIbexScaSubcommandInit:
      return handle_ibex_sca_init(uj);
    case kIbexScaSubcommandRFRead:
      return handle_ibex_sca_register_file_read(uj);
    case kIbexScaSubcommandRFWrite:
      return handle_ibex_sca_register_file_write(uj);
    case kIbexScaSubcommandTLRead:
      return handle_ibex_sca_tl_read(uj);
    case kIbexScaSubcommandTLWrite:
      return handle_ibex_sca_tl_write(uj);
    default:
      LOG_ERROR("Unrecognized IBEX SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
