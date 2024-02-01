// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/ibex_fi.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/firmware/sca_lib.h"
#include "sw/device/tests/crypto/cryptotest/firmware/status.h"
#include "sw/device/tests/crypto/cryptotest/json/ibex_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Make sure that this function does not get optimized by the compiler.
uint32_t increment_counter(uint32_t counter) __attribute__((optnone)) {
  uint32_t return_value = counter + 1;
  return return_value;
}

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP100 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10 NOP10
#define NOP1000 \
  NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100 NOP100

// Init x5 = 0 macro.
#define INITX5 "addi x5, x0, 0"

// Addi x5 = x5 + 1 macros.
#define ADDI1 "addi x5, x5, 1\n"
#define ADDI10 ADDI1 ADDI1 ADDI1 ADDI1 ADDI1 ADDI1 ADDI1 ADDI1 ADDI1 ADDI1
#define ADDI100 \
  ADDI10 ADDI10 ADDI10 ADDI10 ADDI10 ADDI10 ADDI10 ADDI10 ADDI10 ADDI10
#define ADDI1000                                                          \
  ADDI100 ADDI100 ADDI100 ADDI100 ADDI100 ADDI100 ADDI100 ADDI100 ADDI100 \
      ADDI100

// Init x6 = 10000 macro.
#define INITX6 "li x6, 10000"

// Subi x6 = x6 - 1 macro.
#define SUBI1 "addi x6, x6, -1\n"

// Load word, addi, sw macro.
#define LWADDISW1 "lw x5, (%0)\n addi x5, x5, 1\n sw x5, (%0)\n"
#define LWADDISW10                                                      \
  LWADDISW1 LWADDISW1 LWADDISW1 LWADDISW1 LWADDISW1 LWADDISW1 LWADDISW1 \
      LWADDISW1 LWADDISW1 LWADDISW1
#define LWADDISW100                                                            \
  LWADDISW10 LWADDISW10 LWADDISW10 LWADDISW10 LWADDISW10 LWADDISW10 LWADDISW10 \
      LWADDISW10 LWADDISW10 LWADDISW10
#define LWADDISW1000                                                      \
  LWADDISW100 LWADDISW100 LWADDISW100 LWADDISW100 LWADDISW100 LWADDISW100 \
      LWADDISW100 LWADDISW100 LWADDISW100 LWADDISW100

// Load word, subi, sw macro.
#define LWSUBISW1 "lw x6, (%0)\n addi x6, x6, -1\n sw x6, (%0)\n"

// Reference values.
const uint32_t ref_values[32] = {
    0x1BADB002, 0x8BADF00D, 0xA5A5A5A5, 0xABABABAB, 0xABBABABE, 0xABADCAFE,
    0xBAAAAAAD, 0xBAD22222, 0xBBADBEEF, 0xBEBEBEBE, 0xBEEFCACE, 0xC00010FF,
    0xCAFED00D, 0xCAFEFEED, 0xCCCCCCCC, 0xCDCDCDCD, 0x0D15EA5E, 0xDEAD10CC,
    0xDEADBEEF, 0xDEADCAFE, 0xDEADC0DE, 0xDEADFA11, 0xDEADF00D, 0xDEFEC8ED,
    0xDEADDEAD, 0xD00D2BAD, 0xEBEBEBEB, 0xFADEDEAD, 0xFDFDFDFD, 0xFEE1DEAD,
    0xFEEDFACE, 0xFEEEFEEE};

// Flash information.
static dif_flash_ctrl_state_t flash;
static dif_flash_ctrl_device_info_t flash_info;
#define FLASH_PAGES_PER_BANK flash_info.data_pages
#define FLASH_WORD_SZ flash_info.bytes_per_word
#define FLASH_PAGE_SZ flash_info.bytes_per_page
#define FLASH_UINT32_WORDS_PER_PAGE \
  (FLASH_PAGE_SZ / FLASH_WORD_SZ) * (FLASH_WORD_SZ / sizeof(uint32_t))

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_main_buffer[32];

/**
 * ibex.char.flash_read command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_flash_read(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Configure the data flash.
  // Flash configuration.
  dif_flash_ctrl_region_properties_t region_properties = {
      .rd_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .erase_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True,
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False};

  dif_flash_ctrl_data_region_properties_t data_region = {
      .base = FLASH_PAGES_PER_BANK,
      .size = 0x1,
      .properties = region_properties};

  UJSON_CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_properties(&flash, 0, data_region));
  UJSON_CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_enablement(&flash, 0, kDifToggleEnabled));

  ptrdiff_t flash_bank_1_addr =
      (ptrdiff_t)flash_info.data_pages * (ptrdiff_t)flash_info.bytes_per_page;
  mmio_region_t flash_bank_1 = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_bank_1_addr);

  // Prepare page and write reference values into it.
  uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
  memset(input_page, 0x0, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
  for (int i = 0; i < 32; i++) {
    input_page[i] = ref_values[i];
  }

  // Erase flash and write page with reference values.
  UJSON_CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));

  // FI code target.
  uint32_t res_values[32];
  sca_set_trigger_high();
  for (int i = 0; i < 32; i++) {
    res_values[i] =
        mmio_region_read32(flash_bank_1, i * (ptrdiff_t)sizeof(uint32_t));
  }
  sca_set_trigger_low();

  // Compare against reference values.
  uint32_t res = 0;
  for (int i = 0; i < 32; i++) {
    if (res_values[i] != ref_values[i]) {
      res |= 1;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.flash_write command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_flash_write(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));
  // Configure the data flash.
  // Flash configuration.
  dif_flash_ctrl_region_properties_t region_properties = {
      .rd_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .erase_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True,
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False};
  dif_flash_ctrl_data_region_properties_t data_region = {
      .base = FLASH_PAGES_PER_BANK,
      .size = 0x1,
      .properties = region_properties};
  UJSON_CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_properties(&flash, 0, data_region));
  UJSON_CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_enablement(&flash, 0, kDifToggleEnabled));

  ptrdiff_t flash_bank_1_addr =
      (ptrdiff_t)flash_info.data_pages * (ptrdiff_t)flash_info.bytes_per_page;
  mmio_region_t flash_bank_1 = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_bank_1_addr);

  // Prepare page and write reference values into it.
  uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
  memset(input_page, 0x0, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
  for (int i = 0; i < 32; i++) {
    input_page[i] = ref_values[i];
  }

  // FI code target.
  sca_set_trigger_high();
  // Erase flash and write page with reference values.
  UJSON_CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  sca_set_trigger_low();

  // Read back and compare against reference values.
  uint32_t res_values[32];
  uint32_t res = 0;
  for (int i = 0; i < 32; i++) {
    res_values[i] =
        mmio_region_read32(flash_bank_1, i * (ptrdiff_t)sizeof(uint32_t));
    if (res_values[i] != ref_values[i]) {
      res |= 1;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.sram_read command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_sram_read(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write reference values into SRAM.
  for (int i = 0; i < 32; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[i]);
  }

  uint32_t res_values[32];
  // FI code target.
  sca_set_trigger_high();
  for (int i = 0; i < 32; i++) {
    res_values[i] = mmio_region_read32(sram_region_main_addr,
                                       i * (ptrdiff_t)sizeof(uint32_t));
  }
  sca_set_trigger_low();

  // Compare against reference values.
  uint32_t res = 0;
  for (int i = 0; i < 32; i++) {
    if (res_values[i] != ref_values[i]) {
      res |= 1;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.sram_write command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_sram_write(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // FI code target.
  sca_set_trigger_high();
  for (int i = 0; i < 32; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[i]);
  }
  sca_set_trigger_low();

  // Read back and compare against reference values.
  uint32_t res_values[32];
  uint32_t res = 0;
  for (int i = 0; i < 32; i++) {
    res_values[i] = mmio_region_read32(sram_region_main_addr,
                                       i * (ptrdiff_t)sizeof(uint32_t));
    if (res_values[i] != ref_values[i]) {
      res |= 1;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.unconditional_branch command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_unconditional_branch(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // FI code target.
  uint32_t result = 0;
  sca_set_trigger_high();
  asm volatile(NOP10);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  result = increment_counter(result);
  sca_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = result;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.conditional_branch command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_conditional_branch(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // FI code target.
  uint32_t branch_if_ = 1;
  uint32_t branch_else = 0;
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (int i = 0; i < 10000; i++) {
    if (branch_if_ > 0) {
      branch_if_++;
    } else {
      branch_else++;
    }
  }
  sca_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = branch_if_;
  uj_output.result2 = branch_else;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.mem_op_loop command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_mem_op_loop(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // FI code target.
  uint32_t loop_counter1 = 0;
  uint32_t loop_counter2 = 10000;
  sca_set_trigger_high();
  asm volatile(NOP100);
  for (int loop_cnt = 0; loop_cnt < 10000; loop_cnt++) {
    asm volatile(LWADDISW1 : : "r"((uint32_t *)&loop_counter1));
    asm volatile(LWSUBISW1 : : "r"((uint32_t *)&loop_counter2));
  }
  sca_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_loop_counter_mirrored_t uj_output;
  uj_output.loop_counter1 = loop_counter1;
  uj_output.loop_counter2 = loop_counter2;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_mirrored_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.unrolled_mem_op_loop command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_unrolled_mem_op_loop(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // FI code target.
  uint32_t loop_counter = 0;
  sca_set_trigger_high();
  asm volatile(NOP100);
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  asm volatile(LWADDISW1000 : : "r"((uint32_t *)&loop_counter));
  sca_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counter & ERR_STATUS to host.
  ibex_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.reg_op_loop command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_reg_op_loop(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // FI code target.
  uint32_t loop_counter1 = 0;
  uint32_t loop_counter2 = 10000;
  sca_set_trigger_high();
  asm volatile(INITX5);
  asm volatile(INITX6);
  asm volatile(NOP100);
  for (int loop_cnt = 0; loop_cnt < 10000; loop_cnt++) {
    asm volatile(ADDI1);
    asm volatile(SUBI1);
  }
  asm volatile("mv %0, x5" : "=r"(loop_counter1));
  asm volatile("mv %0, x6" : "=r"(loop_counter2));
  sca_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_loop_counter_mirrored_t uj_output;
  uj_output.loop_counter1 = loop_counter1;
  uj_output.loop_counter2 = loop_counter2;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_mirrored_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.unrolled_reg_op_loop command handler.
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
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_unrolled_reg_op_loop(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // FI code target.
  uint32_t loop_counter = 0;
  sca_set_trigger_high();
  asm volatile(INITX5);
  asm volatile(NOP100);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile(ADDI1000);
  asm volatile("mv %0, x5" : "=r"(loop_counter));
  sca_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counter & ERR_STATUS to host.
  ibex_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.register_file command handler.
 *
 * This FI penetration test executes the following instructions:
 * - Initialize temp. registers with reference values
 * - Execute 1000 NOPs
 * - Read back temp. register values and compare against reference values
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_register_file(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  uint32_t res_values[7];

  // Initialize temporary registers with reference values.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));
  asm volatile("li x6, %0" : : "i"(ref_values[1]));
  asm volatile("li x7, %0" : : "i"(ref_values[2]));
  asm volatile("li x28, %0" : : "i"(ref_values[3]));
  asm volatile("li x29, %0" : : "i"(ref_values[4]));
  asm volatile("li x30, %0" : : "i"(ref_values[5]));
  asm volatile("li x31, %0" : : "i"(ref_values[6]));

  // FI code target.
  sca_set_trigger_high();
  asm volatile(NOP1000);
  sca_set_trigger_low();

  // Load register values.
  asm volatile("mv %0, x5" : "=r"(res_values[0]));
  asm volatile("mv %0, x6" : "=r"(res_values[1]));
  asm volatile("mv %0, x7" : "=r"(res_values[2]));
  asm volatile("mv %0, x28" : "=r"(res_values[3]));
  asm volatile("mv %0, x29" : "=r"(res_values[4]));
  asm volatile("mv %0, x30" : "=r"(res_values[5]));
  asm volatile("mv %0, x31" : "=r"(res_values[6]));

  // Check if one or multiple registers values are faulty.
  uint32_t res = 0;
  for (int it = 0; it < 7; it++) {
    if (res_values[it] != ref_values[it]) {
      res |= 1;
      LOG_ERROR("reg %d exp=%u got=%u", it, ref_values[it], res_values[it]);
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * ibex.char.register_file_read command handler.
 *
 * This FI penetration test executes the following instructions:
 * - Initialize temp. registers with reference values
 * - Read these registers.
 * - Compare against reference values
 *
 * Faults are injected during the trigger_high & trigger_low.
 * It needs to be ensured that the compiler does not optimize this code.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_char_register_file_read(ujson_t *uj) {
  // Configure Ibex to allow reading ERR_STATUS register.
  dif_rv_core_ibex_t rv_core_ibex;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  uint32_t res_values[3];

  // Initialize temporary registers with reference values.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));
  asm volatile("li x6, %0" : : "i"(ref_values[1]));
  asm volatile("li x7, %0" : : "i"(ref_values[2]));
  asm volatile("li x28, 0");
  asm volatile("li x29, 0");
  asm volatile("li x30, 0");

  // FI code target.
  sca_set_trigger_high();
  asm volatile("mv x28, x5");
  asm volatile("mv x29, x6");
  asm volatile("mv x30, x7");
  sca_set_trigger_low();

  // Load register values.
  asm volatile("mv %0, x28" : "=r"(res_values[0]));
  asm volatile("mv %0, x29" : "=r"(res_values[1]));
  asm volatile("mv %0, x30" : "=r"(res_values[2]));

  // Check if one or multiple registers values are faulty.
  uint32_t res = 0;
  for (int it = 0; it < 3; it++) {
    if (res_values[it] != ref_values[it]) {
      res |= 1;
      LOG_ERROR("reg %d exp=%u got=%u", it, ref_values[it], res_values[it]);
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  UJSON_CHECK_DIF_OK(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS(0);
}

/**
 * Initializes the SCA trigger.
 *
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi_init_trigger(ujson_t *uj) {
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes, kScaPeripheralIoDiv4);

  // Disable the instruction cache and dummy instructions for FI attacks.
  sca_configure_cpu();

  // Enable the flash.
  flash_info = dif_flash_ctrl_get_device_info();
  UJSON_CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  UJSON_CHECK_STATUS_OK(flash_ctrl_testutils_wait_for_init(&flash));

  return OK_STATUS(0);
}

/**
 * Ibex FI command handler.
 *
 * Command handler for the Ibex FI command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_ibex_fi(ujson_t *uj) {
  ibex_fi_subcommand_t cmd;
  TRY(ujson_deserialize_ibex_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kIbexFiSubcommandInitTrigger:
      return handle_ibex_fi_init_trigger(uj);
    case kIbexFiSubcommandCharUnrolledRegOpLoop:
      return handle_ibex_fi_char_unrolled_reg_op_loop(uj);
    case kIbexFiSubcommandCharRegOpLoop:
      return handle_ibex_fi_char_reg_op_loop(uj);
    case kIbexFiSubcommandCharUnrolledMemOpLoop:
      return handle_ibex_fi_char_unrolled_mem_op_loop(uj);
    case kIbexFiSubcommandCharMemOpLoop:
      return handle_ibex_fi_char_mem_op_loop(uj);
    case kIbexFiSubcommandCharRegisterFile:
      return handle_ibex_fi_char_register_file(uj);
    case kIbexFiSubcommandCharRegisterFileRead:
      return handle_ibex_fi_char_register_file_read(uj);
    case kIbexFiSubcommandCharCondBranch:
      return handle_ibex_fi_char_conditional_branch(uj);
    case kIbexFiSubcommandCharUncondBranch:
      return handle_ibex_fi_char_unconditional_branch(uj);
    case kIbexFiSubcommandCharSramWrite:
      return handle_ibex_fi_char_sram_write(uj);
    case kIbexFiSubcommandCharSramRead:
      return handle_ibex_fi_char_sram_read(uj);
    case kIbexFiSubcommandCharFlashWrite:
      return handle_ibex_fi_char_flash_write(uj);
    case kIbexFiSubcommandCharFlashRead:
      return handle_ibex_fi_char_flash_read(uj);
    default:
      LOG_ERROR("Unrecognized IBEX FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
