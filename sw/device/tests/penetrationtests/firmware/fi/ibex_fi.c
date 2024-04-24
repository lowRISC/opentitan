// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/ibex_fi.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/csr_registers.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/tests/penetrationtests/firmware/lib/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/ibex_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// A function which takes an uint32_t as its only argument.
typedef uint32_t (*str_fn_t)(uint32_t);

extern uint32_t increment_100x10(uint32_t start_value);

extern uint32_t increment_100x1(uint32_t start_value);

static str_fn_t increment_100x10_remapped = (str_fn_t)increment_100x10;
static str_fn_t increment_100x1_remapped = (str_fn_t)increment_100x1;

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

// Indicates whether flash already was initialized for the test or not.
static bool flash_init;
// Indicates whether flash content is valid or not.
static bool flash_data_valid;
// Indicates whether ret SRAM already was initialized for the test or not.
static bool sram_ret_init;

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

static volatile uint32_t sram_main_buffer[256];

// Inline function used by the sram_write_read test.
static inline void sram_write_read_instr(void) {
  asm volatile("sw x5, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"(&sram_main_buffer[0]));
}

status_t handle_ibex_fi_address_translation(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Create translation descriptions.
  dif_rv_core_ibex_addr_translation_mapping_t increment_100x10_mapping = {
      .matching_addr = (uintptr_t)increment_100x1,
      .remap_addr = (uintptr_t)increment_100x10,
      .size = 256,
  };
  dif_rv_core_ibex_addr_translation_mapping_t increment_100x1_mapping = {
      .matching_addr = (uintptr_t)increment_100x10,
      .remap_addr = (uintptr_t)increment_100x1,
      .size = 256,
  };

  // Configure slot 0 for the increment_100x10.
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationIBus, increment_100x10_mapping));
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationDBus, increment_100x10_mapping));

  // Configure slot 1 for the increment_100x1.
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationIBus, increment_100x1_mapping));
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationDBus, increment_100x1_mapping));

  // Enable the slots.
  TRY(dif_rv_core_ibex_enable_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationIBus));
  TRY(dif_rv_core_ibex_enable_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationDBus));

  TRY(dif_rv_core_ibex_enable_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationIBus));
  TRY(dif_rv_core_ibex_enable_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationDBus));

  // FI code target.
  uint32_t result_expected = 0;
  sca_set_trigger_high();
  asm volatile(NOP100);
  result_expected = increment_100x10_remapped(0);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  uint32_t result_target = increment_100x1_remapped(0);
  // Compare values
  uint32_t res = 0;
  if (result_expected != 100) {
    res = 1;
  }

  if (result_target != 1000) {
    res |= 1;
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_address_translation_config(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Address translation configuration.
  dif_rv_core_ibex_addr_translation_mapping_t mapping1 = {
      .matching_addr = 0xa0000000,
      .remap_addr = (uintptr_t)handle_ibex_fi_address_translation_config,
      .size = 256,
  };

  dif_rv_core_ibex_addr_translation_mapping_t mapping2 = {
      .matching_addr = 0xa0000000,
      .remap_addr = (uintptr_t)handle_ibex_fi_address_translation_config,
      .size = 256,
  };

  // Write address translation configuration.
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationIBus, mapping1));

  // FI code target.
  // Either slot 0 config, which is already written, or slot 1 config, which
  // gets written is targeted using FI.
  sca_set_trigger_high();
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationDBus, mapping2));
  asm volatile(NOP1000);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read back address translation configuration.
  dif_rv_core_ibex_addr_translation_mapping_t mapping1_read_back;
  dif_rv_core_ibex_addr_translation_mapping_t mapping2_read_back;
  TRY(dif_rv_core_ibex_read_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationIBus, &mapping1_read_back));
  TRY(dif_rv_core_ibex_read_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationDBus, &mapping2_read_back));

  uint32_t res = 0;
  // Compare mapping 1.
  if ((mapping1_read_back.matching_addr != mapping1.matching_addr) ||
      (mapping1_read_back.remap_addr != mapping1.remap_addr) ||
      (mapping1_read_back.size != mapping1.size)) {
    res = 1;
  }

  // Compare mapping 2.
  if ((mapping2_read_back.matching_addr != mapping2.matching_addr) ||
      (mapping2_read_back.remap_addr != mapping2.remap_addr) ||
      (mapping2_read_back.size != mapping2.size)) {
    res = 1;
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_csr_write(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // FI code target.
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (int i = 0; i < 100; i++) {
    CSR_WRITE(CSR_REG_MSCRATCH, ref_values[0]);
  }
  asm volatile(NOP10);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  uint32_t res_values;
  // Read values from CSRs.
  CSR_READ(CSR_REG_MSCRATCH, &res_values);

  // Compare against reference values.
  uint32_t res = 0;
  if (res_values != ref_values[0]) {
    res = 1;
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_csr_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Write reference value into CSR.
  CSR_WRITE(CSR_REG_MSCRATCH, ref_values[0]);

  uint32_t res_values[32];
  // FI code target.
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (int i = 0; i < 32; i++) {
    CSR_READ(CSR_REG_MSCRATCH, &res_values[i]);
  }
  asm volatile(NOP10);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Compare against reference values.
  uint32_t res = 0;
  for (int i = 0; i < 32; i++) {
    if (res_values[i] != ref_values[0]) {
      res |= 1;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_flash_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  if (!flash_init) {
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

    TRY(dif_flash_ctrl_set_data_region_properties(&flash, 0, data_region));
    TRY(dif_flash_ctrl_set_data_region_enablement(&flash, 0,
                                                  kDifToggleEnabled));

    flash_init = true;
  }

  ptrdiff_t flash_bank_1_addr =
      (ptrdiff_t)flash_info.data_pages * (ptrdiff_t)flash_info.bytes_per_page;
  mmio_region_t flash_bank_1 = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_bank_1_addr);

  if (!flash_data_valid) {
    // Prepare page and write reference values into it.
    uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
    memset(input_page, 0x0, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
    for (int i = 0; i < 32; i++) {
      input_page[i] = ref_values[i];
    }

    // Erase flash and write page with reference values.
    TRY(flash_ctrl_testutils_erase_and_write_page(
        &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
        kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));

    flash_data_valid = true;
  }

  // FI code target.
  uint32_t res_values[32];
  sca_set_trigger_high();
  for (int i = 0; i < 32; i++) {
    res_values[i] =
        mmio_region_read32(flash_bank_1, i * (ptrdiff_t)sizeof(uint32_t));
  }
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Compare against reference values.
  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  int faulty_address_pos = 0;

  for (uint32_t flash_pos = 0; flash_pos < 32; flash_pos++) {
    if (res_values[flash_pos] != ref_values[flash_pos]) {
      uj_output.addresses[faulty_address_pos] = flash_pos;
      uj_output.data[faulty_address_pos] = res_values[flash_pos];
      faulty_address_pos++;
      // Currently, we register only up to 8 faulty FLASH positions. If there
      // are more, we overwrite the addresses array.
      if (faulty_address_pos > 7) {
        faulty_address_pos = 0;
      }

      // Re-init flash with valid data.
      flash_data_valid = false;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_flash_write(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  if (!flash_init) {
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
    TRY(dif_flash_ctrl_set_data_region_properties(&flash, 0, data_region));
    TRY(dif_flash_ctrl_set_data_region_enablement(&flash, 0,
                                                  kDifToggleEnabled));

    flash_init = true;
  }

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
  TRY(flash_ctrl_testutils_erase_and_write_page(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_static(ujson_t *uj) {
  if (!sram_ret_init) {
    // Init retention SRAM, wipe and scramble it.
    dif_sram_ctrl_t ret_sram;
    mmio_region_t addr =
        mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
    TRY(dif_sram_ctrl_init(addr, &ret_sram));
    TRY(sram_ctrl_testutils_wipe(&ret_sram));
    TRY(sram_ctrl_testutils_scramble(&ret_sram));
    sram_ret_init = true;
  }

  int max_words =
      (TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES / sizeof(uint32_t)) - 1;

  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Get address of the ret. SRAM at the beginning of the owner section.
  uintptr_t sram_ret_buffer_addr =
      TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
      offsetof(retention_sram_t, owner);
  mmio_region_t sram_region_ret_addr =
      mmio_region_from_addr(sram_ret_buffer_addr);

  // Write reference value into SRAM.
  for (int i = 0; i < max_words; i++) {
    mmio_region_write32(sram_region_ret_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[0]);
  }

  // FI code target.
  sca_set_trigger_high();
  asm volatile(NOP1000);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Compare against reference values.
  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  int faulty_address_pos = 0;
  for (int sram_pos = 0; sram_pos < max_words; sram_pos++) {
    uint32_t res_value = mmio_region_read32(
        sram_region_ret_addr, sram_pos * (ptrdiff_t)sizeof(uint32_t));
    if (res_value != ref_values[0]) {
      uj_output.addresses[faulty_address_pos] = (uint32_t)sram_pos;
      uj_output.data[faulty_address_pos] = res_value;
      faulty_address_pos++;
      // Currently, we register only up to 8 faulty SRAM positions. If there
      // are more, we overwrite the addresses array.
      if (faulty_address_pos > 7) {
        faulty_address_pos = 0;
      }
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);
  return OK_STATUS(0);
}

status_t handle_ibex_fi_char_sram_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Write reference values into SRAM.
  for (int i = 0; i < 256; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[i % 32]);
  }

  uint32_t res_values[256];
  // FI code target.
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (int i = 0; i < 256; i++) {
    res_values[i] = mmio_region_read32(sram_region_main_addr,
                                       i * (ptrdiff_t)sizeof(uint32_t));
  }
  asm volatile(NOP10);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  int faulty_address_pos = 0;

  for (uint32_t sram_pos = 0; sram_pos < 256; sram_pos++) {
    if (res_values[sram_pos] != ref_values[sram_pos % 32]) {
      uj_output.addresses[faulty_address_pos] = sram_pos;
      uj_output.data[faulty_address_pos] = res_values[sram_pos];
      faulty_address_pos++;
      // Currently, we register only up to 8 faulty SRAM positions. If there
      // are more, we overwrite the addresses array.
      if (faulty_address_pos > 7) {
        faulty_address_pos = 0;
      }
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write_static_unrolled(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Initialize SRAM region with inverse ref_values to avoid that data from a
  // previous run is still in memory.
  for (size_t i = 0; i < 64; i++) {
    sram_main_buffer[i] = ~ref_values[0];
  }

  // FI code target.
  // Unrolled to create 64 consecutive SW instructions as a FI target.
  sca_set_trigger_high();
  asm volatile(NOP10);
  sram_main_buffer[0] = ref_values[0];
  sram_main_buffer[1] = ref_values[0];
  sram_main_buffer[2] = ref_values[0];
  sram_main_buffer[3] = ref_values[0];
  sram_main_buffer[4] = ref_values[0];
  sram_main_buffer[5] = ref_values[0];
  sram_main_buffer[6] = ref_values[0];
  sram_main_buffer[7] = ref_values[0];
  sram_main_buffer[8] = ref_values[0];
  sram_main_buffer[9] = ref_values[0];
  sram_main_buffer[10] = ref_values[0];
  sram_main_buffer[11] = ref_values[0];
  sram_main_buffer[12] = ref_values[0];
  sram_main_buffer[13] = ref_values[0];
  sram_main_buffer[14] = ref_values[0];
  sram_main_buffer[15] = ref_values[0];
  sram_main_buffer[16] = ref_values[0];
  sram_main_buffer[17] = ref_values[0];
  sram_main_buffer[18] = ref_values[0];
  sram_main_buffer[19] = ref_values[0];
  sram_main_buffer[20] = ref_values[0];
  sram_main_buffer[21] = ref_values[0];
  sram_main_buffer[22] = ref_values[0];
  sram_main_buffer[23] = ref_values[0];
  sram_main_buffer[24] = ref_values[0];
  sram_main_buffer[25] = ref_values[0];
  sram_main_buffer[26] = ref_values[0];
  sram_main_buffer[27] = ref_values[0];
  sram_main_buffer[28] = ref_values[0];
  sram_main_buffer[29] = ref_values[0];
  sram_main_buffer[30] = ref_values[0];
  sram_main_buffer[31] = ref_values[0];
  sram_main_buffer[32] = ref_values[0];
  sram_main_buffer[33] = ref_values[0];
  sram_main_buffer[34] = ref_values[0];
  sram_main_buffer[35] = ref_values[0];
  sram_main_buffer[36] = ref_values[0];
  sram_main_buffer[37] = ref_values[0];
  sram_main_buffer[38] = ref_values[0];
  sram_main_buffer[39] = ref_values[0];
  sram_main_buffer[40] = ref_values[0];
  sram_main_buffer[41] = ref_values[0];
  sram_main_buffer[42] = ref_values[0];
  sram_main_buffer[43] = ref_values[0];
  sram_main_buffer[44] = ref_values[0];
  sram_main_buffer[45] = ref_values[0];
  sram_main_buffer[46] = ref_values[0];
  sram_main_buffer[47] = ref_values[0];
  sram_main_buffer[48] = ref_values[0];
  sram_main_buffer[49] = ref_values[0];
  sram_main_buffer[50] = ref_values[0];
  sram_main_buffer[51] = ref_values[0];
  sram_main_buffer[52] = ref_values[0];
  sram_main_buffer[53] = ref_values[0];
  sram_main_buffer[54] = ref_values[0];
  sram_main_buffer[55] = ref_values[0];
  sram_main_buffer[56] = ref_values[0];
  sram_main_buffer[57] = ref_values[0];
  sram_main_buffer[58] = ref_values[0];
  sram_main_buffer[59] = ref_values[0];
  sram_main_buffer[60] = ref_values[0];
  sram_main_buffer[61] = ref_values[0];
  sram_main_buffer[62] = ref_values[0];
  sram_main_buffer[63] = ref_values[0];
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read back and compare against reference values.
  uint32_t res = 0;
  for (int i = 0; i < 64; i++) {
    if (sram_main_buffer[i] != ref_values[0]) {
      res |= 1;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write_read(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Initialize SRAM region with inverse reference value.
  sram_main_buffer[0] = ~ref_values[0];

  // Init x5, x6, x6 with the reference values.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));
  asm volatile("li x6, %0" : : "i"(ref_values[1]));
  asm volatile("li x7, %0" : : "i"(ref_values[2]));

  sca_set_trigger_high();
  asm volatile(NOP10);
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  sram_write_read_instr();
  asm volatile(NOP10);
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  uint32_t res_values[3];
  asm volatile("mv %0, x5" : "=r"(res_values[0]));
  asm volatile("mv %0, x6" : "=r"(res_values[1]));
  asm volatile("mv %0, x7" : "=r"(res_values[2]));

  // Compare against reference values.
  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));

  for (size_t addr = 0; addr < 3; addr++) {
    if (res_values[addr] != ref_values[addr]) {
      uj_output.addresses[addr] = (uint32_t)&sram_main_buffer[0];
      uj_output.data[addr] = res_values[addr];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Initialize SRAM region with inverse ref_values to avoid that data from a
  // previous run are still in memory.
  for (int i = 0; i < 32; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ~ref_values[i]);
  }

  // FI code target.
  sca_set_trigger_high();
  for (int i = 0; i < 32; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[i]);
  }
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_unconditional_branch(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = result;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  // FI code target.
  uint32_t branch_if_ = 1;
  uint32_t branch_else = 0;
  sca_set_trigger_high();
  asm volatile(NOP10);
  for (int i = 0; i < 10000; i++) {
    if (branch_if_ > 0) {
      branch_if_++;
    } else {
      branch_else += 10;
    }
  }
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = branch_if_;
  uj_output.result2 = branch_else;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_mem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_loop_counter_mirrored_t uj_output;
  uj_output.loop_counter1 = loop_counter1;
  uj_output.loop_counter2 = loop_counter2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_mirrored_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_unrolled_mem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counter & ERR_STATUS to host.
  ibex_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_loop_counter_mirrored_t uj_output;
  uj_output.loop_counter1 = loop_counter1;
  uj_output.loop_counter2 = loop_counter2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_mirrored_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_unrolled_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counter & ERR_STATUS to host.
  ibex_fi_loop_counter_t uj_output;
  uj_output.loop_counter = loop_counter;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_loop_counter_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_register_file(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

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
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

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
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result = res;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_register_file_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  sca_registered_alerts_t reg_alerts = sca_get_triggered_alerts();

  uint32_t res_values[6];
  // Initialize temporary registers with reference values.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));
  asm volatile("li x6, %0" : : "i"(ref_values[1]));
  asm volatile("li x7, %0" : : "i"(ref_values[2]));
  asm volatile("li x28, %0" : : "i"(ref_values[3]));
  asm volatile("li x29, %0" : : "i"(ref_values[4]));
  asm volatile("li x30, %0" : : "i"(ref_values[5]));

  // FI code target.
  sca_set_trigger_high();
  asm volatile(NOP10);
  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  sca_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = sca_get_triggered_alerts();

  // Load register values.
  asm volatile("mv %0, x5" : "=r"(res_values[0]));
  asm volatile("mv %0, x6" : "=r"(res_values[1]));
  asm volatile("mv %0, x7" : "=r"(res_values[2]));
  asm volatile("mv %0, x28" : "=r"(res_values[3]));
  asm volatile("mv %0, x29" : "=r"(res_values[4]));
  asm volatile("mv %0, x30" : "=r"(res_values[5]));

  // Check if one or multiple registers values are faulty.
  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  for (uint32_t it = 0; it < 6; it++) {
    if (res_values[it] != ref_values[it]) {
      uj_output.addresses[it] = it;
      uj_output.data[it] = res_values[it];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_init(ujson_t *uj) {
  sca_select_trigger_type(kScaTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // sca_init is not needed. kScaTriggerSourceAes is selected as a placeholder.
  sca_init(kScaTriggerSourceAes,
           kScaPeripheralIoDiv4 | kScaPeripheralEdn | kScaPeripheralCsrng |
               kScaPeripheralEntropy | kScaPeripheralAes | kScaPeripheralHmac |
               kScaPeripheralKmac | kScaPeripheralOtbn);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  sca_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  sca_configure_cpu();

  // Enable the flash.
  flash_info = dif_flash_ctrl_get_device_info();
  TRY(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(flash_ctrl_testutils_wait_for_init(&flash));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Initialize flash for the flash test and write reference values into page.
  flash_init = false;
  flash_data_valid = false;
  // Initialize retention SRAM.
  sram_ret_init = false;

  // Read the device ID and return it back to the host.
  TRY(sca_read_device_id(uj));

  return OK_STATUS();
}

status_t handle_ibex_fi(ujson_t *uj) {
  ibex_fi_subcommand_t cmd;
  TRY(ujson_deserialize_ibex_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kIbexFiSubcommandInit:
      return handle_ibex_fi_init(uj);
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
    case kIbexFiSubcommandCharSramWriteRead:
      return handle_ibex_fi_char_sram_write_read(uj);
    case kIbexFiSubcommandCharSramWriteStaticUnrolled:
      return handle_ibex_fi_char_sram_write_static_unrolled(uj);
    case kIbexFiSubcommandCharSramRead:
      return handle_ibex_fi_char_sram_read(uj);
    case kIbexFiSubcommandCharSramStatic:
      return handle_ibex_fi_char_sram_static(uj);
    case kIbexFiSubcommandCharFlashWrite:
      return handle_ibex_fi_char_flash_write(uj);
    case kIbexFiSubcommandCharFlashRead:
      return handle_ibex_fi_char_flash_read(uj);
    case kIbexFiSubcommandCharCsrWrite:
      return handle_ibex_fi_char_csr_write(uj);
    case kIbexFiSubcommandCharCsrRead:
      return handle_ibex_fi_char_csr_read(uj);
    case kIbexFiSubcommandAddressTranslationCfg:
      return handle_ibex_fi_address_translation_config(uj);
    case kIbexFiSubcommandAddressTranslation:
      return handle_ibex_fi_address_translation(uj);
    default:
      LOG_ERROR("Unrecognized IBEX FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
