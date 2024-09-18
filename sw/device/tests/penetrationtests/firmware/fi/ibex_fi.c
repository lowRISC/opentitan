// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/ibex_fi.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/csr_registers.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/ibex_fi_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

// A function which takes an uint32_t as its only argument.
typedef uint32_t (*str_fn_t)(uint32_t);

extern uint32_t increment_100x10(uint32_t start_value);

extern uint32_t increment_100x1(uint32_t start_value);

static str_fn_t increment_100x10_remapped = (str_fn_t)increment_100x10;
static str_fn_t increment_100x1_remapped = (str_fn_t)increment_100x1;

// Interface to Ibex.
static dif_rv_core_ibex_t rv_core_ibex;

// Interface to OTP.
static dif_otp_ctrl_t otp;

// Indicates whether flash already was initialized for the test or not.
static bool flash_init;
// Indicates whether flash content is valid or not.
static bool flash_data_valid;
// Indicates whether ret SRAM already was initialized for the test or not.
static bool sram_ret_init;
// Indicates whether the otp arrays hold the valid reference values read from
// the OTP partitions.
static bool otp_ref_init;

// Arrays holding the reference data read from the OTP VENDOR_TEST,
// CREATOR_SW_CFG, and OWNER_SW_CFG partitions.
uint32_t
    otp_data_read_ref_vendor_test[(OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
                                   OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
                                  sizeof(uint32_t)];
uint32_t otp_data_read_ref_creator_sw_cfg
    [(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE -
      OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE) /
     sizeof(uint32_t)];
uint32_t
    otp_data_read_ref_owner_sw_cfg[(OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
                                    OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
                                   sizeof(uint32_t)];

// Cond. branch macros.
#define CONDBRANCHBEQ "beq x5, x6, endfitestfaultybeq\n"
#define CONDBRANCHBNE "bne x5, x6, endfitestfaultybne\n"
#define CONDBRANCHBGE "bge x5, x6, endfitestfaultybge\n"
#define CONDBRANCHBGEU "bgeu x5, x6, endfitestfaultybgeu\n"
#define CONDBRANCHBLT "blt x5, x6, endfitestfaultyblt\n"
#define CONDBRANCHBLTU "bltu x5, x6, endfitestfaultybltu\n"

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

// Init tmpregs = 0 macro.
#define INIT_TMPREGS                                   \
  "addi x5, x0, 0\n addi x6, x0, 0\n addi x7, x0, 0\n" \
  "addi x28, x0, 0\n addi x29, x0, 0\n addi x30, x0, 0\n"

// Addi chain macro.
#define ADDI_CHAIN                                      \
  "addi x6, x5, 1\n addi x7, x6, 1\n addi x28, x7, 1\n" \
  "addi x29, x28, 1\n addi x30, x29, 1\n addi x5, x30, 1\n"

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

// Make sure that this function does not get optimized by the compiler.
void increment_counter(void) __attribute__((optnone)) {
  asm volatile("addi x5, x5, 1");
}

static status_t init_ref_otp_data(void) {
  // Fetch faulty-free reference values from OTP paritions.
  if (!otp_ref_init) {
    // Read VENDOR_TEST partition.
    TRY(otp_ctrl_testutils_dai_read32_array(
        &otp, kDifOtpCtrlPartitionVendorTest, 0, otp_data_read_ref_vendor_test,
        (OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
         OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
            sizeof(uint32_t)));

    // Read CREATOR_SW_CFG partition.
    TRY(otp_ctrl_testutils_dai_read32_array(
        &otp, kDifOtpCtrlPartitionCreatorSwCfg, 0,
        otp_data_read_ref_creator_sw_cfg,
        (OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE -
         OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE) /
            sizeof(uint32_t)));

    // READ OWNER_SW_CFG partition.
    TRY(otp_ctrl_testutils_dai_read32_array(
        &otp, kDifOtpCtrlPartitionOwnerSwCfg, 0, otp_data_read_ref_owner_sw_cfg,
        (OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
         OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
            sizeof(uint32_t)));
    otp_ref_init = true;
  }
  return OK_STATUS();
}

// Init temporary registers t0...t7 with given value.
static inline void init_temp_regs(uint32_t value) {
  asm volatile("li x5, %0" : : "i"(value));
  asm volatile("li x6, %0" : : "i"(value));
  asm volatile("li x7, %0" : : "i"(value));
  asm volatile("li x28, %0" : : "i"(value));
  asm volatile("li x29, %0" : : "i"(value));
  asm volatile("li x30, %0" : : "i"(value));
  asm volatile("li x31, %0" : : "i"(value));
}

// Read back values from all registers x1...x31 into buffer.
static inline void read_all_regs(uint32_t buffer[]) {
  // The much nicer approach with
  // asm volatile("sw x1, %0" : : "m"(buffer[1]));
  // leads to two INSNs. Test in godbolt promised single INSN
  // Uglier workaround below inserts single INSN, but requires
  // read_all_regs() to be called prior to the FI trigger
  // start to avoid register overwrite.
  asm volatile("sw x1,    0(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x2,    4(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x3,    8(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x4,   12(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x5,   16(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x6,   20(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x7,   24(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x8,   28(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x9,   32(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x10,  36(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x11,  40(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x12,  44(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x13,  48(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x14,  52(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x15,  56(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x16,  60(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x17,  64(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x18,  68(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x19,  72(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x20,  76(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x21,  80(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x22,  84(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x23,  88(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x24,  92(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x25,  96(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x26, 100(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x27, 104(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x28, 108(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x29, 112(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x30, 116(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x31, 120(%0)" : : "r"(&buffer[0]));
}

static status_t read_otp_partitions(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t
      otp_data_read_res_vendor_test[(OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
                                     OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
                                    sizeof(uint32_t)];
  uint32_t otp_data_read_res_creator_sw_cfg
      [(OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE -
        OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE) /
       sizeof(uint32_t)];
  uint32_t
      otp_data_read_res_owner_sw_cfg[(OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
                                      OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
                                     sizeof(uint32_t)];

  pentest_set_trigger_high();
  asm volatile(NOP10);
  TRY(otp_ctrl_testutils_dai_read32_array(
      &otp, kDifOtpCtrlPartitionVendorTest, 0, otp_data_read_res_vendor_test,
      (OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
       OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
          sizeof(uint32_t)));
  TRY(otp_ctrl_testutils_dai_read32_array(
      &otp, kDifOtpCtrlPartitionCreatorSwCfg, 0,
      otp_data_read_res_creator_sw_cfg,
      (OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE -
       OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE) /
          sizeof(uint32_t)));
  TRY(otp_ctrl_testutils_dai_read32_array(
      &otp, kDifOtpCtrlPartitionOwnerSwCfg, 0, otp_data_read_res_owner_sw_cfg,
      (OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
       OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
          sizeof(uint32_t)));
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Detect potential mismatch caused by faults.
  uint32_t res = 0;
  for (size_t i = 0; i < ((OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
                           OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
                          sizeof(uint32_t));
       i++) {
    if (otp_data_read_ref_vendor_test[i] != otp_data_read_res_vendor_test[i]) {
      res |= 1;
    }
  }

  for (size_t i = 0; i < ((OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
                           OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
                          sizeof(uint32_t));
       i++) {
    if (otp_data_read_ref_creator_sw_cfg[i] !=
        otp_data_read_res_creator_sw_cfg[i]) {
      res |= 2;
    }
  }

  for (size_t i = 0; i < ((OTP_CTRL_PARAM_VENDOR_TEST_SIZE -
                           OTP_CTRL_PARAM_VENDOR_TEST_DIGEST_SIZE) /
                          sizeof(uint32_t));
       i++) {
    if (otp_data_read_ref_owner_sw_cfg[i] !=
        otp_data_read_res_owner_sw_cfg[i]) {
      res |= 4;
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

// Read back values fromo temporary registers t0...t7 into buffer.
static inline void read_temp_regs(uint32_t buffer[]) {
  asm volatile("mv %0, x5" : "=r"(buffer[0]));
  asm volatile("mv %0, x6" : "=r"(buffer[1]));
  asm volatile("mv %0, x7" : "=r"(buffer[2]));
  asm volatile("mv %0, x28" : "=r"(buffer[3]));
  asm volatile("mv %0, x29" : "=r"(buffer[4]));
  asm volatile("mv %0, x30" : "=r"(buffer[5]));
  asm volatile("mv %0, x31" : "=r"(buffer[6]));
}

// Make sure that this function does not get optimized by the compiler.
void not_increment_counter(void) __attribute__((optnone)) {
  asm volatile("ret");
  asm volatile(ADDI10);
}

status_t handle_ibex_fi_address_translation(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  pentest_set_trigger_high();
  asm volatile(NOP100);
  result_expected = increment_100x10_remapped(0);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  pentest_set_trigger_high();
  TRY(dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_1,
      kDifRvCoreIbexAddrTranslationDBus, mapping2));
  asm volatile(NOP1000);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_conditional_branch_beq(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  // FI code target.
  pentest_set_trigger_high();
  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xef");
  asm volatile(NOP10);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile(CONDBRANCHBEQ);
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("beq x0, x0, endfitestbeq");
  asm volatile(
      "endfitestfaultybeq:\n"
      "addi x5, x0, 0x11\n"
      "addi x6, x0, 0x22");
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("endfitestbeq:\n");
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bge(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  // FI code target.
  pentest_set_trigger_high();
  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xef");
  asm volatile(NOP10);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile(CONDBRANCHBGE);
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("beq x0, x0, endfitestbge");
  asm volatile(
      "endfitestfaultybge:\n"
      "addi x5, x0, 0x11\n"
      "addi x6, x0, 0x22");
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("endfitestbge:\n");
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bgeu(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  // FI code target.
  pentest_set_trigger_high();
  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xef");
  asm volatile(NOP10);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile(CONDBRANCHBGEU);
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("beq x0, x0, endfitestbgeu");
  asm volatile(
      "endfitestfaultybgeu:\n"
      "addi x5, x0, 0x11\n"
      "addi x6, x0, 0x22");
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("endfitestbgeu:\n");
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_blt(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  // FI code target.
  pentest_set_trigger_high();
  asm volatile("addi x5, x0, 0xef");
  asm volatile("addi x6, x0, 0xaf");
  asm volatile(NOP10);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile(CONDBRANCHBLT);
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("beq x0, x0, endfitestblt");
  asm volatile(
      "endfitestfaultyblt:\n"
      "addi x5, x0, 0x11\n"
      "addi x6, x0, 0x22");
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("endfitestblt:\n");
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bltu(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  // FI code target.
  pentest_set_trigger_high();
  asm volatile("addi x5, x0, 0xef");
  asm volatile("addi x6, x0, 0xaf");
  asm volatile(NOP10);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile(CONDBRANCHBLTU);
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("beq x0, x0, endfitestbltu");
  asm volatile(
      "endfitestfaultybltu:\n"
      "addi x5, x0, 0x11\n"
      "addi x6, x0, 0x22");
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("endfitestbltu:\n");
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bne(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  // FI code target.
  pentest_set_trigger_high();
  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xaf");
  asm volatile(NOP10);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile(CONDBRANCHBNE);
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("beq x0, x0, endfitestbne");
  asm volatile(
      "endfitestfaultybne:\n"
      "addi x5, x0, 0x11\n"
      "addi x6, x0, 0x22");
  asm volatile("mv %0, x5" : "=r"(result1));
  asm volatile("mv %0, x6" : "=r"(result2));
  asm volatile("endfitestbne:\n");
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_csr_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Write reference value into CSR.
  CSR_WRITE(CSR_REG_MSCRATCH, ref_values[0]);

  // Init t0...t6 with 0.
  init_temp_regs(0);

  // FI code target.
  pentest_set_trigger_high();
  asm volatile(NOP10);
  asm volatile("csrr x5,mscratch");
  asm volatile("csrr x6,mscratch");
  asm volatile("csrr x7,mscratch");
  asm volatile("csrr x28,mscratch");
  asm volatile("csrr x29,mscratch");
  asm volatile("csrr x30,mscratch");
  asm volatile("csrr x31,mscratch");
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Load register values.
  // Result buffer.
  uint32_t res_values[7];
  read_temp_regs(res_values);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Compare against reference values.
  uint32_t res = 0;
  for (int i = 0; i < 7; i++) {
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

status_t handle_ibex_fi_char_csr_write(ujson_t *uj) {
  ibex_fi_test_result_t uj_output;
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Init x5 with reference value.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));

  // FI code target.
  pentest_set_trigger_high();
  asm volatile(NOP10);
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile("csrw	mscratch, x5");
  asm volatile("csrr x5,mscratch");
  asm volatile(NOP10);
  pentest_set_trigger_low();

  uint32_t res_value;
  asm volatile("mv %0, x5" : "=r"(res_value));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Compare against reference values.
  uj_output.result = 0;
  if (res_value != ref_values[0]) {
    uj_output.result = res_value;
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_flash_read(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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

  // Init t0...t6 with 0.
  init_temp_regs(0);

  // FI code target.
  pentest_set_trigger_high();
  asm volatile(NOP10);
  asm volatile("lw x5, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile("lw x6, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile("lw x7, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile("lw x28, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile("lw x29, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile("lw x30, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile("lw x31, (%0)" : : "r"((flash_bank_1.base)));
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Load register values.
  // Result buffer.
  uint32_t res_values[7];
  read_temp_regs(res_values);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Compare against reference values.
  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));

  for (uint32_t flash_pos = 0; flash_pos < 7; flash_pos++) {
    if (res_values[flash_pos] != ref_values[0]) {
      uj_output.addresses[flash_pos] = flash_pos;
      uj_output.data[flash_pos] = res_values[flash_pos];

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
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  pentest_set_trigger_high();
  // Erase flash and write page with reference values.
  TRY(flash_ctrl_testutils_erase_and_write_page(
      &flash, (uint32_t)flash_bank_1_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_hardened_check_eq_complement_branch(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Values are intentially not equal.
  // uint32_t value1 = 0;
  // uint32_t value2 = 1;
  // JH: Changed 28th June. Tests before used unharded values
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile(
    "beq" " %0, %1, .L_HARDENED_%=;" \
    ".UNIMP_%=: unimp;" \
    "bne" " %0, %1, .UNIMP_%=;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2)
  );
  // clang-format on
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_unimp(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Values are intentially not equal.
  // uint32_t value1 = 0;
  // uint32_t value2 = 1;
  // JH: Changed 28th June. Tests before used unharded values
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_2_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Values are intentially not equal.
  // uint32_t value1 = 0;
  // uint32_t value2 = 1;
  // JH: Changed 28th June. Tests before used unharded values
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_3_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Values are intentially not equal.
  // uint32_t value1 = 0;
  // uint32_t value2 = 1;
  // JH: Changed 28th June. Tests before used unharded values
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_4_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Values are intentially not equal.
  // uint32_t value1 = 0;
  // uint32_t value2 = 1;
  // JH: Changed 28th June. Tests before used unharded values
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp; unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_5_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  pentest_set_trigger_high();
  asm volatile(NOP10);
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp; unimp; unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi_char_mem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // FI code target.
  uint32_t loop_counter1 = 0;
  uint32_t loop_counter2 = 10000;
  pentest_set_trigger_high();
  asm volatile(NOP100);
  for (int loop_cnt = 0; loop_cnt < 10000; loop_cnt++) {
    asm volatile(LWADDISW1 : : "r"((uint32_t *)&loop_counter1));
    asm volatile(LWSUBISW1 : : "r"((uint32_t *)&loop_counter2));
  }
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_register_file(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  pentest_set_trigger_high();
  asm volatile(NOP1000);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t res_values[6];
  // Initialize temporary registers with reference values.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));
  asm volatile("li x6, %0" : : "i"(ref_values[1]));
  asm volatile("li x7, %0" : : "i"(ref_values[2]));
  asm volatile("li x28, %0" : : "i"(ref_values[3]));
  asm volatile("li x29, %0" : : "i"(ref_values[4]));
  asm volatile("li x30, %0" : : "i"(ref_values[5]));

  // FI code target.
  pentest_set_trigger_high();
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
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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
      uj_output.addresses[it] = 1;  // 1 indicates an error in the register at
                                    // position it
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

status_t handle_ibex_fi_char_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // FI code target.
  uint32_t loop_counter1 = 0;
  uint32_t loop_counter2 = 10000;
  pentest_set_trigger_high();
  asm volatile(INITX5);
  asm volatile(INITX6);
  asm volatile(NOP100);
  for (int loop_cnt = 0; loop_cnt < 10000; loop_cnt++) {
    asm volatile(ADDI1);
    asm volatile(SUBI1);
  }
  asm volatile("mv %0, x5" : "=r"(loop_counter1));
  asm volatile("mv %0, x6" : "=r"(loop_counter2));
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_sram_read(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Init t0...t6 with 0.
  init_temp_regs(0);

  // Write reference value into SRAM.
  sram_main_buffer[0] = ref_values[0];

  // FI code target.
  pentest_set_trigger_high();
  asm volatile(NOP10);
  // Read from SRAM into temporary registers.
  asm volatile("lw x5, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x28, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x29, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x30, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile("lw x31, (%0)" : : "r"(&sram_main_buffer[0]));
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Load register values.
  // Result buffer.
  uint32_t res_values[7];
  read_temp_regs(res_values);

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));

  for (uint32_t sram_pos = 0; sram_pos < 7; sram_pos++) {
    if (res_values[sram_pos] != ref_values[0]) {
      uj_output.addresses[sram_pos] = sram_pos;
      uj_output.data[sram_pos] = res_values[sram_pos];
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
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  pentest_set_trigger_high();
  asm volatile(NOP1000);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_sram_write(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

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
  pentest_set_trigger_high();
  for (int i = 0; i < 32; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[i]);
  }
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_sram_write_read(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Initialize SRAM region with inverse reference value.
  sram_main_buffer[0] = ~ref_values[0];

  // Init x5, x6, x6 with the reference values.
  asm volatile("li x5, %0" : : "i"(ref_values[0]));
  asm volatile("li x6, %0" : : "i"(ref_values[1]));
  asm volatile("li x7, %0" : : "i"(ref_values[2]));

  pentest_set_trigger_high();
  asm volatile(NOP10);
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile(NOP10);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  uint32_t res_values[3];
  asm volatile("mv %0, x5" : "=r"(res_values[0]));
  asm volatile("mv %0, x6" : "=r"(res_values[1]));
  asm volatile("mv %0, x7" : "=r"(res_values[2]));

  // Compare against reference values.
  ibex_fi_faulty_addresses_data_t uj_output;
  memset(uj_output.addresses, 0, sizeof(uj_output.addresses));
  memset(uj_output.data, 0, sizeof(uj_output.data));

  for (uint32_t addr = 0; addr < 3; addr++) {
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

status_t handle_ibex_fi_char_sram_write_static_unrolled(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Initialize SRAM region with inverse ref_values to avoid that data from a
  // previous run are still in memory.
  for (int i = 0; i < 64; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ~ref_values[0]);
  }

  // FI code target.
  // Unrolled for easier fault injection characterization.
  pentest_set_trigger_high();
  mmio_region_write32(sram_region_main_addr, 0 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 1 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 2 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 3 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 4 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 5 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 6 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 7 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 8 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 9 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 10 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 11 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 12 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 13 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 14 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 15 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 16 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 17 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 18 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 19 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 20 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 21 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 22 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 23 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 24 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 25 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 26 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 27 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 28 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 29 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 30 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 31 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 32 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 33 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 34 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 35 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 36 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 37 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 38 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 39 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 40 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 41 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 42 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 43 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 44 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 45 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 46 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 47 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 48 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 49 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 50 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 51 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 52 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 53 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 54 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 55 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 56 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 57 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 58 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 59 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 60 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 61 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 62 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  mmio_region_write32(sram_region_main_addr, 63 * (ptrdiff_t)sizeof(uint32_t),
                      ref_values[0]);
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read back and compare against reference values.
  uint32_t res_values[64];
  uint32_t res = 0;
  for (int i = 0; i < 64; i++) {
    res_values[i] = mmio_region_read32(sram_region_main_addr,
                                       i * (ptrdiff_t)sizeof(uint32_t));
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

status_t handle_ibex_fi_char_unconditional_branch(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // FI code target.
  uint32_t result = 0;
  pentest_set_trigger_high();
  // Init x5 register we are using for the increment.
  asm volatile(INITX5);
  // Delay the trigger.
  asm volatile(NOP10);
  // Attack target.
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("jal ra, increment_counter");
  asm volatile("mv %0, x5" : "=r"(result));
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_unconditional_branch_nop(ujson_t *uj) {
  uint32_t registers[32] = {0};
  read_all_regs(registers);
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // FI code target.
  uint32_t result = 0;
  pentest_set_trigger_high();
  // Init x5 register we are using for the increment.
  asm volatile(INITX5);
  // Delay the trigger.
  asm volatile(NOP10);
  // Attack target.
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  asm volatile("jal ra, not_increment_counter");
  read_all_regs(registers);
  asm volatile("mv %0, x5" : "=r"(result));
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_registers_t uj_output;
  uj_output.result = result;
  memcpy(uj_output.registers, registers, sizeof(registers));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_registers_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_unrolled_mem_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // FI code target.
  uint32_t loop_counter = 0;
  pentest_set_trigger_high();
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
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_unrolled_reg_op_loop(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  // FI code target.
  uint32_t loop_counter = 0;
  pentest_set_trigger_high();
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
  pentest_set_trigger_low();
  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

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

status_t handle_ibex_fi_char_unrolled_reg_op_loop_chain(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint32_t addresses[8] = {0};
  uint32_t data[8] = {0};

  // FI code target.
  pentest_set_trigger_high();
  asm volatile(INIT_TMPREGS);
  asm volatile(NOP10);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile(ADDI_CHAIN);
  asm volatile("mv %0, x5" : "=r"(data[0]));
  asm volatile("mv %0, x6" : "=r"(data[1]));
  asm volatile("mv %0, x7" : "=r"(data[2]));
  asm volatile("mv %0, x28" : "=r"(data[3]));
  asm volatile("mv %0, x29" : "=r"(data[4]));
  asm volatile("mv %0, x30" : "=r"(data[5]));
  pentest_set_trigger_low();

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send data, alerts & ERR_STATUS to host.
  ibex_fi_faulty_addresses_data_t uj_output;
  memcpy(uj_output.addresses, addresses, sizeof(addresses));
  memcpy(uj_output.data, data, sizeof(data));
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_init(ujson_t *uj) {
  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler();

  // Disable the instruction cache and dummy instructions for FI attacks.
  pentest_configure_cpu();

  // Enable the flash.
  flash_info = dif_flash_ctrl_get_device_info();
  TRY(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(flash_ctrl_testutils_wait_for_init(&flash));

  // Init OTP.
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  // Configure Ibex to allow reading ERR_STATUS register.
  TRY(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

  // Initialize flash for the flash test and write reference values into page.
  flash_init = false;
  flash_data_valid = false;
  // Initialize retention SRAM.
  sram_ret_init = false;
  // Fetch reference values from OTP before OTP tests.
  otp_ref_init = false;

  return OK_STATUS();
}

status_t handle_ibex_fi_otp_data_read(ujson_t *uj) {
  TRY(init_ref_otp_data());
  TRY(read_otp_partitions(uj));
  return OK_STATUS();
}

status_t handle_ibex_fi_otp_read_lock(ujson_t *uj) {
  TRY(init_ref_otp_data());
  TRY(dif_otp_ctrl_lock_reading(&otp, kDifOtpCtrlPartitionVendorTest));
  TRY(dif_otp_ctrl_lock_reading(&otp, kDifOtpCtrlPartitionCreatorSwCfg));
  TRY(dif_otp_ctrl_lock_reading(&otp, kDifOtpCtrlPartitionOwnerSwCfg));

  TRY(read_otp_partitions(uj));

  return OK_STATUS();
}

status_t handle_ibex_fi_otp_write_lock(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();

  uint64_t faulty_token[kSecret0TestUnlockTokenSizeIn64BitWords];
  for (size_t i = 0; i < kSecret0TestUnlockTokenSizeIn64BitWords; i++) {
    faulty_token[i] = 0xdeadbeef;
  }
  pentest_set_trigger_high();
  asm volatile(NOP10);
  TRY(otp_ctrl_testutils_dai_write64(
      &otp, kDifOtpCtrlPartitionSecret0, kSecret0TestUnlockTokenOffset,
      faulty_token, kSecret0TestUnlockTokenSizeIn64BitWords));
  asm volatile(NOP10);
  pentest_set_trigger_low();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result =
      0;  // Writing to the locked OTP partition crashes the chip.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_ibex_fi(ujson_t *uj) {
  ibex_fi_subcommand_t cmd;
  TRY(ujson_deserialize_ibex_fi_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kIbexFiSubcommandAddressTranslation:
      return handle_ibex_fi_address_translation(uj);
    case kIbexFiSubcommandAddressTranslationCfg:
      return handle_ibex_fi_address_translation_config(uj);
    case kIbexFiSubcommandCharCondBranchBeq:
      return handle_ibex_fi_char_conditional_branch_beq(uj);
    case kIbexFiSubcommandCharCondBranchBge:
      return handle_ibex_fi_char_conditional_branch_bge(uj);
    case kIbexFiSubcommandCharCondBranchBgeu:
      return handle_ibex_fi_char_conditional_branch_bgeu(uj);
    case kIbexFiSubcommandCharCondBranchBlt:
      return handle_ibex_fi_char_conditional_branch_blt(uj);
    case kIbexFiSubcommandCharCondBranchBltu:
      return handle_ibex_fi_char_conditional_branch_bltu(uj);
    case kIbexFiSubcommandCharCondBranchBne:
      return handle_ibex_fi_char_conditional_branch_bne(uj);
    case kIbexFiSubcommandCharCsrRead:
      return handle_ibex_fi_char_csr_read(uj);
    case kIbexFiSubcommandCharCsrWrite:
      return handle_ibex_fi_char_csr_write(uj);
    case kIbexFiSubcommandCharFlashRead:
      return handle_ibex_fi_char_flash_read(uj);
    case kIbexFiSubcommandCharFlashWrite:
      return handle_ibex_fi_char_flash_write(uj);
    case kIbexFiSubcommandCharHardenedCheckComplementBranch:
      return handle_ibex_fi_char_hardened_check_eq_complement_branch(uj);
    case kIbexFiSubcommandCharHardenedCheckUnimp:
      return handle_ibex_fi_char_hardened_check_eq_unimp(uj);
    case kIbexFiSubcommandCharHardenedCheck2Unimps:
      return handle_ibex_fi_char_hardened_check_eq_2_unimps(uj);
    case kIbexFiSubcommandCharHardenedCheck3Unimps:
      return handle_ibex_fi_char_hardened_check_eq_3_unimps(uj);
    case kIbexFiSubcommandCharHardenedCheck4Unimps:
      return handle_ibex_fi_char_hardened_check_eq_4_unimps(uj);
    case kIbexFiSubcommandCharHardenedCheck5Unimps:
      return handle_ibex_fi_char_hardened_check_eq_5_unimps(uj);
    case kIbexFiSubcommandCharMemOpLoop:
      return handle_ibex_fi_char_mem_op_loop(uj);
    case kIbexFiSubcommandCharRegisterFile:
      return handle_ibex_fi_char_register_file(uj);
    case kIbexFiSubcommandCharRegisterFileRead:
      return handle_ibex_fi_char_register_file_read(uj);
    case kIbexFiSubcommandCharRegOpLoop:
      return handle_ibex_fi_char_reg_op_loop(uj);
    case kIbexFiSubcommandCharSramRead:
      return handle_ibex_fi_char_sram_read(uj);
    case kIbexFiSubcommandCharSramStatic:
      return handle_ibex_fi_char_sram_static(uj);
    case kIbexFiSubcommandCharSramWrite:
      return handle_ibex_fi_char_sram_write(uj);
    case kIbexFiSubcommandCharSramWriteRead:
      return handle_ibex_fi_char_sram_write_read(uj);
    case kIbexFiSubcommandCharSramWriteStaticUnrolled:
      return handle_ibex_fi_char_sram_write_static_unrolled(uj);
    case kIbexFiSubcommandCharUncondBranch:
      return handle_ibex_fi_char_unconditional_branch(uj);
    case kIbexFiSubcommandCharUncondBranchNop:
      return handle_ibex_fi_char_unconditional_branch_nop(uj);
    case kIbexFiSubcommandCharUnrolledMemOpLoop:
      return handle_ibex_fi_char_unrolled_mem_op_loop(uj);
    case kIbexFiSubcommandCharUnrolledRegOpLoop:
      return handle_ibex_fi_char_unrolled_reg_op_loop(uj);
    case kIbexFiSubcommandCharUnrolledRegOpLoopChain:
      return handle_ibex_fi_char_unrolled_reg_op_loop_chain(uj);
    case kIbexFiSubcommandInit:
      return handle_ibex_fi_init(uj);
    case kIbexFiSubcommandOtpDataRead:
      return handle_ibex_fi_otp_data_read(uj);
    case kIbexFiSubcommandOtpReadLock:
      return handle_ibex_fi_otp_read_lock(uj);
    case kIbexFiSubcommandOtpWriteLock:
      return handle_ibex_fi_otp_write_lock(uj);
    default:
      LOG_ERROR("Unrecognized IBEX FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
