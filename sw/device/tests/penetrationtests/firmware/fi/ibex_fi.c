// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/fi/ibex_fi.h"

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/abs_mmio.h"
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

// Generated
#include "aes_regs.h"
#include "alert_handler_regs.h"
#include "csrng_regs.h"
#include "edn_regs.h"
#include "entropy_src_regs.h"
#include "hmac_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"
#include "sram_ctrl_regs.h"

enum {
  /**
   * Size (in number of 32-bit words) of the buffer that is allocated in the
   * SRAM. This buffer is used by various SRAM tests.
   */
  kSramMainBufSize =
      1 << 13,  // Size of the SRAM buffer used in the SRAM tests.
  /**
   * Number of reference values that are available in the ref_values array.
   */
  kNumRefValues = 32,
  /**
   * Number of values used for the sram_write_read_alt test.
   */
  kSramWriteReadAltNumValues = 16,
};

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

// Interface to retention SRAM.
static dif_sram_ctrl_t ret_sram;

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

// CharFlash config parameters.
static uint32_t flash_region_index;
static uint32_t flash_test_page_addr;

// Cond. branch macros.
#define CONDBRANCHBEQ "beq x5, x6, endfitestfaultybeq\n"
#define CONDBRANCHBNE "bne x5, x6, endfitestfaultybne\n"
#define CONDBRANCHBGE "bge x5, x6, endfitestfaultybge\n"
#define CONDBRANCHBGEU "bgeu x5, x6, endfitestfaultybgeu\n"
#define CONDBRANCHBLT "blt x5, x6, endfitestfaultyblt\n"
#define CONDBRANCHBLTU "bltu x5, x6, endfitestfaultybltu\n"

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

// Reference values used by different FI tests.
const uint32_t ref_values[kNumRefValues] = {
    0x1BADB002, 0x8BADF00D, 0xA5A5A5A5, 0xABABABAB, 0xABBABABE, 0xABADCAFE,
    0xBAAAAAAD, 0xBAD22222, 0xBBADBEEF, 0xBEBEBEBE, 0xBEEFCACE, 0xC00010FF,
    0xCAFED00D, 0xCAFEFEED, 0xCCCCCCCC, 0xCDCDCDCD, 0x0D15EA5E, 0xDEAD10CC,
    0xDEADBEEF, 0xDEADCAFE, 0xDEADC0DE, 0xDEADFA11, 0xDEADF00D, 0xDEFEC8ED,
    0xDEADDEAD, 0xD00D2BAD, 0xEBEBEBEB, 0xFADEDEAD, 0xFDFDFDFD, 0xFEE1DEAD,
    0xFEEDFACE, 0xFEEEFEEE};

// variables to hold register values
uint32_t registers_saved[IBEXFI_NUM_REGS];
uint32_t registers_dumped[IBEXFI_NUM_REGS];

/**
 * Initialize the register file with the ref_values.
 *
 * This inline function pre-initializes the register file with the ref_values
 * before a FI test. All registers except x0 (zero register), x2 (stack
 * pointer), and x8 (frame pointer) are written. The idea of bringing the
 * register file to a pre-defined state is to more easily detect any potential
 * bit-flip that was introduced by FI.
 */
OT_ALWAYS_INLINE void init_reg_ref_values(void) {
  asm volatile("li x1, %0" : : "i"(ref_values[kRegX1]));
  asm volatile("li x3, %0" : : "i"(ref_values[kRegX3]));
  asm volatile("li x4, %0" : : "i"(ref_values[kRegX4]));
  asm volatile("li x5, %0" : : "i"(ref_values[kRegX5]));
  asm volatile("li x6, %0" : : "i"(ref_values[kRegX6]));
  asm volatile("li x7, %0" : : "i"(ref_values[kRegX7]));
  asm volatile("li x9, %0" : : "i"(ref_values[kRegX9]));
  asm volatile("li x10, %0" : : "i"(ref_values[kRegX10]));
  asm volatile("li x11, %0" : : "i"(ref_values[kRegX11]));
  asm volatile("li x12, %0" : : "i"(ref_values[kRegX12]));
  asm volatile("li x13, %0" : : "i"(ref_values[kRegX13]));
  asm volatile("li x14, %0" : : "i"(ref_values[kRegX14]));
  asm volatile("li x15, %0" : : "i"(ref_values[kRegX15]));
  asm volatile("li x16, %0" : : "i"(ref_values[kRegX16]));
  asm volatile("li x17, %0" : : "i"(ref_values[kRegX17]));
  asm volatile("li x18, %0" : : "i"(ref_values[kRegX18]));
  asm volatile("li x19, %0" : : "i"(ref_values[kRegX19]));
  asm volatile("li x20, %0" : : "i"(ref_values[kRegX20]));
  asm volatile("li x21, %0" : : "i"(ref_values[kRegX21]));
  asm volatile("li x22, %0" : : "i"(ref_values[kRegX22]));
  asm volatile("li x23, %0" : : "i"(ref_values[kRegX23]));
  asm volatile("li x24, %0" : : "i"(ref_values[kRegX24]));
  asm volatile("li x25, %0" : : "i"(ref_values[kRegX25]));
  asm volatile("li x26, %0" : : "i"(ref_values[kRegX26]));
  asm volatile("li x27, %0" : : "i"(ref_values[kRegX27]));
  asm volatile("li x28, %0" : : "i"(ref_values[kRegX28]));
  asm volatile("li x29, %0" : : "i"(ref_values[kRegX29]));
  asm volatile("li x30, %0" : : "i"(ref_values[kRegX30]));
  asm volatile("li x31, %0" : : "i"(ref_values[kRegX31]));
}

/**
 * Initialize the temporary and function argument registers with the ref_values.
 *
 * This inline function pre-initializes the temporary and some function argument
 * registers in the RF with the ref_values. This includes x5...x7, x12...x17,
 * and x28...x31.
 */
OT_ALWAYS_INLINE void init_tmp_reg_ref_values(void) {
  asm volatile("li x5, %0" : : "i"(ref_values[kRegX5]));
  asm volatile("li x6, %0" : : "i"(ref_values[kRegX6]));
  asm volatile("li x7, %0" : : "i"(ref_values[kRegX7]));

  asm volatile("li x12, %0" : : "i"(ref_values[kRegX12]));
  asm volatile("li x13, %0" : : "i"(ref_values[kRegX13]));
  asm volatile("li x14, %0" : : "i"(ref_values[kRegX14]));
  asm volatile("li x15, %0" : : "i"(ref_values[kRegX15]));
  asm volatile("li x16, %0" : : "i"(ref_values[kRegX16]));
  asm volatile("li x17, %0" : : "i"(ref_values[kRegX17]));

  asm volatile("li x28, %0" : : "i"(ref_values[kRegX28]));
  asm volatile("li x29, %0" : : "i"(ref_values[kRegX29]));
  asm volatile("li x30, %0" : : "i"(ref_values[kRegX30]));
  asm volatile("li x31, %0" : : "i"(ref_values[kRegX31]));
}

/**
 * Save the content of the register file (x0...x31) into the buffer.
 *
 * This function can be used to save the register file state before and after
 * the FI trigger window. Call this function before init_reg_ref_values() such
 * that the register file content can be restored after the FI test. After a FI
 * test this function can be used to dump the register file content to detect
 * any differences.
 *
 * @param buffer: The buffer to store the register file content.
 */
OT_ALWAYS_INLINE void save_all_regs(uint32_t buffer[]) {
  asm volatile("sw x0,    0(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x1,    4(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x2,    8(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x3,   12(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x4,   16(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x5,   20(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x6,   24(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x7,   28(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x8,   32(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x9,   36(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x10,  40(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x11,  44(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x12,  48(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x13,  52(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x14,  56(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x15,  60(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x16,  64(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x17,  68(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x18,  72(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x19,  76(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x20,  80(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x21,  84(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x22,  88(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x23,  92(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x24,  96(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x25, 100(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x26, 104(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x27, 108(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x28, 112(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x29, 116(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x30, 120(%0)" : : "r"(&buffer[0]));
  asm volatile("sw x31, 124(%0)" : : "r"(&buffer[0]));
}

/**
 * Initialize the temporary and function argument registers with the ref_values.
 *
 * This inline function pre-initializes the temporary and some function argument
 * registers in the RF with the ref_values. This includes x5...x7, x12...x17,
 * and x28...x31.
 */

/**
 * Save the content of the temporary and function argument registers into the
 * buffer.
 *
 * This includes x5...x7, x12...x17, and x28...x31.
 *
 * @param buffer: The buffer to store the register file content.
 */
OT_ALWAYS_INLINE void save_tmp_regs(uint32_t buffer[]) {
  asm volatile("mv %0, x5" : "=r"(buffer[kRegX5]));
  asm volatile("mv %0, x6" : "=r"(buffer[kRegX6]));
  asm volatile("mv %0, x7" : "=r"(buffer[kRegX7]));

  asm volatile("mv %0, x12" : "=r"(buffer[kRegX12]));
  asm volatile("mv %0, x13" : "=r"(buffer[kRegX13]));
  asm volatile("mv %0, x14" : "=r"(buffer[kRegX14]));
  asm volatile("mv %0, x15" : "=r"(buffer[kRegX15]));
  asm volatile("mv %0, x16" : "=r"(buffer[kRegX16]));
  asm volatile("mv %0, x17" : "=r"(buffer[kRegX17]));

  asm volatile("mv %0, x28" : "=r"(buffer[kRegX28]));
  asm volatile("mv %0, x29" : "=r"(buffer[kRegX29]));
  asm volatile("mv %0, x30" : "=r"(buffer[kRegX30]));
  asm volatile("mv %0, x31" : "=r"(buffer[kRegX31]));
}

/**
 * Restore the content of the register file (x0...x31) from the buffer.
 *
 * @param buffer: The buffer to store the register file content.
 */
OT_ALWAYS_INLINE void restore_all_regs(uint32_t buffer[]) {
  asm volatile("lw x0,    0(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x1,    4(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x2,    8(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x3,   12(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x4,   16(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x5,   20(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x6,   24(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x7,   28(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x8,   32(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x9,   36(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x10,  40(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x11,  44(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x12,  48(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x13,  52(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x14,  56(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x15,  60(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x16,  64(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x17,  68(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x18,  72(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x19,  76(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x20,  80(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x21,  84(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x22,  88(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x23,  92(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x24,  96(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x25, 100(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x26, 104(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x27, 108(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x28, 112(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x29, 116(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x30, 120(%0)" : : "r"(&buffer[0]));
  asm volatile("lw x31, 124(%0)" : : "r"(&buffer[0]));
}

// Save the current register file content and initialize it with pre-defined
// values.
#define INIT_REGISTER_FILE                              \
  memset(registers_saved, 0, sizeof(registers_dumped)); \
  save_all_regs(registers_saved);                       \
  init_reg_ref_values();                                \
  uint32_t registers_dumped[IBEXFI_NUM_REGS];

// Init the temporary registers with reference values.
#define INIT_TMP_REGISTER_FILE                           \
  memset(registers_dumped, 0, sizeof(registers_dumped)); \
  init_tmp_reg_ref_values();

// Save the current register file content and restore it wit the saved
// values.
#define DUMP_REGISTER_FILE         \
  save_all_regs(registers_dumped); \
  restore_all_regs(registers_saved);

// Save the temporary registers.
#define DUMP_TMP_REGISTER_FILE save_tmp_regs(registers_dumped);

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
static volatile uint32_t sram_main_buffer[kSramMainBufSize];

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

static status_t read_otp_partitions(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

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

  for (size_t i = 0; i < ((OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE -
                           OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_SIZE) /
                          sizeof(uint32_t));
       i++) {
    if (otp_data_read_ref_creator_sw_cfg[i] !=
        otp_data_read_res_creator_sw_cfg[i]) {
      res |= 2;
    }
  }

  for (size_t i = 0; i < ((OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
                           OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
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
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

// Make sure that this function does not get optimized by the compiler.
void not_increment_counter(void) __attribute__((optnone)) {
  asm volatile("ret");
  asm volatile(ADDI10);
}

status_t handle_ibex_fi_address_translation(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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
  dif_result_t status = dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationIBus, increment_100x10_mapping);
  if (status == kDifLocked) {
    LOG_INFO("address translation locked");
    ibex_fi_empty_t uj_output;
    uj_output.success = false;
    RESP_OK(ujson_serialize_ibex_fi_empty_t, uj, &uj_output);
    return OK_STATUS();
  }
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
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

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
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_address_translation_config(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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
  dif_result_t status = dif_rv_core_ibex_configure_addr_translation(
      &rv_core_ibex, kDifRvCoreIbexAddrTranslationSlot_0,
      kDifRvCoreIbexAddrTranslationIBus, mapping1);
  if (status == kDifLocked) {
    LOG_INFO("address translation locked");
    ibex_fi_empty_t uj_output;
    uj_output.success = false;
    RESP_OK(ujson_serialize_ibex_fi_empty_t, uj, &uj_output);
    return OK_STATUS();
  }

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
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

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
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_addi_single_beq(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Init x5 and x6.
  asm volatile("li x5, 0x1a\n");
  asm volatile("li x6, 0x1a\n");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "c.addi x12, 1\n"
      "c.addi x13, 1\n"
      "c.addi x14, 1\n"
      "c.addi x15, 1\n"
      "c.addi x16, 1\n"
      "c.addi x17, 1\n"
      "c.addi x28, 1\n"
      "c.addi x29, 1\n"
      "c.addi x30, 1\n"
      "c.addi x31, 1\n"
      "beq x5, x6, correctaddibeq\n"
      "c.addi x12, 16\n"
      "c.addi x13, 16\n"
      "c.addi x14, 16\n"
      "c.addi x15, 16\n"
      "c.addi x16, 16\n"
      "c.addi x17, 16\n"
      "c.addi x28, 16\n"
      "c.addi x29, 16\n"
      "c.addi x30, 16\n"
      "c.addi x31, 16\n"
      "j badaddibeq\n"
      "correctaddibeq:\n"
      "addi x5, x5, 0x11\n"
      "addi x6, x6, 0x22\n"
      "badaddibeq:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  // If there is a mismatch, set data_faulty to true and return the
  // faulty value.
  if (registers_dumped[kRegX5] != (0x11 + 0x1a)) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }

  if (registers_dumped[kRegX6] != (0x22 + 0x1a)) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_addi_single_beq_cm(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // As this test is expected to crash, pull down the trigger to low to avoid
  // that it is still at high.
  PENTEST_ASM_TRIGGER_LOW;
  asm volatile(NOP100);

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Those values are on purpose different such that the hardened check fails.
  volatile hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  volatile hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "c.addi x12, 1\n"
      "c.addi x13, 1\n"
      "c.addi x14, 1\n"
      "c.addi x15, 1\n"
      "c.addi x16, 1\n"
      "c.addi x17, 1\n"
      "c.addi x28, 1\n"
      "c.addi x29, 1\n"
      "c.addi x30, 1\n"
      "c.addi x31, 1\n");
  HARDENED_CHECK_EQ(value1, value2);
  asm volatile(
      "c.addi x12, 16\n"
      "c.addi x13, 16\n"
      "j labelend\n"
      "j labelend\n"
      "c.addi x14, 16\n"
      "j labelend\n"
      "c.addi x15, 16\n"
      "j labelend\n"
      "c.addi x16, 16\n"
      "j labelend\n"
      "j labelend\n"
      "j labelend\n"
      "c.addi x17, 16\n"
      "c.addi x28, 16\n"
      "j labelend\n"
      "j labelend\n"
      "c.addi x29, 16\n"
      "c.addi x30, 16\n"
      "c.addi x31, 16\n"
      "labelend:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_rf_dump_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_rf_dump_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_addi_single_beq_cm2(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // As this test is expected to crash, pull down the trigger to low to avoid
  // that it is still at high.
  PENTEST_ASM_TRIGGER_LOW;
  asm volatile(NOP100);

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Those values are on purpose different such that the hardened check fails.
  volatile hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  volatile hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "c.addi x12, 1\n"
      "c.addi x13, 1\n"
      "c.addi x14, 1\n"
      "c.addi x15, 1\n"
      "c.addi x16, 1\n"
      "c.addi x17, 1\n"
      "c.addi x28, 1\n"
      "c.addi x29, 1\n"
      "c.addi x30, 1\n"
      "c.addi x31, 1\n"
      "mv a0, %0\n"
      "mv a1, %1\n"
      "beq a0,a1,cm2_fault\n"
      "cm2_correct:\n"
      "unimp\n"
      "unimp\n"
      "bne a0,a1,cm2_correct\n"
      "cm2_fault:\n"
      "c.addi x12, 16\n"
      "c.addi x13, 16\n"
      "j labelend2\n"
      "j labelend2\n"
      "c.addi x14, 16\n"
      "j labelend2\n"
      "c.addi x15, 16\n"
      "j labelend2\n"
      "c.addi x16, 16\n"
      "j labelend2\n"
      "j labelend2\n"
      "j labelend2\n"
      "c.addi x17, 16\n"
      "c.addi x28, 16\n"
      "j labelend2\n"
      "j labelend2\n"
      "c.addi x29, 16\n"
      "c.addi x30, 16\n"
      "c.addi x31, 16\n"
      "labelend2:\n"
      : "=r"(value1), "=r"(value2));
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_rf_dump_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_rf_dump_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_addi_single_beq_neg(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the registers used in the FI trigger window (x5, x6) to constants.
  asm volatile("li x5, 0x1a\n");
  asm volatile("li x6, 0x0f\n");

  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "c.addi x12, 1\n"
      "c.addi x13, 1\n"
      "c.addi x14, 1\n"
      "c.addi x15, 1\n"
      "c.addi x16, 1\n"
      "c.addi x17, 1\n"
      "c.addi x28, 1\n"
      "c.addi x29, 1\n"
      "c.addi x30, 1\n"
      "c.addi x31, 1\n"
      "beq x5, x6, badbeqneg\n"
      "c.addi x12, 16\n"
      "c.addi x13, 16\n"
      "c.addi x14, 16\n"
      "c.addi x15, 16\n"
      "c.addi x16, 16\n"
      "c.addi x17, 16\n"
      "c.addi x28, 16\n"
      "c.addi x29, 16\n"
      "c.addi x30, 16\n"
      "c.addi x31, 16\n"
      "j correctbeqneg\n"
      "badbeqneg:\n"
      "addi x5, x5, 0x11\n"
      "addi x6, x6, 0x22\n"
      "correctbeqneg:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  // If there is a mismatch, set data_faulty to true and return the
  // faulty value.
  if (registers_dumped[kRegX5] != 0x1a) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }

  if (registers_dumped[kRegX6] != 0x0f) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_addi_single_bne(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the registers used in the FI trigger window (x5, x6) to constants.
  asm volatile("li x5, 0x1a\n");
  asm volatile("li x6, 0x0a\n");

  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "c.addi x12, 1\n"
      "c.addi x13, 1\n"
      "c.addi x14, 1\n"
      "c.addi x15, 1\n"
      "c.addi x16, 1\n"
      "c.addi x17, 1\n"
      "c.addi x28, 1\n"
      "c.addi x29, 1\n"
      "c.addi x30, 1\n"
      "c.addi x31, 1\n"
      "bne x5, x6, correctaddibne\n"
      "c.addi x12, 16\n"
      "c.addi x13, 16\n"
      "c.addi x14, 16\n"
      "c.addi x15, 16\n"
      "c.addi x16, 16\n"
      "c.addi x17, 16\n"
      "c.addi x28, 16\n"
      "c.addi x29, 16\n"
      "c.addi x30, 16\n"
      "c.addi x31, 16\n"
      "j badaddibne\n"
      "correctaddibne:\n"
      "addi x5, x5, 0x11\n"
      "addi x6, x6, 0x22\n"
      "badaddibne:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  // If there is a mismatch, set data_faulty to true and return the
  // faulty value.
  if (registers_dumped[kRegX5] != (0x11 + 0x1a)) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }

  if (registers_dumped[kRegX6] != (0x22 + 0x0a)) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_addi_single_bne_neg(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the registers used in the FI trigger window (x5, x6) to a constant.
  asm volatile("li x5, 0x1a\n");
  asm volatile("li x6, 0x1a\n");

  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "c.addi x12, 1\n"
      "c.addi x13, 1\n"
      "c.addi x14, 1\n"
      "c.addi x15, 1\n"
      "c.addi x16, 1\n"
      "c.addi x17, 1\n"
      "c.addi x28, 1\n"
      "c.addi x29, 1\n"
      "c.addi x30, 1\n"
      "c.addi x31, 1\n"
      "bne x5, x6, badbneneg\n"
      "c.addi x12, 16\n"
      "c.addi x13, 16\n"
      "c.addi x14, 16\n"
      "c.addi x15, 16\n"
      "c.addi x16, 16\n"
      "c.addi x17, 16\n"
      "c.addi x28, 16\n"
      "c.addi x29, 16\n"
      "c.addi x30, 16\n"
      "c.addi x31, 16\n"
      "j correctbneneg\n"
      "badbneneg:\n"
      "addi x5, x5, 0x11\n"
      "addi x6, x6, 0x22\n"
      "correctbneneg:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  // If there is a mismatch, set data_faulty to true and return the
  // faulty value.
  if (registers_dumped[kRegX5] != 0x1a) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }

  if (registers_dumped[kRegX6] != 0x1a) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_combi(ujson_t *uj) __attribute__((optnone)) {
  //////////// TEST 1

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  // Init the used registers.
  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xaf");

  asm volatile("addi x12, x0, 0xa0");
  asm volatile("addi x13, x0, 0x0f");

  asm volatile("addi x14, x0, 0x01");
  asm volatile("addi x15, x0, 0x03");

  asm volatile("addi x16, x0, 0x0a");
  asm volatile("addi x17, x0, 0x1c");

  asm volatile("addi x28, x0, 0xa2");
  asm volatile("addi x29, x0, 0x05");

  asm volatile("addi x30, x0, 0xc4");
  asm volatile("addi x31, x0, 0x07");

  asm volatile("addi x7, x0, 0");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "bne x5, x6, endcombifaultybne\n"
      "bne x5, x6, endcombifaultybne\n"
      "bne x5, x6, endcombifaultybne\n"
      "bne x5, x6, endcombifaultybne\n"
      "bne x5, x6, endcombifaultybne\n"
      "bne x5, x6, endcombifaultybne\n"

      "beq x12, x13, endcombifaultybeq\n"
      "beq x12, x13, endcombifaultybeq\n"
      "beq x12, x13, endcombifaultybeq\n"
      "beq x12, x13, endcombifaultybeq\n"
      "beq x12, x13, endcombifaultybeq\n"
      "beq x12, x13, endcombifaultybeq\n"

      "bge x14, x15, endcombifaultybge\n"
      "bge x14, x15, endcombifaultybge\n"
      "bge x14, x15, endcombifaultybge\n"
      "bge x14, x15, endcombifaultybge\n"
      "bge x14, x15, endcombifaultybge\n"
      "bge x14, x15, endcombifaultybge\n"

      "bgeu x16, x17, endcombifaultybgeu\n"
      "bgeu x16, x17, endcombifaultybgeu\n"
      "bgeu x16, x17, endcombifaultybgeu\n"
      "bgeu x16, x17, endcombifaultybgeu\n"
      "bgeu x16, x17, endcombifaultybgeu\n"
      "bgeu x16, x17, endcombifaultybgeu\n"

      "blt x28, x29, endcombifaultyblt\n"
      "blt x28, x29, endcombifaultyblt\n"
      "blt x28, x29, endcombifaultyblt\n"
      "blt x28, x29, endcombifaultyblt\n"
      "blt x28, x29, endcombifaultyblt\n"
      "blt x28, x29, endcombifaultyblt\n"

      "bltu x30, x31, endcombifaultybltu\n"
      "bltu x30, x31, endcombifaultybltu\n"
      "bltu x30, x31, endcombifaultybltu\n"
      "bltu x30, x31, endcombifaultybltu\n"
      "bltu x30, x31, endcombifaultybltu\n"
      "bltu x30, x31, endcombifaultybltu\n"

      NOP100

      "j endcombicorrect\n"

      "endcombifaultybne:\n"
      "addi x5, x5, 0x1\n"
      "addi x6, x6, 0x1\n"
      "j endcombicorrect\n"

      "endcombifaultybeq:\n"
      "addi x12, x12, 0x1\n"
      "addi x13, x13, 0x1\n"
      "j endcombicorrect\n"

      "endcombifaultybge:\n"
      "addi x14, x14, 0x1\n"
      "addi x15, x15, 0x1\n"
      "j endcombicorrect\n"

      "endcombifaultybgeu:\n"
      "addi x16, x16, 0x1\n"
      "addi x17, x17, 0x1\n"
      "j endcombicorrect\n"

      "endcombifaultyblt:\n"
      "addi x28, x28, 0x1\n"
      "addi x29, x29, 0x1\n"
      "j endcombicorrect\n"

      "endcombifaultybltu:\n"
      "addi x30, x30, 0x1\n"
      "addi x31, x31, 0x1\n"

      "endcombicorrect:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  uint32_t registers_dumped_test_1[IBEXFI_NUM_REGS];
  memcpy(registers_dumped_test_1, registers_dumped, sizeof(registers_dumped));

  //////////////// TEST 2

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  asm volatile("addi x5, x0, 0");
  asm volatile("addi x6, x0, 0");
  asm volatile("addi x7, x0, 0");
  asm volatile("addi x12, x0, 0");
  asm volatile("addi x13, x0, 0");
  asm volatile("addi x14, x0, 0");
  asm volatile("addi x15, x0, 0");
  asm volatile("addi x16, x0, 0");
  asm volatile("addi x17, x0, 0");
  asm volatile("addi x28, x0, 0");
  asm volatile("addi x29, x0, 0");
  asm volatile("addi x30, x0, 0");
  asm volatile("addi x31, x0, 0");

  uint32_t counter = 0;

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(
      "lw x5, (%0)\n addi x5, x5, 1\n sw x5, (%0)\n"
      "lw x6, (%0)\n addi x6, x6, 1\n sw x6, (%0)\n"
      "lw x7, (%0)\n addi x7, x7, 1\n sw x7, (%0)\n"
      "lw x12, (%0)\n addi x12, x12, 1\n sw x12, (%0)\n"
      "lw x13, (%0)\n addi x13, x13, 1\n sw x13, (%0)\n"
      "lw x14, (%0)\n addi x14, x14, 1\n sw x14, (%0)\n"
      "lw x15, (%0)\n addi x15, x15, 1\n sw x15, (%0)\n"
      "lw x16, (%0)\n addi x16, x16, 1\n sw x16, (%0)\n"
      "lw x17, (%0)\n addi x17, x17, 1\n sw x17, (%0)\n"
      "lw x28, (%0)\n addi x28, x28, 1\n sw x28, (%0)\n"
      "lw x29, (%0)\n addi x29, x29, 1\n sw x29, (%0)\n"
      "lw x30, (%0)\n addi x30, x30, 1\n sw x30, (%0)\n"
      "lw x31, (%0)\n addi x31, x31, 1\n sw x31, (%0)\n"
      :
      : "r"((uint32_t *)&counter));
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  uint32_t registers_dumped_test_2[IBEXFI_NUM_REGS];
  memcpy(registers_dumped_test_2, registers_dumped, sizeof(registers_dumped));

  ////////// TEST 3

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  // Init x5 register we are using for the increment.
  asm volatile(INITX5);

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  uint32_t registers_dumped_test_3[IBEXFI_NUM_REGS];
  memcpy(registers_dumped_test_3, registers_dumped, sizeof(registers_dumped));

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  dif_rv_core_ibex_error_status_t codes;

  // Read ERR_STATUS register.
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_combi_data_t uj_test_output;

  // Return the results for the first test.
  // Preset buffers to 0.
  memset(uj_test_output.data_faulty_test_1, false,
         sizeof(uj_test_output.data_faulty_test_1));
  memset(uj_test_output.data_test_1, 0, sizeof(uj_test_output.data_test_1));
  memset(uj_test_output.registers_test_1, 0,
         sizeof(uj_test_output.registers_test_1));
  // Return register file from the first test dump back to host.
  memcpy(uj_test_output.registers_test_1, registers_dumped_test_1,
         sizeof(registers_dumped_test_1));
  // Check the content of x5, x6, x12-x17, x28-x31.
  size_t compare_regs[12] = {kRegX5,  kRegX6,  kRegX12, kRegX13,
                             kRegX14, kRegX15, kRegX16, kRegX17,
                             kRegX28, kRegX29, kRegX30, kRegX31};
  size_t expected_values[12] = {0xaf, 0xaf, 0xa0, 0x0f, 0x01, 0x03,
                                0x0a, 0x1c, 0xa2, 0x05, 0xc4, 0x07};
  for (size_t it = 0; it < 12; it++) {
    if (registers_dumped_test_1[compare_regs[it]] != expected_values[it]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_test_output.data_faulty_test_1[it] = true;
      uj_test_output.data_test_1[it] =
          registers_dumped_test_1[compare_regs[it]];
    }
  }

  // Return the results from the second test.
  memset(uj_test_output.registers_test_2, 0,
         sizeof(uj_test_output.registers_test_2));
  // Return register file dump back to host.
  memcpy(uj_test_output.registers_test_2, registers_dumped_test_2,
         sizeof(registers_dumped_test_2));
  // Return counter back to host.
  uj_test_output.result_test_2 = counter;

  // Return the results from the third test.
  // Return result and registers back to host.
  memset(uj_test_output.registers_test_3, 0,
         sizeof(uj_test_output.registers_test_3));
  // Return register file dump back to host.
  memcpy(uj_test_output.registers_test_3, registers_dumped_test_3,
         sizeof(registers_dumped_test_3));
  // Return x5 back to host.
  uj_test_output.result_test_3 = registers_dumped_test_3[kRegX5];
  // Send loop counters & ERR_STATUS to host.
  uj_test_output.err_status = codes;
  memcpy(uj_test_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_test_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_test_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));

  // Send over the response
  RESP_OK(ujson_serialize_ibex_fi_combi_data_t, uj, &uj_test_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_beq(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xef");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bge(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xef");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bgeu(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xef");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_blt(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  asm volatile("addi x5, x0, 0xef");
  asm volatile("addi x6, x0, 0xaf");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bltu(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  asm volatile("addi x5, x0, 0xef");
  asm volatile("addi x6, x0, 0xaf");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_conditional_branch_bne(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t result1 = 0;
  uint32_t result2 = 0;

  asm volatile("addi x5, x0, 0xaf");
  asm volatile("addi x6, x0, 0xaf");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW
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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send loop counters & ERR_STATUS to host.
  ibex_fi_test_result_mult_t uj_output;
  uj_output.result1 = result1;
  uj_output.result2 = result2;
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_csr_read(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Write reference value into CSR.
  CSR_WRITE(CSR_REG_MSCRATCH, ref_values[0]);

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile("csrr x5,mscratch");
  asm volatile("csrr x6,mscratch");
  asm volatile("csrr x7,mscratch");
  asm volatile("csrr x12,mscratch");
  asm volatile("csrr x13,mscratch");
  asm volatile("csrr x14,mscratch");
  asm volatile("csrr x15,mscratch");
  asm volatile("csrr x16,mscratch");
  asm volatile("csrr x17,mscratch");
  asm volatile("csrr x28,mscratch");
  asm volatile("csrr x29,mscratch");
  asm volatile("csrr x30,mscratch");
  asm volatile("csrr x31,mscratch");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Compare against reference values.
  size_t compare_regs[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {
      kRegX5,  kRegX6,  kRegX7,  kRegX12, kRegX13, kRegX14, kRegX15,
      kRegX16, kRegX17, kRegX28, kRegX29, kRegX30, kRegX31};
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[0]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send alerts back to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_csr_write(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Compare against reference values.
  ibex_fi_test_result_t uj_output;
  // Compare x5 with the expected value.
  uj_output.result = 0;
  if (registers_dumped[kRegX5] != ref_values[kRegX5]) {
    uj_output.result = registers_dumped[kRegX5];
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Return register file dump back to host.
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send res & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_csr_combi(ujson_t *uj) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Read the trigger data and the reference values
  ibex_fi_csr_combi_in_t uj_data;
  TRY(ujson_deserialize_ibex_fi_csr_combi_in_t(uj, &uj_data));

  uint32_t read_csrs[IBEXFI_NUM_CSR_COMBI];
  for (int i = 0; i < IBEXFI_NUM_CSR_COMBI; i++) {
    read_csrs[i] = 0x1BADB002;
  }

  // Clear the `sha_en` bit to ensure the message length registers are
  // writeable. Leave the rest of the configuration unchanged.
  uint32_t cfg =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, false);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, cfg);

  // Make explicit register variables for the test
  register volatile uint32_t reg_x9 asm("x9");
  register volatile uint32_t reg_x19 asm("x19");
  register volatile uint32_t reg_x29 asm("x29");

  // Write reference value into CSR.
  if (uj_data.trigger & 0x1) {
    PENTEST_ASM_TRIGGER_HIGH
  }
  abs_mmio_write32(TOP_EARLGREY_AES_BASE_ADDR + AES_IV_0_REG_OFFSET,
                   uj_data.ref_values[0]);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_0_REG_OFFSET,
                   uj_data.ref_values[1]);
  abs_mmio_write32(
      TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_LENGTH_LOWER_REG_OFFSET,
      uj_data.ref_values[2]);
  abs_mmio_write32(
      TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_SEALING_SW_BINDING_7_REG_OFFSET,
      uj_data.ref_values[3]);
  abs_mmio_write32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_SALT_0_REG_OFFSET,
                   uj_data.ref_values[4]);
  abs_mmio_write32(
      TOP_EARLGREY_CSRNG_BASE_ADDR + CSRNG_RESEED_INTERVAL_REG_OFFSET,
      uj_data.ref_values[5]);
  abs_mmio_write32(TOP_EARLGREY_CSRNG_BASE_ADDR + CSRNG_CTRL_REG_OFFSET,
                   uj_data.ref_values[6]);
  abs_mmio_write32(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR +
                       SRAM_CTRL_READBACK_REG_OFFSET,
                   uj_data.ref_values[7]);
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_AES_BASE_ADDR + AES_CTRL_SHADOWED_REG_OFFSET,
      uj_data.ref_values[8]);
  abs_mmio_write32_shadowed(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                                KEYMGR_RESEED_INTERVAL_SHADOWED_REG_OFFSET,
                            uj_data.ref_values[9]);
  abs_mmio_write32(TOP_EARLGREY_EDN0_BASE_ADDR + EDN_CTRL_REG_OFFSET,
                   uj_data.ref_values[10]);
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
          ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET,
      uj_data.ref_values[11]);
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
          ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET,
      uj_data.ref_values[12]);
  abs_mmio_write32_shadowed(
      TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
          ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET,
      uj_data.ref_values[13]);
  reg_x9 = uj_data.ref_values[14];
  reg_x19 = uj_data.ref_values[15];
  reg_x29 = uj_data.ref_values[16];
  if (uj_data.trigger & 0x1) {
    PENTEST_ASM_TRIGGER_LOW
  }

  if (uj_data.trigger & 0x2) {
    PENTEST_ASM_TRIGGER_HIGH
  }
  asm volatile(NOP100);
  if (uj_data.trigger & 0x2) {
    PENTEST_ASM_TRIGGER_LOW
  }

  if (uj_data.trigger & 0x4) {
    PENTEST_ASM_TRIGGER_HIGH
  }
  read_csrs[0] =
      abs_mmio_read32(TOP_EARLGREY_AES_BASE_ADDR + AES_IV_0_REG_OFFSET);
  read_csrs[1] =
      abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_0_REG_OFFSET);
  read_csrs[2] = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR +
                                 HMAC_MSG_LENGTH_LOWER_REG_OFFSET);
  read_csrs[3] = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                                 KEYMGR_SEALING_SW_BINDING_7_REG_OFFSET);
  read_csrs[4] =
      abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR + KEYMGR_SALT_0_REG_OFFSET);

  read_csrs[5] = abs_mmio_read32(TOP_EARLGREY_CSRNG_BASE_ADDR +
                                 CSRNG_RESEED_INTERVAL_REG_OFFSET);
  read_csrs[6] =
      abs_mmio_read32(TOP_EARLGREY_CSRNG_BASE_ADDR + CSRNG_CTRL_REG_OFFSET);
  read_csrs[7] = abs_mmio_read32(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR +
                                 SRAM_CTRL_READBACK_REG_OFFSET);
  read_csrs[8] = abs_mmio_read32(TOP_EARLGREY_AES_BASE_ADDR +
                                 AES_CTRL_SHADOWED_REG_OFFSET);
  read_csrs[9] = abs_mmio_read32(TOP_EARLGREY_KEYMGR_BASE_ADDR +
                                 KEYMGR_RESEED_INTERVAL_SHADOWED_REG_OFFSET);
  read_csrs[10] =
      abs_mmio_read32(TOP_EARLGREY_EDN0_BASE_ADDR + EDN_CTRL_REG_OFFSET);
  read_csrs[11] =
      abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                      ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET);
  read_csrs[12] =
      abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                      ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET);
  read_csrs[13] =
      abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                      ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET);
  read_csrs[14] = reg_x9;
  read_csrs[15] = reg_x19;
  read_csrs[16] = reg_x29;
  if (uj_data.trigger & 0x4) {
    PENTEST_ASM_TRIGGER_LOW
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_csr_combi_out_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.output, 0, sizeof(uj_output.output));

  for (size_t it = 0; it < IBEXFI_NUM_CSR_COMBI; it++) {
    if (read_csrs[it] != uj_data.ref_values[it]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
    }
    uj_output.output[it] = read_csrs[it];
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send alerts back to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_csr_combi_out_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_flash_read(ujson_t *uj) __attribute__((optnone)) {
  // Set the flash region we want to test.
  ibex_fi_flash_region_t uj_data;
  TRY(ujson_deserialize_ibex_fi_flash_region_t(uj, &uj_data));
  if (uj_data.flash_region != flash_region_index) {
    flash_region_index = uj_data.flash_region;
    flash_init = false;
  }

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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

    dif_result_t res_prop = dif_flash_ctrl_set_data_region_properties(
        &flash, flash_region_index, data_region);
    dif_result_t res_en = dif_flash_ctrl_set_data_region_enablement(
        &flash, flash_region_index, kDifToggleEnabled);
    if (res_prop == kDifLocked || res_en == kDifLocked) {
      LOG_INFO("Flash region locked, aborting!");
      ibex_fi_empty_t uj_output;
      uj_output.success = false;
      RESP_OK(ujson_serialize_ibex_fi_empty_t, uj, &uj_output);
      return OK_STATUS();
    }

    flash_init = true;
    flash_test_page_addr = data_region.base * FLASH_PAGE_SZ;
  }

  mmio_region_t flash_test_page = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_test_page_addr);

  if (!flash_data_valid) {
    // Prepare page and write reference values into it.
    uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
    memset(input_page, 0x0, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
    for (int i = 0; i < kNumRefValues; i++) {
      input_page[i] = ref_values[i];
    }

    // Erase flash and write page with reference values.
    TRY(flash_ctrl_testutils_erase_and_write_page(
        &flash, flash_test_page_addr, /*partition_id=*/0, input_page,
        kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));

    flash_data_valid = true;
  }

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile("lw x5, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x6, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x7, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x12, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x13, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x14, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x15, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x16, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x17, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x28, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x29, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x30, (%0)" : : "r"((flash_test_page.base)));
  asm volatile("lw x31, (%0)" : : "r"((flash_test_page.base)));
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Check if one or multiple registers values are faulty.
  size_t compare_regs[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {
      kRegX5,  kRegX6,  kRegX7,  kRegX12, kRegX13, kRegX14, kRegX15,
      kRegX16, kRegX17, kRegX28, kRegX29, kRegX30, kRegX31};
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[0]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
      // Re-init flash with valid data.
      flash_data_valid = false;
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_flash_read_static(ujson_t *uj)
    __attribute__((optnone)) {
  // Set the flash region we want to test.
  ibex_fi_flash_set_region_t uj_data;
  TRY(ujson_deserialize_ibex_fi_flash_set_region_t(uj, &uj_data));

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Configure the data flash.
  // Flash configuration with ECC and scramble disabled
  dif_flash_ctrl_region_properties_t region_properties = {
      .rd_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .erase_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False,
      .ecc_en = kMultiBitBool4False,
      .high_endurance_en = kMultiBitBool4False};

  dif_flash_ctrl_data_region_properties_t data_region = {
      .base = FLASH_PAGES_PER_BANK,
      .size = 0x1,
      .properties = region_properties};

  dif_result_t res_prop = dif_flash_ctrl_set_data_region_properties(
      &flash, uj_data.flash_region, data_region);
  if (res_prop == kDifLocked) {
    LOG_INFO("Flash region locked, aborting!");
    ibex_fi_empty_t uj_output;
    uj_output.success = false;
    RESP_OK(ujson_serialize_ibex_fi_empty_t, uj, &uj_output);
    return OK_STATUS();
  }

  uint32_t flash_addr = data_region.base * FLASH_PAGE_SZ;
  mmio_region_t flash_test_page = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_addr);

  if (uj_data.init) {
    dif_result_t res_en = dif_flash_ctrl_set_data_region_enablement(
        &flash, uj_data.flash_region, kDifToggleEnabled);
    if (res_en == kDifLocked) {
      LOG_INFO("Flash region locked, aborting!");
      ibex_fi_empty_t uj_output;
      uj_output.success = false;
      RESP_OK(ujson_serialize_ibex_fi_empty_t, uj, &uj_output);
      return OK_STATUS();
    }

    // Prepare page and write reference values into it.
    uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
    memset(input_page, 0x0, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
    for (int i = 0; i < kNumRefValues; i++) {
      input_page[i] = ref_values[i];
    }

    // Erase flash and write page with reference values.
    TRY(flash_ctrl_testutils_erase_and_write_page(
        &flash, flash_addr, /*partition_id=*/0, input_page,
        kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  }

  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(NOP1000);
  PENTEST_ASM_TRIGGER_LOW

  uint32_t flash_reads[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {0};

  for (int idx = 0; idx < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; idx++) {
    flash_reads[idx] =
        mmio_region_read32(flash_test_page, idx * (ptrdiff_t)sizeof(uint32_t));
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_pure_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));

  // Check if one or multiple values are faulty.
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (flash_reads[it] != ref_values[it]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = flash_reads[it];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_pure_data_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_ibex_fi_char_flash_write(ujson_t *uj) __attribute__((optnone)) {
  // Set the flash region we want to test.
  ibex_fi_flash_region_t uj_data;
  TRY(ujson_deserialize_ibex_fi_flash_region_t(uj, &uj_data));
  if (uj_data.flash_region != flash_region_index) {
    flash_region_index = uj_data.flash_region;
    flash_init = false;
  }

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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

    dif_result_t res_prop = dif_flash_ctrl_set_data_region_properties(
        &flash, flash_region_index, data_region);
    dif_result_t res_en = dif_flash_ctrl_set_data_region_enablement(
        &flash, flash_region_index, kDifToggleEnabled);
    if (res_prop == kDifLocked || res_en == kDifLocked) {
      ibex_fi_empty_t uj_output;
      uj_output.success = false;
      RESP_OK(ujson_serialize_ibex_fi_empty_t, uj, &uj_output);
      return OK_STATUS();
    }

    flash_init = true;
    flash_test_page_addr = data_region.base * FLASH_PAGE_SZ;
  }

  mmio_region_t flash_test_page = mmio_region_from_addr(
      TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + (uintptr_t)flash_test_page_addr);

  // Prepare page and write reference values into it.
  uint32_t input_page[FLASH_UINT32_WORDS_PER_PAGE];
  memset(input_page, 0x0, FLASH_UINT32_WORDS_PER_PAGE * sizeof(uint32_t));
  for (int i = 0; i < kNumRefValues; i++) {
    input_page[i] = ref_values[i];
  }

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  // Erase flash and write page with reference values.
  TRY(flash_ctrl_testutils_erase_and_write_page(
      &flash, flash_test_page_addr, /*partition_id=*/0, input_page,
      kDifFlashCtrlPartitionTypeData, FLASH_UINT32_WORDS_PER_PAGE));
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read back and compare against reference values.
  uint32_t res_values[kNumRefValues];
  uint32_t res = 0;
  for (int i = 0; i < kNumRefValues; i++) {
    res_values[i] =
        mmio_region_read32(flash_test_page, i * (ptrdiff_t)sizeof(uint32_t));
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
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_complement_branch(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  PENTEST_ASM_TRIGGER_HIGH
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile(
    "beq" " %0, %1, .L_HARDENED_%=;" \
    ".UNIMP_%=: unimp;" \
    "bne" " %0, %1, .UNIMP_%=;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2)
  );
  // clang-format on
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_unimp(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  PENTEST_ASM_TRIGGER_HIGH
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_2_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  PENTEST_ASM_TRIGGER_HIGH
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_3_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  PENTEST_ASM_TRIGGER_HIGH
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_4_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  PENTEST_ASM_TRIGGER_HIGH
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp; unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_hardened_check_eq_5_unimps(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Values are intentially not equal.
  hardened_bool_t value1 = HARDENED_BOOL_TRUE;
  hardened_bool_t value2 = HARDENED_BOOL_FALSE;

  PENTEST_ASM_TRIGGER_HIGH
  // The HARDENED_CHECK macro from hardened.h is solved explicitely.
  // clang-format off
  asm volatile("beq" " %0, %1, .L_HARDENED_%=;" \
    "unimp; unimp; unimp; unimp; unimp;" \
    ".L_HARDENED_%=:;"::"r"(value1), "r"(value2) );
  // clang-format on
  PENTEST_ASM_TRIGGER_LOW

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_mult_t uj_output;
  uj_output.err_status = codes;
  uj_output.result1 = value1;
  uj_output.result2 = value2;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_mult_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_mem_op_loop(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Init the loop counters.
  uint32_t loop_counter1 = 0;
  uint32_t loop_counter2 = 10000;

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  for (int loop_cnt = 0; loop_cnt < 10000; loop_cnt++) {
    asm volatile(LWADDISW1 : : "r"((uint32_t *)&loop_counter1));
    asm volatile(LWSUBISW1 : : "r"((uint32_t *)&loop_counter2));
  }
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, loop counter, alerts & ERR_STATUS to host.
  ibex_fi_test_result_array_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send back loop counters.
  memset(uj_output.result, 0, sizeof(uj_output.result));
  uj_output.result[0] = loop_counter1;
  uj_output.result[1] = loop_counter2;

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_array_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_register_file(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(NOP1000);
  PENTEST_ASM_TRIGGER_LOW;

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Check if one or multiple registers values are faulty.
  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Compare against reference values.
  size_t compare_regs[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {
      kRegX5,  kRegX6,  kRegX7,  kRegX12, kRegX13, kRegX14, kRegX15,
      kRegX16, kRegX17, kRegX28, kRegX29, kRegX30, kRegX31};
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[compare_regs[it]]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Return register file dump back to host.
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_register_file_read(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x12, x12, x12");
  asm volatile("or x13, x13, x13");
  asm volatile("or x14, x14, x14");
  asm volatile("or x15, x15, x15");
  asm volatile("or x16, x16, x16");
  asm volatile("or x17, x17, x17");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x31, x31, x31");

  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x12, x12, x12");
  asm volatile("or x13, x13, x13");
  asm volatile("or x14, x14, x14");
  asm volatile("or x15, x15, x15");
  asm volatile("or x16, x16, x16");
  asm volatile("or x17, x17, x17");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x31, x31, x31");

  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x12, x12, x12");
  asm volatile("or x13, x13, x13");
  asm volatile("or x14, x14, x14");
  asm volatile("or x15, x15, x15");
  asm volatile("or x16, x16, x16");
  asm volatile("or x17, x17, x17");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x31, x31, x31");

  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x12, x12, x12");
  asm volatile("or x13, x13, x13");
  asm volatile("or x14, x14, x14");
  asm volatile("or x15, x15, x15");
  asm volatile("or x16, x16, x16");
  asm volatile("or x17, x17, x17");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x31, x31, x31");

  asm volatile("or x5, x5, x5");
  asm volatile("or x6, x6, x6");
  asm volatile("or x7, x7, x7");
  asm volatile("or x12, x12, x12");
  asm volatile("or x13, x13, x13");
  asm volatile("or x14, x14, x14");
  asm volatile("or x15, x15, x15");
  asm volatile("or x16, x16, x16");
  asm volatile("or x17, x17, x17");
  asm volatile("or x28, x28, x28");
  asm volatile("or x29, x29, x29");
  asm volatile("or x30, x30, x30");
  asm volatile("or x31, x31, x31");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Check if one or multiple registers values are faulty.
  size_t compare_regs[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {
      kRegX5,  kRegX6,  kRegX7,  kRegX12, kRegX13, kRegX14, kRegX15,
      kRegX16, kRegX17, kRegX28, kRegX29, kRegX30, kRegX31};
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[compare_regs[it]]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_reg_op_loop(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Init x5=0 and x6=10000.
  asm volatile(INITX5);
  asm volatile(INITX6);

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  for (int loop_cnt = 0; loop_cnt < 10000; loop_cnt++) {
    asm volatile(ADDI1);
    asm volatile(SUBI1);
  }
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_faulty_data_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Check if loop counters match expected values.
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.data_faulty, 0, sizeof(uj_output.data_faulty));
  // x5 should be 10000.
  if (registers_dumped[kRegX5] != 10000) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }
  // x6 should be 0.
  if (registers_dumped[kRegX6] != 0) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_single_beq(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Init x5 and x6.
  asm volatile("li x5, 0x1a\n");
  asm volatile("li x6, 0x1a\n");

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(NOP10 "beq x5, x6, correctbeq\n" NOP10
                     "j badbeq\n"
                     "correctbeq:\n"
                     "addi x5, x5, 0x11\n"
                     "addi x6, x6, 0x22\n"
                     "badbeq:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  // If there is a mismatch, set data_faulty to true and return the
  // faulty value.
  if (registers_dumped[kRegX5] != (0x11 + 0x1a)) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }

  if (registers_dumped[kRegX6] != (0x22 + 0x1a)) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_single_bne(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Init x5 and x6.
  asm volatile("li x5, 0x1a\n");
  asm volatile("li x6, 0x0a\n");

  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(NOP10 "bne x5, x6, correctbne\n" NOP10
                     "j badbne\n"
                     "correctbne:\n"
                     "addi x5, x5, 0x11\n"
                     "addi x6, x6, 0x22\n"
                     "badbne:\n");
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  // If there is a mismatch, set data_faulty to true and return the
  // faulty value.
  if (registers_dumped[kRegX5] != (0x11 + 0x1a)) {
    uj_output.data_faulty[0] = true;
    uj_output.data[0] = registers_dumped[kRegX5];
  }

  if (registers_dumped[kRegX6] != (0x22 + 0x0a)) {
    uj_output.data_faulty[1] = true;
    uj_output.data[1] = registers_dumped[kRegX6];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_read(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  int sram_buffer_size = sizeof(sram_main_buffer) / 4;
  int sram_half_size = sram_buffer_size / 2;

  // Init the SRAM with counter values.
  for (size_t i = 0; i < sram_buffer_size; i++) {
    sram_main_buffer[i] = i;
  }

  // Init the SRAM position we are reading from with ref_values[0].
  sram_main_buffer[sram_half_size] = ref_values[0];

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  // Read from SRAM into temporary registers.
  asm volatile("lw x5, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x6, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x7, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x12, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x13, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x14, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x15, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x16, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x17, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x28, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x29, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x30, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  asm volatile("lw x31, (%0)" : : "r"(&sram_main_buffer[sram_half_size]));
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Check if one or multiple registers values are faulty.
  size_t compare_regs[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {
      kRegX5,  kRegX6,  kRegX7,  kRegX12, kRegX13, kRegX14, kRegX15,
      kRegX16, kRegX17, kRegX28, kRegX29, kRegX30, kRegX31};
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[0]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_read_ret(ujson_t *uj)
    __attribute__((optnone)) {
  if (!sram_ret_init) {
    // Init retention SRAM, wipe and scramble it.
    mmio_region_t addr =
        mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
    TRY(dif_sram_ctrl_init(addr, &ret_sram));
    TRY(sram_ctrl_testutils_wipe(&ret_sram));
    TRY(sram_ctrl_testutils_scramble(&ret_sram));
    sram_ret_init = true;
  }

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  uint32_t *ret_ram = (uint32_t *)TOP_EARLGREY_RAM_RET_AON_BASE_ADDR;
  size_t ret_ram_len = TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES / sizeof(ret_ram[0]);
  size_t ret_ram_half_len = ret_ram_len / 2;

  // Write counter value into ret SRAM.
  for (size_t i = 0; i < ret_ram_len; i++) {
    ret_ram[i] = i;
  }

  // Init the SRAM position we are reading from with ref_values[0].
  ret_ram[ret_ram_half_len] = ref_values[0];

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  // Read from ret. SRAM into temporary registers.
  asm volatile("lw x5, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x6, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x7, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x12, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x13, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x14, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x15, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x16, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x17, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x28, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x29, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x30, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  asm volatile("lw x31, (%0)" : : "r"(&ret_ram[ret_ram_half_len]));
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_data_sram_codes_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Check if one or multiple registers values are faulty.
  size_t compare_regs[IBEXFI_MAX_FAULTY_ADDRESSES_DATA] = {
      kRegX5,  kRegX6,  kRegX7,  kRegX12, kRegX13, kRegX14, kRegX15,
      kRegX16, kRegX17, kRegX28, kRegX29, kRegX30, kRegX31};
  for (size_t it = 0; it < IBEXFI_MAX_FAULTY_ADDRESSES_DATA; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[0]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
    }
  }

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Read the ret. SRAM errors from the status register.
  dif_sram_ctrl_status_bitfield_t ret_sram_codes;
  TRY(dif_sram_ctrl_get_status(&ret_sram, &ret_sram_codes));

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  uj_output.sram_err_status = ret_sram_codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_sram_codes_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_static(ujson_t *uj) __attribute__((optnone)) {
  if (!sram_ret_init) {
    // Init retention SRAM, wipe and scramble it.
    mmio_region_t addr =
        mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR);
    TRY(dif_sram_ctrl_init(addr, &ret_sram));
    TRY(sram_ctrl_testutils_wipe(&ret_sram));
    TRY(sram_ctrl_testutils_scramble(&ret_sram));
    sram_ret_init = true;
  }

  int max_words = sizeof(retention_sram_owner_t) / sizeof(uint32_t);

  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile(NOP1000);
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  ibex_fi_faulty_addresses_data_t uj_output;
  // Send back register file dump.
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Compare against reference values.
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
      // Currently, we register only up to IBEXFI_MAX_FAULTY_ADDRESSES_DATA
      // faulty SRAM positions. If there are more, we overwrite the addresses
      // array.
      if (faulty_address_pos >= IBEXFI_MAX_FAULTY_ADDRESSES_DATA) {
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
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_addresses_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Initialize SRAM region with inverse ref_values[0] to avoid that data from a
  // previous run is still in memory.
  for (int i = 0; i < IBEXFI_SRAM_WORDS; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ~ref_values[0]);
  }

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  for (int i = 0; i < IBEXFI_SRAM_WORDS; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ref_values[i % 32]);
  }
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, memory dump, alerts & ERR_STATUS to host.
  ibex_fi_test_result_sram_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Return memory back to host.
  for (int it = 0; it < IBEXFI_SRAM_WORDS; it++) {
    uj_output.memory[it] = mmio_region_read32(sram_region_main_addr,
                                              it * (ptrdiff_t)sizeof(uint32_t));
  }

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_sram_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write_read(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_faulty_data_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.data_faulty, false, sizeof(uj_output.data_faulty));
  memset(uj_output.data, 0, sizeof(uj_output.data));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Check if one or multiple registers values are faulty.
  size_t compare_regs[3] = {kRegX5, kRegX6, kRegX7};
  for (size_t it = 0; it < 3; it++) {
    if (registers_dumped[compare_regs[it]] != ref_values[compare_regs[it]]) {
      // If there is a mismatch, set data_faulty to true and return the
      // faulty value.
      uj_output.data_faulty[it] = true;
      uj_output.data[it] = registers_dumped[compare_regs[it]];
    }
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_faulty_data_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write_read_alt(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the SRAM with a counter
  for (size_t i = 0; i < kSramWriteReadAltNumValues; i++) {
    sram_main_buffer[i] = i;
  }

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[0]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[1]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[1]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[2]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[2]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[3]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[3]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[4]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[4]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[5]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[5]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[6]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[6]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[7]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[7]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[8]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[8]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[9]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[9]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[10]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[10]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[11]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[11]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[12]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[12]));
  asm volatile("sw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[13]));
  asm volatile("lw x6, (%0)" : : "r"((uint32_t *)&sram_main_buffer[13]));
  asm volatile("sw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[14]));
  asm volatile("lw x7, (%0)" : : "r"((uint32_t *)&sram_main_buffer[14]));
  asm volatile("sw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[15]));
  asm volatile("lw x5, (%0)" : : "r"((uint32_t *)&sram_main_buffer[15]));
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Load the values stored in the sram buffer.
  uint32_t sram_values[kSramWriteReadAltNumValues] = {0};
  for (size_t i = 0; i < kSramWriteReadAltNumValues; i++) {
    sram_values[i] = sram_main_buffer[i];
  }

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  ibex_fi_test_result_sram_t uj_output;
  // Preset buffers to 0.
  memset(uj_output.memory, 0, sizeof(uj_output.memory));
  memset(uj_output.registers, 0, sizeof(uj_output.registers));

  // Return the 16 values from SRAM.
  for (size_t it = 0; it < kSramWriteReadAltNumValues; it++) {
    uj_output.memory[it] = sram_values[it];
  }

  // Return register file dump back to host.
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Send result & ERR_STATUS to host.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_sram_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_sram_write_static_unrolled(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Get address of buffer located in SRAM.
  uintptr_t sram_main_buffer_addr = (uintptr_t)&sram_main_buffer;
  mmio_region_t sram_region_main_addr =
      mmio_region_from_addr(sram_main_buffer_addr);

  // Initialize SRAM region with inverse ref_values to avoid that data from a
  // previous run is still in memory.
  for (int i = 0; i < IBEXFI_SRAM_WORDS; i++) {
    mmio_region_write32(sram_region_main_addr, i * (ptrdiff_t)sizeof(uint32_t),
                        ~ref_values[0]);
  }

  // Initialize the register file before the FI trigger window.
  INIT_TMP_REGISTER_FILE

  // FI code target.
  // Unrolled for easier fault injection characterization.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_TMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, memory dump, alerts & ERR_STATUS to host.
  ibex_fi_test_result_sram_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Return memory back to host.
  for (int it = 0; it < IBEXFI_SRAM_WORDS; it++) {
    uj_output.memory[it] = mmio_region_read32(sram_region_main_addr,
                                              it * (ptrdiff_t)sizeof(uint32_t));
  }

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_sram_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_unconditional_branch(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the register that is used in the FI trigger window (x5) to 0.
  asm volatile(INITX5);

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Incremented counter is stored in register x5.
  uj_output.result = registers_dumped[kRegX5];

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_unconditional_branch_nop(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the register that is used in the FI trigger window (x5) to 0.
  asm volatile(INITX5);

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Incremented counter is stored in register x5.
  uj_output.result = registers_dumped[kRegX5];

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_unrolled_mem_op_loop(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // FI code target.
  uint32_t loop_counter = 0;
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, loop counter, alerts & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  uj_output.result = loop_counter;

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_unrolled_reg_op_loop(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the register that is used in the FI trigger window (x5) to 0.
  asm volatile(INITX5);

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Loop counter is stored in register x5.
  uj_output.result = registers_dumped[kRegX5];

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_char_unrolled_reg_op_loop_chain(ujson_t *uj)
    __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

  // Initialize the register file before the FI trigger window.
  INIT_REGISTER_FILE

  // Set the registers that are used in the FI trigger window (x5, x6, x7, x28,
  // x29, and x30) to 0.
  asm volatile(INIT_TMPREGS);

  // FI code target.
  PENTEST_ASM_TRIGGER_HIGH
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
  PENTEST_ASM_TRIGGER_LOW

  // Dump the register file after the FI trigger window.
  DUMP_REGISTER_FILE

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send register file dump, alerts & ERR_STATUS to host.
  ibex_fi_test_result_array_t uj_output;
  memset(uj_output.registers, 0, sizeof(uj_output.registers));
  memcpy(uj_output.registers, registers_dumped, sizeof(registers_dumped));
  // Return registers used in the FI trigger window back to the host.
  memset(uj_output.result, 0, sizeof(uj_output.result));
  uj_output.result[0] = registers_dumped[kRegX5];
  uj_output.result[1] = registers_dumped[kRegX6];
  uj_output.result[2] = registers_dumped[kRegX7];
  uj_output.result[3] = registers_dumped[kRegX28];
  uj_output.result[4] = registers_dumped[kRegX29];
  uj_output.result[5] = registers_dumped[kRegX30];

  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_array_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

  return OK_STATUS();
}

status_t handle_ibex_fi_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));
  penetrationtest_alert_config_t uj_alert_data;
  TRY(ujson_deserialize_penetrationtest_alert_config_t(uj, &uj_alert_data));

  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // As we are using the software defined trigger, the first argument of
  // pentest_init is not needed. kPentestTriggerSourceAes is selected as a
  // placeholder.
  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralEdn |
                   kPentestPeripheralCsrng | kPentestPeripheralEntropy |
                   kPentestPeripheralAes | kPentestPeripheralHmac |
                   kPentestPeripheralKmac | kPentestPeripheralOtbn,
               uj_sensor_data.sensor_ctrl_enable,
               uj_sensor_data.sensor_ctrl_en_fatal);

  // Configure the alert handler. Alerts triggered by IP blocks are captured
  // and reported to the test.
  pentest_configure_alert_handler(
      uj_alert_data.alert_classes, uj_alert_data.enable_alerts,
      uj_alert_data.enable_loc_alerts, uj_alert_data.enable_classes,
      uj_alert_data.accumulation_thresholds, uj_alert_data.signals,
      uj_alert_data.duration_cycles, uj_alert_data.ping_timeout);

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_cpuctrl_data.enable_icache, &uj_output.icache_en,
      uj_cpuctrl_data.enable_dummy_instr, &uj_output.dummy_instr_en,
      uj_cpuctrl_data.dummy_instr_count, uj_cpuctrl_data.enable_jittery_clock,
      uj_cpuctrl_data.enable_sram_readback, &uj_output.clock_jitter_locked,
      &uj_output.clock_jitter_en, &uj_output.sram_main_readback_locked,
      &uj_output.sram_ret_readback_locked, &uj_output.sram_main_readback_en,
      &uj_output.sram_ret_readback_en, uj_cpuctrl_data.enable_data_ind_timing,
      &uj_output.data_ind_timing_en));

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

  // Read rom digest.
  TRY(pentest_read_rom_digest(uj_output.rom_digest));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  // Read the sensor config.
  TRY(pentest_send_sensor_config(uj));

  // Read the alert config.
  TRY(pentest_send_alert_config(uj));

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  // Initialize flash for the flash test and write reference values into page.
  flash_init = false;
  flash_data_valid = false;
  // Initialize retention SRAM.
  sram_ret_init = false;
  // Fetch reference values from OTP before OTP tests.
  otp_ref_init = false;

  return OK_STATUS();
}

status_t handle_ibex_fi_otp_data_read(ujson_t *uj) __attribute__((optnone)) {
  TRY(init_ref_otp_data());
  TRY(read_otp_partitions(uj));
  return OK_STATUS();
}

status_t handle_ibex_fi_otp_read_lock(ujson_t *uj) __attribute__((optnone)) {
  TRY(init_ref_otp_data());
  TRY(dif_otp_ctrl_lock_reading(&otp, kDifOtpCtrlPartitionVendorTest));
  TRY(dif_otp_ctrl_lock_reading(&otp, kDifOtpCtrlPartitionCreatorSwCfg));
  TRY(dif_otp_ctrl_lock_reading(&otp, kDifOtpCtrlPartitionOwnerSwCfg));

  TRY(read_otp_partitions(uj));

  return OK_STATUS();
}

status_t handle_ibex_fi_otp_write_lock(ujson_t *uj) __attribute__((optnone)) {
  // Clear registered alerts in alert handler.
  pentest_registered_alerts_t reg_alerts = pentest_get_triggered_alerts();
  // Clear registered local alerts in alert handler.
  pentest_registered_loc_alerts_t reg_loc_alerts =
      pentest_get_triggered_loc_alerts();
  // Clear the AST recoverable alerts.
  pentest_clear_sensor_recov_alerts();

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

  // Get registered alerts from alert handler.
  reg_alerts = pentest_get_triggered_alerts();
  // Get registered local alerts from alert handler.
  reg_loc_alerts = pentest_get_triggered_loc_alerts();
  // Get fatal and recoverable AST alerts from sensor controller.
  pentest_sensor_alerts_t sensor_alerts = pentest_get_sensor_alerts();

  // Read ERR_STATUS register.
  dif_rv_core_ibex_error_status_t codes;
  TRY(dif_rv_core_ibex_get_error_status(&rv_core_ibex, &codes));

  // Send res & ERR_STATUS to host.
  ibex_fi_test_result_t uj_output;
  uj_output.result =
      0;  // Writing to the locked OTP partition crashes the chip.
  uj_output.err_status = codes;
  memcpy(uj_output.alerts, reg_alerts.alerts, sizeof(reg_alerts.alerts));
  uj_output.loc_alerts = reg_loc_alerts.loc_alerts;
  memcpy(uj_output.ast_alerts, sensor_alerts.alerts,
         sizeof(sensor_alerts.alerts));
  RESP_OK(ujson_serialize_ibex_fi_test_result_t, uj, &uj_output);

  // Signal to Verilator that the test completed.
  pentest_verilator_signal_test_end();

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
    case kIbexFiSubcommandCharAddiSingleBeq:
      return handle_ibex_fi_char_addi_single_beq(uj);
    case kIbexFiSubcommandCharAddiSingleBeqCm:
      return handle_ibex_fi_char_addi_single_beq_cm(uj);
    case kIbexFiSubcommandCharAddiSingleBeqCm2:
      return handle_ibex_fi_char_addi_single_beq_cm2(uj);
    case kIbexFiSubcommandCharAddiSingleBeqNeg:
      return handle_ibex_fi_char_addi_single_beq_neg(uj);
    case kIbexFiSubcommandCharAddiSingleBne:
      return handle_ibex_fi_char_addi_single_bne(uj);
    case kIbexFiSubcommandCharAddiSingleBneNeg:
      return handle_ibex_fi_char_addi_single_bne_neg(uj);
    case kIbexFiSubcommandCharCombi:
      return handle_ibex_fi_char_combi(uj);
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
    case kIbexFiSubcommandCharCsrCombi:
      return handle_ibex_fi_char_csr_combi(uj);
    case kIbexFiSubcommandCharFlashRead:
      return handle_ibex_fi_char_flash_read(uj);
    case kIbexFiSubcommandCharFlashReadStatic:
      return handle_ibex_fi_char_flash_read_static(uj);
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
    case kIbexFiSubcommandCharSingleBeq:
      return handle_ibex_fi_char_single_beq(uj);
    case kIbexFiSubcommandCharSingleBne:
      return handle_ibex_fi_char_single_bne(uj);
    case kIbexFiSubcommandCharSramRead:
      return handle_ibex_fi_char_sram_read(uj);
    case kIbexFiSubcommandCharSramReadRet:
      return handle_ibex_fi_char_sram_read_ret(uj);
    case kIbexFiSubcommandCharSramStatic:
      return handle_ibex_fi_char_sram_static(uj);
    case kIbexFiSubcommandCharSramWrite:
      return handle_ibex_fi_char_sram_write(uj);
    case kIbexFiSubcommandCharSramWriteRead:
      return handle_ibex_fi_char_sram_write_read(uj);
    case kIbexFiSubcommandCharSramWriteReadAlt:
      return handle_ibex_fi_char_sram_write_read_alt(uj);
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
    default:
      LOG_ERROR("Unrecognized IBEX FI subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
