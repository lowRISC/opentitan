// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Note that since rma process takes more than 100ms in dvsim,
// the test runs 1.6h (110ms in simtime).

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print_uart.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top/otp_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_pinmux_t pinmux;
static dif_uart_t uart0;
static dif_lc_ctrl_t lc;

// This is updated by the sv component of the test
static volatile const uint8_t kTestPhase = 0;
static volatile const uint8_t kSrcLcState = 0;

// Closed source short rma support: under `+en_small_rma=1` the vseq's
// `enable_small_rma()` forces the RMA data-partition wipe's `end_page` down
// to 2.
static volatile const uint8_t kShortRma = 0;

enum {
  kDataSize = 16,
};

enum {
  kTestPhaseWriteData = 0,
  kTestPhaseEnterRMA = 1,
  kTestPhaseCheckWipe = 2,
};

// Page indices covering the start, middle, and end of the flat NVM data
// partition. This stands in for flash's old "check both banks" coverage --
// RRAM's data partition has no bank concept, just one address range -- by
// spreading the same handful of checks across the full range instead.
//
// The literal last page of the whole partition falls inside RRAM's reserved
// per-slot tail (part of it is even read/write protected in hardware -- see
// `kRramCtrlOtpPageCount` in rram_ctrl.h) -- writing there hangs rather than
// erroring. Use the last page of slot B that's still inside its *usable*
// range instead (`NVM_SLOT_B_END_BYTES` is nvm_ctrl.h's own exclusive upper
// bound of that range). For flash (no reserved tail), this is the same as
// the literal last page, so no separate branch is needed.
enum {
  kDataPageCount = NVM_DATA_SIZE_BYTES / NVM_BYTES_PER_PAGE,
  kDataPageStart = 0,
  kDataPageMiddle = kDataPageCount / 2,
  kDataPageEnd = (NVM_SLOT_B_END_BYTES / NVM_BYTES_PER_PAGE) - 1,
};

// Data region indices used to configure the three data-partition pages
// above; arbitrary but must be distinct.
enum {
  kDataRegionStart = 0,
  kDataRegionMiddle = 1,
  kDataRegionEnd = 2,
};

// Under short RMA, only global pages 0-2 of the data partition are guaranteed
// wiped. Move the middle/end checks next to the base so they stay within that
// range instead of deep in slot B.
static uint32_t data_page_middle(void) {
  return kShortRma ? 1 : kDataPageMiddle;
}

static uint32_t data_page_end(void) { return kShortRma ? 2 : kDataPageEnd; }

static const uint32_t kRandomData[6][kDataSize] = {
    {0x27af716e, 0xdd493905, 0x4d674f07, 0x1e876023, 0x555477e5, 0x8c079501,
     0xfa0aed05, 0x1091a5e4, 0xe94119be, 0xe0bed120, 0xb4611217, 0x1fa02d2a,
     0x5252583f, 0xc2a5083b, 0xc43409c3, 0xdb348c5c},
    {0x55c88b8c, 0x5cb3c5eb, 0xc942d714, 0x7df99821, 0x151101b2, 0x739749a1,
     0x82bab3ef, 0xeb96c062, 0x99ac3750, 0xb31bb5e2, 0x83f979fb, 0x2e89575f,
     0x0ff9081f, 0x81d627e9, 0x8d0bdbfb, 0x69349b84},
    {0xabd3622b, 0xd5d03fbb, 0x7c3bf1df, 0x697b82fb, 0xa96e5282, 0xf6dda27e,
     0x9bb834db, 0x207e2f9f, 0xe7249768, 0x24e91f04, 0x0c86716b, 0x38f956fe,
     0x246ac305, 0xee607b20, 0xb20bb6ef, 0xe95c3687},
    {0xaf2afb37, 0x646de1b1, 0x092b67d9, 0x1aaaebc3, 0x0dab6bd2, 0x47c83a55,
     0xbdd1009f, 0xcd9f4c7a, 0xabe6e3a3, 0xb56e9d22, 0xacb955ce, 0x2d05fe1b,
     0x7e748f0c, 0xc7f4a59d, 0x7cac8713, 0x568ba3c9},
    {0x95f9fe5a, 0xb5173233, 0x7055dc6e, 0x9ffdbec7, 0x98d5a883, 0xe81e5751,
     0x62bbd34e, 0x4bd22ca9, 0x58aac56e, 0xf9d87d26, 0xb2e7eba5, 0x6bcb1c4e,
     0xec7421c7, 0x8c49708a, 0xbf7932b2, 0x353b6a75},
    {0xf8ff57b9, 0x444ff4a9, 0xf3574d3c, 0xf6682a84, 0x67455a38, 0x9c138df2,
     0x4054e3e5, 0xde4b1a26, 0x047cc121, 0x42cbd0ae, 0x3eec418f, 0x454323c4,
     0xf21bee28, 0x28dd24b7, 0x29dd06a6, 0xf83e419f},
};

static void write_info_page_scrambled(nvm_info_page_t page,
                                      const uint32_t *data) {
  CHECK_STATUS_OK(
      nvm_testutils_info_page_setup(page, kPageReadWrite, kPageScrambleCfg));
  CHECK_STATUS_OK(nvm_testutils_write_info_page(page, /*byte_offset=*/0, data,
                                                kDataSize,
                                                /*erase_before_write=*/true,
                                                /*readback=*/false));
}

static void write_data_page_scrambled(uint32_t region, uint32_t page_index,
                                      const uint32_t *data) {
  CHECK_STATUS_OK(nvm_testutils_data_region_setup(
      region, page_index, /*size=*/1, kPageReadWrite, kPageScrambleCfg));
  CHECK_STATUS_OK(nvm_testutils_data_write(page_index * NVM_BYTES_PER_PAGE,
                                           data, kDataSize,
                                           /*erase_before_write=*/true));
}

static void read_and_check_info_page_scrambled(bool is_equal,
                                               nvm_info_page_t page,
                                               const uint32_t *data) {
  uint32_t readback_data[kDataSize];
  CHECK_STATUS_OK(
      nvm_testutils_info_page_setup(page, kPageReadWrite, kPageScrambleCfg));
  CHECK_STATUS_OK(nvm_testutils_read_info_page(page, /*byte_offset=*/0,
                                               readback_data, kDataSize));
  if (is_equal) {
    CHECK_ARRAYS_EQ(readback_data, data, kDataSize);
  } else {
    CHECK_ARRAYS_NE(readback_data, data, kDataSize);
  }
}

static void read_and_check_data_page_scrambled(bool is_equal, uint32_t region,
                                               uint32_t page_index,
                                               const uint32_t *data) {
  uint32_t readback_data[kDataSize];
  CHECK_STATUS_OK(nvm_testutils_data_region_setup(
      region, page_index, /*size=*/1, kPageReadWrite, kPageScrambleCfg));
  mmio_region_t data_region = mmio_region_from_addr(NVM_DATA_BASE_ADDR);
  for (size_t i = 0; i < kDataSize; ++i) {
    readback_data[i] = mmio_region_read32(
        data_region,
        (ptrdiff_t)(page_index * NVM_BYTES_PER_PAGE + i * sizeof(uint32_t)));
  }
  if (is_equal) {
    CHECK_ARRAYS_EQ(readback_data, data, kDataSize);
  } else {
    CHECK_ARRAYS_NE(readback_data, data, kDataSize);
  }
}

// Function for the first boot, the NVM is written to with known data.
// All partitions can be written to when the LC_STATE is Dev and
// the OTP secret 2 partition has not been provisioned.
static void write_data_test_phase(void) {
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));
  CHECK(curr_state == kSrcLcState);

  write_info_page_scrambled(kNvmInfoPageCreatorSecret, kRandomData[0]);
  write_info_page_scrambled(kNvmInfoPageOwnerSecret, kRandomData[1]);
  write_info_page_scrambled(kNvmInfoPageWaferAuthSecret, kRandomData[2]);
  write_data_page_scrambled(kDataRegionStart, kDataPageStart, kRandomData[3]);
  write_data_page_scrambled(kDataRegionMiddle, data_page_middle(),
                            kRandomData[4]);
  write_data_page_scrambled(kDataRegionEnd, data_page_end(), kRandomData[5]);

  LOG_INFO("Write data test complete - waiting for TB");
  // Going into WFI which will be detected by the testbench
  // and an OTP write and reset can be triggered.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

// Function for the second boot, the LC_STATE is still Dev but the OTP secret 2
// partition has now been provisioned by the testbench. Reading back
// from the NVM pages that are still accessible as a smoke check.
// Creator Secret is not accessible because of OTP secret 2 provisioning.
// Isolation Partition cannot be read in LC_STATE of Dev.
// All others are accessible.
// Once readback is complete we wait for the testbench to issue a
// transition into RMA.
static void enter_rma_test_phase(void) {
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));
  CHECK(curr_state == kSrcLcState);

  read_and_check_info_page_scrambled(true, kNvmInfoPageOwnerSecret,
                                     kRandomData[1]);
  read_and_check_data_page_scrambled(true, kDataRegionStart, kDataPageStart,
                                     kRandomData[3]);
  read_and_check_data_page_scrambled(true, kDataRegionMiddle,
                                     data_page_middle(), kRandomData[4]);
  read_and_check_data_page_scrambled(true, kDataRegionEnd, data_page_end(),
                                     kRandomData[5]);

  LOG_INFO("Enter RMA test complete - waiting for TB");
  // Enter WFI for detection in the testbench.
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

// Function for the third boot, all NVM partitions are readable as the
// LC_STATE is now RMA. Check that the data read from these partitions does
// *not* match the original data and therefore has been successfully wiped.
static void check_wipe_test_phase(void) {
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));
  CHECK(curr_state == kDifLcCtrlStateRma);

  read_and_check_info_page_scrambled(false, kNvmInfoPageCreatorSecret,
                                     kRandomData[0]);
  read_and_check_info_page_scrambled(false, kNvmInfoPageOwnerSecret,
                                     kRandomData[1]);
  read_and_check_info_page_scrambled(false, kNvmInfoPageWaferAuthSecret,
                                     kRandomData[2]);
  read_and_check_data_page_scrambled(false, kDataRegionStart, kDataPageStart,
                                     kRandomData[3]);
  read_and_check_data_page_scrambled(false, kDataRegionMiddle,
                                     data_page_middle(), kRandomData[4]);
  read_and_check_data_page_scrambled(false, kDataRegionEnd, data_page_end(),
                                     kRandomData[5]);
  LOG_INFO("Wipe test complete - done");
}

bool rom_test_main(void) {
  // We need to set the test status as "in test" to indicate to the test code
  // has been reached, even though this test is also in the "boot ROM".
  test_status_set(kTestStatusInTest);

  // This test runs as its own boot ROM (`kind = "rom"`) rather than after the
  // normal test_rom boot flow. The RRAM controller must be initialized before
  // any read/write.
  uint32_t otp_nvm_default_cfg = abs_mmio_read32(
      TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
      OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET);
  CHECK_STATUS_OK(nvm_testutils_rom_init(otp_nvm_default_cfg));

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);

  // We need to initialize the UART regardless if we LOG any messages, since
  // Verilator and FPGA platforms use the UART to communicate the test results.
  if (kDeviceType != kDeviceSimDV) {
    CHECK_DIF_OK(dif_uart_init(
        mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
    CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
    CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
          "kClockFreqPeripheralHz must fit in uint32_t");
    CHECK_DIF_OK(dif_uart_configure(
        &uart0, (dif_uart_config_t){
                    .baudrate = (uint32_t)kUartBaudrate,
                    .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                    .parity_enable = kDifToggleDisabled,
                    .parity = kDifUartParityEven,
                    .tx_enable = kDifToggleEnabled,
                    .rx_enable = kDifToggleEnabled,
                }));
    base_uart_stdout(&uart0);
  }

  // Start of the test specific code.
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc));

  dif_otp_ctrl_t otp;
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  dif_otp_ctrl_config_t otp_config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x0,
      .consistency_period_mask = 0x0,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, otp_config));

  LOG_INFO("Test phase %d (kShortRma: %d)", kTestPhase, kShortRma);
  switch (kTestPhase) {
    case kTestPhaseWriteData:
      write_data_test_phase();
      break;
    case kTestPhaseEnterRMA:
      enter_rma_test_phase();
      break;
    case kTestPhaseCheckWipe:
      check_wipe_test_phase();
      return true;
    default:
      LOG_FATAL("Unexpected Test Phase");
      break;
  }

  return false;
}
