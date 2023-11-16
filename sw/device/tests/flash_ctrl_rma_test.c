// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

volatile uint32_t kTestPhase;
volatile uint32_t kEndTest;

static dif_pinmux_t pinmux;
static dif_flash_ctrl_state_t flash;
static dif_otp_ctrl_t otp_ctrl;

enum {
  kFlashInfoBankId = 0,
  kFlashInfoPartitionId = 0,
  kFlashInfoPageIdCreatorSecret = 1,
  kFlashInfoPageIdOwnerSecret = 2,
  kFlashInfoPageIdIsoPart = 3,
  kTestPhase0 = 0,
  kTestPhase1 = 1,
  kTestPhaseInit = 2,
  kCommandTimeout = 5000000,  // usec
};

// Hardcoded secret data for flash info partition.
static const uint32_t kRandomData[3] = {
    0xbab0bab1,
    0xdeadbeef,
    0xcafefeed,
};

static status_t write_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                                const uint32_t *data, bool scramble) {
  uint32_t address = 0;
  if (scramble) {
    TRY(flash_ctrl_testutils_info_region_scrambled_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  } else {
    TRY(flash_ctrl_testutils_info_region_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  }

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash, address, kFlashInfoPartitionId, data,
      kDifFlashCtrlPartitionTypeInfo, 1));

  LOG_INFO("wr_info: data:0x%x", *data);
  return OK_STATUS();
}

static status_t read_info_page(dif_flash_ctrl_state_t *flash, uint32_t page_id,
                               uint32_t *data, bool scramble) {
  uint32_t address = 0;
  if (scramble) {
    TRY(flash_ctrl_testutils_info_region_scrambled_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  } else {
    TRY(flash_ctrl_testutils_info_region_setup(
        flash, page_id, kFlashInfoBankId, kFlashInfoPartitionId, &address));
  }

  TRY(flash_ctrl_testutils_read(flash, address, kFlashInfoPartitionId, data,
                                kDifFlashCtrlPartitionTypeInfo, 1, 1));

  return OK_STATUS();
}

static status_t read_and_check_info(bool match) {
  uint32_t readback_data[3];
  read_info_page(&flash, kFlashInfoPageIdCreatorSecret, readback_data, true);
  read_info_page(&flash, kFlashInfoPageIdOwnerSecret, readback_data + 1, true);
  read_info_page(&flash, kFlashInfoPageIdIsoPart, readback_data + 2, true);
  LOG_INFO("readdata0: %x", *readback_data);
  LOG_INFO("readdata1: %x", *(readback_data + 1));
  LOG_INFO("readdata2: %x", *(readback_data + 2));
  if (match) {
    // iso partition cannot be accessed in dev state.
    // check create and owner partition only
    CHECK_ARRAYS_EQ(readback_data, kRandomData, 2);
  } else {
    CHECK_ARRAYS_NE(readback_data, kRandomData, 3);
  }
  LOG_INFO("read_and_check is done");
  return OK_STATUS();
}

bool sram_main(void) {
  // Initialize dif handles and pinmux
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));

  ottf_console_init();

  kEndTest = 0;
  kTestPhase = kTestPhaseInit;

  // Waiting for uart input from the host.
  LOG_INFO("Starting test ");
  OTTF_WAIT_FOR(kEndTest, kCommandTimeout);

  switch (kTestPhase) {
    case kTestPhase0:
      LOG_INFO("testphase0");
      write_info_page(&flash, kFlashInfoPageIdCreatorSecret, kRandomData, true);
      write_info_page(&flash, kFlashInfoPageIdOwnerSecret, kRandomData + 1,
                      true);
      write_info_page(&flash, kFlashInfoPageIdIsoPart, kRandomData + 2, true);
      read_and_check_info(true);

      // After update info partition in flash,
      // lock secret2 partition in otp.
      CHECK_STATUS_OK(otp_ctrl_testutils_lock_partition(
          &otp_ctrl, kDifOtpCtrlPartitionSecret2, 0));
      break;
    case kTestPhase1:
      LOG_INFO("testphase1");
      // After RMA, all contents in flash info partition are scrapped.
      // So expecting read data mismatch.
      read_and_check_info(false);
      break;
    default:
      LOG_ERROR("unexpected test phase : %d", kTestPhase);
      break;
  }

  // This print is required for host hand shake.
  LOG_INFO("test_end");
  return true;
}
