// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/json/mem.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

volatile uint32_t kTestPhase;
volatile uint32_t kEndTest;

static dif_uart_t uart;
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
};

// Hardcoded secret data for flash info partition.
static const uint32_t kRandomData[3] = {
    0xbab0bab1,
    0xdeadbeef,
    0xcafefeed,
};

status_t command_processor(ujson_t *uj) {
  while (!kEndTest) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    status_t status = ujson_ottf_dispatch(uj, command);
    if (status_err(status) == kUnimplemented) {
      RESP_ERR(uj, status);
    } else if (status_err(status) != kOk) {
      return status;
    }
  }
  return OK_STATUS();
}
#define EXECUTE_TEST(result_, test_function_, ...)                       \
  do {                                                                   \
    LOG_INFO("Starting test " #test_function_ "...");                    \
    uint64_t t_start_ = ibex_mcycle_read();                              \
    status_t local_status = INTO_STATUS(test_function_(__VA_ARGS__));    \
    uint64_t cycles_ = ibex_mcycle_read() - t_start_;                    \
    CHECK(kClockFreqCpuHz <= UINT32_MAX, "");                            \
    uint32_t clock_mhz = (uint32_t)kClockFreqCpuHz / 1000000;            \
    if (status_ok(local_status)) {                                       \
      if (cycles_ <= UINT32_MAX) {                                       \
        uint32_t micros = (uint32_t)cycles_ / clock_mhz;                 \
        LOG_INFO("Successfully finished test " #test_function_           \
                 " in %u cycles or %u us @ %u MHz.",                     \
                 (uint32_t)cycles_, micros, clock_mhz);                  \
      } else {                                                           \
        uint32_t cycles_lower_ = (uint32_t)(cycles_ & UINT32_MAX);       \
        uint32_t cycles_upper_ = (uint32_t)(cycles_ >> 32);              \
        LOG_INFO("Successfully finished test " #test_function_           \
                 " in 0x%08x%08x cycles.",                               \
                 cycles_upper_, cycles_lower_);                          \
      }                                                                  \
    } else {                                                             \
      result_ = local_status;                                            \
      LOG_ERROR("Finished test " #test_function_ ": %r.", local_status); \
    }                                                                    \
  } while (0)

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
  // Initialize UART console.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));

  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                 .parity_enable = kDifToggleDisabled,
                 .parity = kDifUartParityEven,
                 .tx_enable = kDifToggleEnabled,
                 .rx_enable = kDifToggleEnabled,
             }));
  ottf_console_init();

  kEndTest = 0;
  kTestPhase = kTestPhaseInit;

  ujson_t uj = ujson_ottf_console();

  status_t result = OK_STATUS();
  // Waiting for uart input from the host.
  EXECUTE_TEST(result, command_processor, &uj);

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
  return status_ok(result);
}
