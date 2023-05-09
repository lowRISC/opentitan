// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_uart_t uart0;
static dif_flash_ctrl_state_t flash_state;

enum {
  kFlashInfoPageIdCreatorSecret = 1,
  kFlashInfoPageIdOwnerSecret = 2,
  kFlashInfoPageIdIsoPart = 3,
  kFlashInfoBank = 0,
  kFlashDataRegionZero = 0,
  kFlashDataRegionOne = 1,
  kRegionBaseBank0Page0Index = 0,
  kRegionBaseBank1Page0Index = 256,
  kPartitionId = 0,
  kRegionSize = 1,
  kPageSize = 2048,
  kNumTestWords = 16,
  kNumTestBytes = kNumTestWords * sizeof(uint32_t),
};

enum {
  kTestPhaseCheckUnscrambledInit0 = 0,
  kTestPhaseCheckUnscrambledInit1 = 1,
  kTestPhaseCheckUnscrambledInit2 = 2,
  kTestPhaseCheckScrambledInit0 = 3,
  kTestPhaseCheckScrambledInit1 = 4,
  kTestPhaseCheckBackdoor0 = 5,
  kTestPhaseCheckBackdoor1 = 6,
  kTestPhaseKeymgrPrep = 7,
  kTestPhaseKeymgrTest0 = 8,
  kTestPhaseKeymgrTest1 = 9,
};

enum {
  kNumRegions = 5,
  kAddressBank0Page0Data = 0,
  kAddressBank1Page0Data = 1,
  kAddressCreatorSecret = 2,
  kAddressOwnerSecret = 3,
  kAddressIsoPart = 4,
};

enum {
  kCreatorSecretDataRetSramAddress = 0,
  kOwnerSecretDataRetSramAddress =
      kCreatorSecretDataRetSramAddress + (kNumTestWords * sizeof(uint32_t)),
  kIsoPartDataRetSramAddress =
      kOwnerSecretDataRetSramAddress + (kNumTestWords * sizeof(uint32_t)),
  kBank0Page0DataRetSramAddress =
      kIsoPartDataRetSramAddress + (kNumTestWords * sizeof(uint32_t)),
  kBank1Page0DataRetSramAddress =
      kBank0Page0DataRetSramAddress + (kNumTestWords * sizeof(uint32_t)),
};

// The test phase is updated by the testbench with a symbol backdoor overwrite.
static volatile const uint8_t kTestPhase = 0;

// The test data is updated by the testbench by filling the retention SRAM
// which can then be copied and used locally.
static uint32_t kCreatorSecretData[kNumTestWords];
static uint32_t kOwnerSecretData[kNumTestWords];
static uint32_t kIsoPartData[kNumTestWords];
static uint32_t kBank0Page0Data[kNumTestWords];
static uint32_t kBank1Page0Data[kNumTestWords];

static uint32_t region_addresses[kNumRegions];

static void setup_unscrambled_regions(void) {
  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
      &flash_state, kRegionBaseBank0Page0Index, kFlashDataRegionZero,
      kRegionSize, &region_addresses[kAddressBank0Page0Data]));
  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
      &flash_state, kRegionBaseBank1Page0Index, kFlashDataRegionOne,
      kRegionSize, &region_addresses[kAddressBank1Page0Data]));
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash_state, kFlashInfoPageIdCreatorSecret, kFlashInfoBank, kPartitionId,
      &region_addresses[kAddressCreatorSecret]));
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash_state, kFlashInfoPageIdOwnerSecret, kFlashInfoBank, kPartitionId,
      &region_addresses[kAddressOwnerSecret]));

  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash_state, kFlashInfoPageIdIsoPart, kFlashInfoBank, kPartitionId,
      &region_addresses[kAddressIsoPart]));
}

static void setup_scrambled_regions(void) {
  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_scrambled_setup(
      &flash_state, kRegionBaseBank0Page0Index, kFlashDataRegionZero,
      kRegionSize, &region_addresses[kAddressBank0Page0Data]));
  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_scrambled_setup(
      &flash_state, kRegionBaseBank1Page0Index, kFlashDataRegionOne,
      kRegionSize, &region_addresses[kAddressBank1Page0Data]));
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_scrambled_setup(
      &flash_state, kFlashInfoPageIdCreatorSecret, kFlashInfoBank, kPartitionId,
      &region_addresses[kAddressCreatorSecret]));
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_scrambled_setup(
      &flash_state, kFlashInfoPageIdOwnerSecret, kFlashInfoBank, kPartitionId,
      &region_addresses[kAddressOwnerSecret]));
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_scrambled_setup(
      &flash_state, kFlashInfoPageIdIsoPart, kFlashInfoBank, kPartitionId,
      &region_addresses[kAddressIsoPart]));
}

static void erase_and_write_regions(void) {
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash_state, region_addresses[kAddressBank0Page0Data], kPartitionId,
      kBank0Page0Data, kDifFlashCtrlPartitionTypeData, kNumTestWords));
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash_state, region_addresses[kAddressBank1Page0Data], kPartitionId,
      kBank1Page0Data, kDifFlashCtrlPartitionTypeData, kNumTestWords));
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash_state, region_addresses[kAddressCreatorSecret], kPartitionId,
      kCreatorSecretData, kDifFlashCtrlPartitionTypeInfo, kNumTestWords));
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash_state, region_addresses[kAddressOwnerSecret], kPartitionId,
      kOwnerSecretData, kDifFlashCtrlPartitionTypeInfo, kNumTestWords));
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      &flash_state, region_addresses[kAddressIsoPart], kPartitionId,
      kIsoPartData, kDifFlashCtrlPartitionTypeInfo, kNumTestWords));
}

static void read_and_check_host_if(uint32_t addr, const uint32_t *check_data) {
  uint32_t host_data[kNumTestWords];
  mmio_region_memcpy_from_mmio32(
      mmio_region_from_addr(TOP_EARLGREY_EFLASH_BASE_ADDR), addr, &host_data,
      kNumTestBytes);
  CHECK_ARRAYS_EQ(host_data, check_data, kNumTestWords);
}

static void check_readback_data_match(void) {
  uint32_t readback_data[kNumTestWords];
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, region_addresses[kAddressBank0Page0Data], kPartitionId,
      readback_data, kDifFlashCtrlPartitionTypeData, kNumTestWords, 0));
  CHECK_ARRAYS_EQ(readback_data, kBank0Page0Data, kNumTestWords);
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, region_addresses[kAddressBank1Page0Data], kPartitionId,
      readback_data, kDifFlashCtrlPartitionTypeData, kNumTestWords, 0));
  CHECK_ARRAYS_EQ(readback_data, kBank1Page0Data, kNumTestWords);
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, region_addresses[kAddressCreatorSecret], kPartitionId,
      readback_data, kDifFlashCtrlPartitionTypeInfo, kNumTestWords, 0));
  CHECK_ARRAYS_EQ(readback_data, kCreatorSecretData, kNumTestWords);
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, region_addresses[kAddressOwnerSecret], kPartitionId,
      readback_data, kDifFlashCtrlPartitionTypeInfo, kNumTestWords, 0));
  CHECK_ARRAYS_EQ(readback_data, kOwnerSecretData, kNumTestWords);
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, region_addresses[kAddressIsoPart], kPartitionId,
      readback_data, kDifFlashCtrlPartitionTypeInfo, kNumTestWords, 0));
  CHECK_ARRAYS_EQ(readback_data, kIsoPartData, kNumTestWords);

  read_and_check_host_if(kRegionBaseBank0Page0Index, kBank0Page0Data);
  read_and_check_host_if(kPageSize * kRegionBaseBank1Page0Index,
                         kBank1Page0Data);
}

static bool transaction_end_check_read_error(void) {
  dif_flash_ctrl_output_t output;
  while (true) {
    dif_result_t dif_result = dif_flash_ctrl_end(&flash_state, &output);
    CHECK(dif_result != kDifBadArg);
    CHECK(dif_result != kDifError);
    if (dif_result == kDifOk) {
      break;
    }
  }
  bool is_read_error = !output.error_code.codes.memory_properties_error &
                       output.error_code.codes.read_error &
                       !output.error_code.codes.prog_window_error &
                       !output.error_code.codes.prog_type_error &
                       !output.error_code.codes.shadow_register_error;
  CHECK_DIF_OK(
      dif_flash_ctrl_clear_error_codes(&flash_state, output.error_code.codes));
  return is_read_error;
}

static void check_readback_fail(void) {
  uint32_t readback_data[kNumTestWords];

  dif_flash_ctrl_transaction_t transaction = {
      .byte_address = region_addresses[kAddressBank0Page0Data],
      .op = kDifFlashCtrlOpRead,
      .partition_type = kDifFlashCtrlPartitionTypeData,
      .partition_id = kPartitionId,
      .word_count = kNumTestWords};
  CHECK_DIF_OK(dif_flash_ctrl_start(&flash_state, transaction));
  CHECK_DIF_OK(
      dif_flash_ctrl_read_fifo_pop(&flash_state, kNumTestWords, readback_data));
  CHECK(transaction_end_check_read_error());

  transaction.byte_address = region_addresses[kAddressBank1Page0Data];
  CHECK_DIF_OK(dif_flash_ctrl_start(&flash_state, transaction));
  CHECK_DIF_OK(
      dif_flash_ctrl_read_fifo_pop(&flash_state, kNumTestWords, readback_data));
  CHECK(transaction_end_check_read_error());

  transaction.partition_type = kDifFlashCtrlPartitionTypeInfo;
  transaction.byte_address = region_addresses[kAddressCreatorSecret];
  CHECK_DIF_OK(dif_flash_ctrl_start(&flash_state, transaction));
  CHECK_DIF_OK(
      dif_flash_ctrl_read_fifo_pop(&flash_state, kNumTestWords, readback_data));
  CHECK(transaction_end_check_read_error());

  transaction.byte_address = region_addresses[kAddressOwnerSecret];
  CHECK_DIF_OK(dif_flash_ctrl_start(&flash_state, transaction));
  CHECK_DIF_OK(
      dif_flash_ctrl_read_fifo_pop(&flash_state, kNumTestWords, readback_data));
  CHECK(transaction_end_check_read_error());

  transaction.byte_address = region_addresses[kAddressIsoPart];
  CHECK_DIF_OK(dif_flash_ctrl_start(&flash_state, transaction));
  CHECK_DIF_OK(
      dif_flash_ctrl_read_fifo_pop(&flash_state, kNumTestWords, readback_data));
  CHECK(transaction_end_check_read_error());
}

static void flash_init(void) {
  CHECK_DIF_OK(dif_flash_ctrl_start_controller_init(&flash_state));
  dif_flash_ctrl_status_t flash_ctrl_status;
  while (true) {
    CHECK_DIF_OK(dif_flash_ctrl_get_status(&flash_state, &flash_ctrl_status));
    if (flash_ctrl_status.controller_init_wip == false) {
      break;
    }
  }
}

static void check_unscrambled_init(void) {
  setup_unscrambled_regions();
  erase_and_write_regions();
  flash_init();
  check_readback_data_match();
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

static void check_scrambled_init(void) {
  setup_scrambled_regions();
  erase_and_write_regions();
  check_readback_data_match();
  flash_init();
  check_readback_fail();
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

static void check_scrambled_backdoor_data(void) {
  setup_scrambled_regions();
  flash_init();
  check_readback_data_match();
  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();
}

bool rom_test_main(void) {
  // We need to set the test status as "in test" to indicate to the test code
  // has been reached, even though this test is also in the "boot ROM".
  test_status_set(kTestStatusInTest);
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
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

  // Test code.
  mmio_region_t sram_region_ret_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR);

  mmio_region_memcpy_from_mmio32(sram_region_ret_base_addr,
                                 kCreatorSecretDataRetSramAddress,
                                 &kCreatorSecretData, kNumTestBytes);
  mmio_region_memcpy_from_mmio32(sram_region_ret_base_addr,
                                 kOwnerSecretDataRetSramAddress,
                                 &kOwnerSecretData, kNumTestBytes);
  mmio_region_memcpy_from_mmio32(sram_region_ret_base_addr,
                                 kIsoPartDataRetSramAddress, &kIsoPartData,
                                 kNumTestBytes);
  mmio_region_memcpy_from_mmio32(sram_region_ret_base_addr,
                                 kBank0Page0DataRetSramAddress,
                                 &kBank0Page0Data, kNumTestBytes);
  mmio_region_memcpy_from_mmio32(sram_region_ret_base_addr,
                                 kBank1Page0DataRetSramAddress,
                                 &kBank1Page0Data, kNumTestBytes);

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  switch (kTestPhase) {
    case kTestPhaseCheckUnscrambledInit0:
    case kTestPhaseCheckUnscrambledInit1:
    case kTestPhaseCheckUnscrambledInit2:
      check_unscrambled_init();
      break;
    case kTestPhaseCheckScrambledInit0:
    case kTestPhaseCheckScrambledInit1:
      check_scrambled_init();
      break;
    case kTestPhaseCheckBackdoor0:
    case kTestPhaseCheckBackdoor1:
      check_scrambled_backdoor_data();
      break;
    case kTestPhaseKeymgrPrep:
    case kTestPhaseKeymgrTest0:
    case kTestPhaseKeymgrTest1:
      flash_init();
      test_status_set(kTestStatusInWfi);
      wait_for_interrupt();
      break;
    default:
      break;
  }
  return true;
}
