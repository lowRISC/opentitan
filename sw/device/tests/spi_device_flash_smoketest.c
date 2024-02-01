// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_emulator.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kSpiDeviceDatasetSize = 128,
  kSpiDeviceFlashAddress = 0x00,
};

// A set of bytes to be send out by spi_device.
const uint8_t kSpiTxData[kSpiDeviceDatasetSize] = {
    0xe8, 0x50, 0xc6, 0xb4, 0xbe, 0x16, 0xed, 0x55, 0x16, 0x1d, 0xe6, 0x1c,
    0xde, 0x9f, 0xfd, 0x24, 0x89, 0x81, 0x4d, 0x0d, 0x1a, 0x12, 0x4f, 0x57,
    0xea, 0xd6, 0x6f, 0xc0, 0x7d, 0x46, 0xe7, 0x37, 0x81, 0xd3, 0x8e, 0x16,
    0xad, 0x7b, 0xd0, 0xe2, 0x4f, 0xff, 0x39, 0xe6, 0x71, 0x3c, 0x82, 0x04,
    0xec, 0x3a, 0x27, 0xcc, 0x3d, 0x58, 0x0e, 0x56, 0xd2, 0xd2, 0xb9, 0xa3,
    0xb5, 0x3d, 0xc0, 0x40, 0xba, 0x90, 0x16, 0xd8, 0xe3, 0xa4, 0x22, 0x74,
    0x80, 0xcb, 0x7b, 0xde, 0xd7, 0x3f, 0x4d, 0x93, 0x4d, 0x59, 0x79, 0x88,
    0x24, 0xe7, 0x68, 0x8b, 0x7a, 0x78, 0xb7, 0x07, 0x09, 0x26, 0xcf, 0x6b,
    0x52, 0xd9, 0x4c, 0xd3, 0x33, 0xdf, 0x2e, 0x0d, 0x3b, 0xab, 0x45, 0x85,
    0xc2, 0xc2, 0x19, 0xe5, 0xc7, 0x2b, 0xb0, 0xf6, 0xcb, 0x06, 0xf6, 0xe2,
    0xf5, 0xb1, 0xab, 0xef, 0x6f, 0xd8, 0x23, 0xfd,
};

static status_t configure_jedec_id(dif_spi_device_handle_t *spid) {
  dif_spi_device_flash_id_t id = {
      .device_id = 0x2298,
      .manufacturer_id = 0x74,
      .continuation_code = 0x17,
      .num_continuation_code = 2,
  };
  TRY(dif_spi_device_set_flash_id(spid, id));
  return OK_STATUS();
}

static status_t configure_flash_mode(dif_spi_device_handle_t *spid) {
  dif_spi_device_config_t spi_device_config = {
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModeFlashEmulation,
  };
  TRY(dif_spi_device_configure(spid, spi_device_config));

  dif_spi_device_flash_command_t read_commands[] = {
      {
          // Slot 0: ReadStatus1
          .opcode = kSpiDeviceFlashOpReadStatus1,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 1: ReadStatus2
          .opcode = kSpiDeviceFlashOpReadStatus2,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 2: ReadStatus3
          .opcode = kSpiDeviceFlashOpReadStatus3,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 3: ReadJedecID
          .opcode = kSpiDeviceFlashOpReadJedec,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 4: ReadSfdp
          .opcode = kSpiDeviceFlashOpReadSfdp,
          .address_type = kDifSpiDeviceFlashAddr3Byte,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 1: ReadNormal
          .opcode = kSpiDeviceFlashOpReadNormal,
          .address_type = kDifSpiDeviceFlashAddr3Byte,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
  };

  for (uint8_t i = 0; i < ARRAYSIZE(read_commands); ++i) {
    uint8_t slot = i + kSpiDeviceReadCommandSlotBase;
    TRY(dif_spi_device_set_flash_command_slot(spid, slot, kDifToggleEnabled,
                                              read_commands[i]));
  }

  dif_spi_device_flash_command_t write_commands[] = {
      {
          // Slot 1: PageProgram
          .opcode = kSpiDeviceFlashOpPageProgram,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = true,
          .set_busy_status = true,
      },
  };

  for (uint8_t i = 0; i < ARRAYSIZE(write_commands); ++i) {
    uint8_t slot = i + (uint8_t)kSpiDeviceWriteCommandSlotBase;
    TRY(dif_spi_device_set_flash_command_slot(spid, slot, kDifToggleEnabled,
                                              write_commands[i]));
  }
  return OK_STATUS();
}

bool test_main(void) {
  dif_spi_device_handle_t spid;
  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spid));

  CHECK_STATUS_OK(configure_flash_mode(&spid));

  LOG_INFO("SYNC: Waiting for write page");
  upload_info_t info;
  CHECK_STATUS_OK(spi_device_testutils_wait_for_upload(&spid, &info));

  CHECK_ARRAYS_EQ(info.data, kSpiTxData, ARRAYSIZE(kSpiTxData));

  CHECK_DIF_OK(dif_spi_device_write_flash_buffer(
      &spid, kDifSpiDeviceFlashBufferTypeEFlash, 0, ARRAYSIZE(kSpiTxData),
      kSpiTxData));

  LOG_INFO("Waiting for read");
  CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(&spid, 0x00));

  busy_spin_micros(500000);
  uint32_t address;
  CHECK_DIF_OK(dif_spi_device_get_last_read_address(&spid, &address));
  CHECK(address == (kSpiDeviceFlashAddress + kSpiDeviceDatasetSize - 1));

  return true;
}
