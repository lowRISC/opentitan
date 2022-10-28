// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// Bit map of command slots to be filtered. This is supplied by the DV
// environment.
const volatile uint32_t kFilteredCommands;

static dif_pinmux_t pinmux;
static dif_spi_device_handle_t spi_device;
static dif_spi_host_t spi_host0;
static dif_spi_host_t spi_host1;

typedef struct pinmux_pad_attributes {
  dif_pinmux_index_t pad;
  dif_pinmux_pad_kind_t kind;
  dif_pinmux_pad_attr_flags_t flags;
} pinmux_pad_attributes_t;

// Enable pull-ups for spi_host data pins to avoid floating inputs.
static const pinmux_pad_attributes_t pinmux_pad_config[] = {
    {
        .pad = kTopEarlgreyMuxedPadsIob1,
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyMuxedPadsIob3,
        .kind = kDifPinmuxPadKindMio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd0,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd1,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd2,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kTopEarlgreyDirectPadsSpiHost0Sd3,
        .kind = kDifPinmuxPadKindDio,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
};

typedef struct pinmux_select {
  dif_pinmux_index_t pad;
  dif_pinmux_index_t peripheral;
} pinmux_select_t;

static const pinmux_select_t pinmux_out_config[] = {
    {
        .pad = kTopEarlgreyPinmuxMioOutIob0,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Csb,
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob2,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sck,
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob1,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd0,
    },
    {
        .pad = kTopEarlgreyPinmuxMioOutIob3,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd1,
    },
    // These peripheral I/Os are not assigned for tests.
    //     {
    //         .pad = ???,
    //         .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd2,
    //     },
    //     {
    //         .pad = ???,
    //         .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd3,
    //     },
};

static const pinmux_select_t pinmux_in_config[] = {
    {
        .pad = kTopEarlgreyPinmuxInselIob1,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd0,
    },
    {
        .pad = kTopEarlgreyPinmuxInselIob3,
        .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd1,
    },
    // These peripheral I/Os are not assigned for tests.
    //     {
    //         .pad = ???,
    //         .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd2,
    //     },
    //     {
    //         .pad = ???,
    //         .peripheral = kTopEarlgreyPinmuxOutselSpiHost1Sd3,
    //     },
};

/**
 * A set of typical opcodes for the named flash commands.
 */
enum spi_flash_opcode {
  kSpiFlashOpReadJedec = 0x9f,
  kSpiFlashOpReadSfdp = 0x5a,
  kSpiFlashOpReadNormal = 0x03,
  kSpiFlashOpReadFast = 0x0b,
  kSpiFlashOpReadDual = 0x3b,
  kSpiFlashOpReadQuad = 0x6b,
  kSpiFlashOpWriteEnable = 0x06,
  kSpiFlashOpWriteDisable = 0x04,
  kSpiFlashOpReadStatus1 = 0x05,
  kSpiFlashOpReadStatus2 = 0x35,
  kSpiFlashOpReadStatus3 = 0x15,
  kSpiFlashOpWriteStatus1 = 0x01,
  kSpiFlashOpWriteStatus2 = 0x31,
  kSpiFlashOpWriteStatus3 = 0x11,
  kSpiFlashOpChipErase = 0xc7,
  kSpiFlashOpSectorErase = 0x20,
  kSpiFlashOpPageProgram = 0x02,
  kSpiFlashOpEnter4bAddr = 0xb7,
  kSpiFlashOpExit4bAddr = 0xe9,
};

enum spi_device_command_slot {
  kSpiDeviceReadCommandSlotBase = 0,
  kSpiDeviceWriteCommandSlotBase = 11,
};

/**
 * Initialize the provided SPI host. For the most part, the values provided are
 * filler, as spi_host0 will be in passthrough mode and spi_host1 will remain
 * unused throughout the test.
 */
void init_spi_host(dif_spi_host_t *spi_host,
                   uint32_t peripheral_clock_freq_hz) {
  dif_spi_host_config_t config = {
      .spi_clock = peripheral_clock_freq_hz / 2,
      .peripheral_clock_freq_hz = peripheral_clock_freq_hz,
      .chip_select =
          {
              .idle = 2,
              .trail = 2,
              .lead = 2,
          },
  };
  CHECK_DIF_OK(dif_spi_host_configure(spi_host, config));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, /*enabled=*/true));
}

/**
 * Initialize the SPI device to be in passthrough mode and allow the following
 * commands to pass through:
 *  - ReadJedec
 *  - ReadSfdp
 *  - ReadNormal
 *  - ReadFast
 *  - ReadDual
 *  - ReadQuad
 *  - WriteEnable
 *  - WriteDisable
 *  - ReadStatus1
 *  - ReadStatus2
 *  - ReadStatus3
 *  - WriteStatus1
 *  - WriteStatus2
 *  - WriteStatus3
 *  - ChipErase
 *  - SectorErase
 *  - PageProgram
 *  - Enter4bAddr
 *  - Exit4bAddr
 *
 */
void init_spi_device(void) {
  dif_spi_device_config_t spi_device_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModePassthrough,
  };
  CHECK_DIF_OK(dif_spi_device_configure(&spi_device, spi_device_config));

  dif_spi_device_passthrough_intercept_config_t intercept_config = {
      .status = false,
      .jedec_id = false,
      .sfdp = false,
      .mailbox = false,
  };
  CHECK_DIF_OK(dif_spi_device_set_passthrough_intercept_config(
      &spi_device, intercept_config));

  // Set up passthrough filter to allow all commands, initially.
  CHECK_DIF_OK(dif_spi_device_set_all_passthrough_command_filters(
      &spi_device, kDifToggleDisabled));

  uint32_t filters = kFilteredCommands;
  dif_spi_device_flash_command_t read_commands[] = {
      {
          // Slot 0: ReadStatus1
          .opcode = kSpiFlashOpReadStatus1,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 1: ReadStatus2
          .opcode = kSpiFlashOpReadStatus2,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 2: ReadStatus3
          .opcode = kSpiFlashOpReadStatus3,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 3: ReadJedecID
          .opcode = kSpiFlashOpReadJedec,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 4: ReadSfdp
          .opcode = kSpiFlashOpReadSfdp,
          .address_type = kDifSpiDeviceFlashAddr3Byte,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 5: ReadNormal
          .opcode = kSpiFlashOpReadNormal,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 6: ReadFast
          .opcode = kSpiFlashOpReadFast,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 7: ReadDual
          .opcode = kSpiFlashOpReadDual,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoDual,
          .payload_dir_to_host = true,
      },
      {
          // Slot 8: ReadQuad
          .opcode = kSpiFlashOpReadQuad,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoQuad,
          .payload_dir_to_host = true,
      },
  };
  for (int i = 0; i < ARRAYSIZE(read_commands); ++i) {
    uint8_t slot = i + kSpiDeviceReadCommandSlotBase;
    if (bitfield_bit32_read(filters, slot)) {
      CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
          &spi_device, read_commands[i].opcode, kDifToggleEnabled));
    }
    CHECK_DIF_OK(dif_spi_device_set_flash_command_slot(
        &spi_device, slot, kDifToggleEnabled, read_commands[i]));
  }
  dif_spi_device_flash_command_t write_commands[] = {
      {
          // Slot 11: WriteStatus1
          .opcode = kSpiFlashOpWriteStatus1,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
      },
      {
          // Slot 12: WriteStatus2
          .opcode = kSpiFlashOpWriteStatus2,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
      },
      {
          // Slot 13: WriteStatus3
          .opcode = kSpiFlashOpWriteStatus3,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
      },
      {
          // Slot 14: ChipErase
          .opcode = kSpiFlashOpChipErase,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
      },
      {
          // Slot 15: SectorErase
          .opcode = kSpiFlashOpSectorErase,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
      },
      {
          // Slot 16: PageProgram
          .opcode = kSpiFlashOpPageProgram,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
      },
  };
  for (int i = 0; i < ARRAYSIZE(write_commands); ++i) {
    uint8_t slot = i + kSpiDeviceWriteCommandSlotBase;
    if (bitfield_bit32_read(filters, slot)) {
      CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
          &spi_device, write_commands[i].opcode, kDifToggleEnabled));
    }
    CHECK_DIF_OK(dif_spi_device_set_flash_command_slot(
        &spi_device, slot, kDifToggleEnabled, write_commands[i]));
  }
  CHECK_DIF_OK(dif_spi_device_configure_flash_wren_command(
      &spi_device, kDifToggleEnabled, kSpiFlashOpWriteEnable));
  CHECK_DIF_OK(dif_spi_device_configure_flash_wrdi_command(
      &spi_device, kDifToggleEnabled, kSpiFlashOpWriteDisable));
  CHECK_DIF_OK(dif_spi_device_configure_flash_en4b_command(
      &spi_device, kDifToggleEnabled, kSpiFlashOpEnter4bAddr));
  CHECK_DIF_OK(dif_spi_device_configure_flash_ex4b_command(
      &spi_device, kDifToggleEnabled, kSpiFlashOpExit4bAddr));
}

bool test_main(void) {
  // Initialize the pinmux.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  for (int i = 0; i < ARRAYSIZE(pinmux_pad_config); ++i) {
    dif_pinmux_pad_attr_t attr, attr_check;
    pinmux_pad_attributes_t config = pinmux_pad_config[i];
    CHECK_DIF_OK(
        dif_pinmux_pad_get_attrs(&pinmux, config.pad, config.kind, &attr));
    attr.flags = config.flags;
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, config.pad, config.kind,
                                            attr, &attr_check));
    // Check that attributes were accepted?
  }
  for (int i = 0; i < ARRAYSIZE(pinmux_in_config); ++i) {
    pinmux_select_t setting = pinmux_in_config[i];
    CHECK_DIF_OK(
        dif_pinmux_input_select(&pinmux, setting.peripheral, setting.pad));
  }
  for (int i = 0; i < ARRAYSIZE(pinmux_out_config); ++i) {
    pinmux_select_t setting = pinmux_out_config[i];
    CHECK_DIF_OK(
        dif_pinmux_output_select(&pinmux, setting.pad, setting.peripheral));
  }

  // Initialize the spi_host devices.
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host0));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host1));
  init_spi_host(&spi_host0, (uint32_t)kClockFreqHiSpeedPeripheralHz);
  init_spi_host(&spi_host1, (uint32_t)kClockFreqPeripheralHz);

  // Initialize spi_device.
  mmio_region_t spi_device_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init_handle(spi_device_base_addr, &spi_device));
  init_spi_device();

  // Send the DV environment a specific message for synchronization. The
  // sequencer can pick this up and know it can begin sending SPI flash
  // transactions.
  LOG_INFO("Test setup complete.");

  // Enable all spi_device and spi_host interrupts, and check that they do not
  // trigger.
  dif_spi_device_irq_t all_spi_device_irqs[] = {
      kDifSpiDeviceIrqGenericRxFull,
      kDifSpiDeviceIrqGenericRxWatermark,
      kDifSpiDeviceIrqGenericTxWatermark,
      kDifSpiDeviceIrqGenericRxError,
      kDifSpiDeviceIrqGenericRxOverflow,
      kDifSpiDeviceIrqGenericTxUnderflow,
      kDifSpiDeviceIrqUploadCmdfifoNotEmpty,
      kDifSpiDeviceIrqUploadPayloadNotEmpty,
      kDifSpiDeviceIrqUploadPayloadOverflow,
      kDifSpiDeviceIrqReadbufWatermark,
      kDifSpiDeviceIrqReadbufFlip,
      kDifSpiDeviceIrqTpmHeaderNotEmpty,
  };
  for (int i = 0; i < ARRAYSIZE(all_spi_device_irqs); ++i) {
    dif_spi_device_irq_t irq = all_spi_device_irqs[i];
    CHECK_DIF_OK(dif_spi_device_irq_set_enabled(&spi_device.dev, irq,
                                                kDifToggleEnabled));
  }
  CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host0, kDifSpiHostIrqError,
                                            kDifToggleEnabled));
  CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host0, kDifSpiHostIrqSpiEvent,
                                            kDifToggleEnabled));
  irq_external_ctrl(/*en=*/true);
  wait_for_interrupt();

  // No interrupts are expected, so fail if one occurred. Note that the DV
  // environment is the only one that can signal that the test has passed.
  LOG_INFO("Received unexpected interrupt, ending wfi");
  return false;
}
