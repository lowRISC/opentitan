// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>
#include <string.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// Bit map of command slots to be filtered. This is supplied by the DV
// environment.
const volatile uint32_t kFilteredCommands;

// Whether to upload write commands and have software relay them.
const volatile uint8_t kUploadWriteCommands;

static dif_pinmux_t pinmux;
static dif_rv_plic_t rv_plic;
static dif_spi_device_handle_t spi_device;
static dif_spi_host_t spi_host0;
static dif_spi_host_t spi_host1;

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

/**
 * A convenience struct to associate a mux selection that connects a pad and
 * peripheral. This can be used for an input mux or an output mux.
 */
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
 * Handle an incoming Write Status command.
 *
 * Modifies the internal status register and relays the command out to the
 * downstream SPI flash.
 *
 * @param status The aggregated value of all three flash status registers prior
 * to this command's execution.
 * @param offset The bit offset for the byte to be modified by the payload.
 * @param opcode The opcode corresponding to the incoming command.
 */
void handle_write_status(uint32_t status, uint8_t offset, uint8_t opcode) {
  uint8_t payload;
  uint16_t occupancy;
  uint32_t start_offset;
  CHECK_DIF_OK(dif_spi_device_get_flash_payload_fifo_occupancy(
      &spi_device, &occupancy, &start_offset));
  CHECK(occupancy == 1);
  CHECK_DIF_OK(dif_spi_device_read_flash_buffer(
      &spi_device, kDifSpiDeviceFlashBufferTypePayload, start_offset, occupancy,
      &payload));

  status &= (0xffu << offset);
  status |= ((uint32_t)(payload) << offset);
  CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(&spi_device, status));

  CHECK_STATUS_OK(spi_flash_testutils_issue_write_enable(&spi_host0));

  dif_spi_host_segment_t transaction[] = {
      {.type = kDifSpiHostSegmentTypeOpcode,
       .opcode = {.opcode = opcode, .width = kDifSpiHostWidthStandard}},
      {
          .type = kDifSpiHostSegmentTypeTx,
          .tx =
              {
                  .width = kDifSpiHostWidthStandard,
                  .buf = &payload,
                  .length = 1,
              },
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(&spi_host0, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));
  CHECK_STATUS_OK(spi_flash_testutils_wait_until_not_busy(&spi_host0));
  CHECK_DIF_OK(dif_spi_device_clear_flash_busy_bit(&spi_device));
}

/**
 * Handle an incoming Chip Erase command.
 *
 * Relays the command out to the downstream SPI flash.
 */
void handle_chip_erase(void) {
  CHECK_STATUS_OK(spi_flash_testutils_erase_chip(&spi_host0));
  CHECK_DIF_OK(dif_spi_device_clear_flash_busy_bit(&spi_device));
}

/**
 * Handle an incoming Sector Erase command.
 *
 * Relays the command out to the downstream SPI flash.
 */
void handle_sector_erase(void) {
  uint8_t occupancy;
  CHECK_DIF_OK(
      dif_spi_device_get_flash_address_fifo_occupancy(&spi_device, &occupancy));
  CHECK(occupancy == 1);

  uint32_t address;
  CHECK_DIF_OK(dif_spi_device_pop_flash_address_fifo(&spi_device, &address));

  dif_toggle_t addr4b_enabled;
  CHECK_DIF_OK(
      dif_spi_device_get_4b_address_mode(&spi_device, &addr4b_enabled));

  bool addr_is_4b = dif_toggle_to_bool(addr4b_enabled);
  CHECK_STATUS_OK(
      spi_flash_testutils_erase_sector(&spi_host0, address, addr_is_4b));
  CHECK_DIF_OK(dif_spi_device_clear_flash_busy_bit(&spi_device));
}

/**
 * Handle an incoming Page Program command.
 *
 * Relays the command out to the downstream SPI flash.
 */
void handle_page_program(void) {
  uint8_t address_occupancy;
  CHECK_DIF_OK(dif_spi_device_get_flash_address_fifo_occupancy(
      &spi_device, &address_occupancy));
  CHECK(address_occupancy == 1);

  uint32_t address;
  CHECK_DIF_OK(dif_spi_device_pop_flash_address_fifo(&spi_device, &address));

  uint8_t payload[256];
  uint16_t payload_occupancy;
  uint32_t start_offset;
  CHECK_DIF_OK(dif_spi_device_get_flash_payload_fifo_occupancy(
      &spi_device, &payload_occupancy, &start_offset));
  CHECK(start_offset == 0);
  CHECK(payload_occupancy <= sizeof(payload));
  CHECK_DIF_OK(dif_spi_device_read_flash_buffer(
      &spi_device, kDifSpiDeviceFlashBufferTypePayload, start_offset,
      payload_occupancy, payload));

  dif_toggle_t addr4b_enabled;
  CHECK_DIF_OK(
      dif_spi_device_get_4b_address_mode(&spi_device, &addr4b_enabled));

  bool addr_is_4b = dif_toggle_to_bool(addr4b_enabled);
  CHECK_STATUS_OK(spi_flash_testutils_program_page(
      &spi_host0, payload, payload_occupancy, address, addr_is_4b));
  CHECK_DIF_OK(dif_spi_device_clear_flash_busy_bit(&spi_device));
}

// This function assumes only one command will ever be uploaded to the FIFO at a
// time. The IP does not currently make any such guarantee.
void spi_device_process_upload_fifo(void) {
  dif_irq_type_t irq_type;
  CHECK_DIF_OK(dif_spi_device_irq_get_type(
      &spi_device.dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty, &irq_type));
  if (irq_type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(dif_spi_device_irq_acknowledge(
        &spi_device.dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty));
  }

  // Uploaded commands should all set the busy bit, and WREN should have been
  // submitted before the uploaded command.
  uint32_t status;
  CHECK_DIF_OK(dif_spi_device_get_flash_status_registers(&spi_device, &status));
  CHECK(status & kSpiFlashStatusBitWip);
  CHECK(status & kSpiFlashStatusBitWel);

  uint8_t command;
  CHECK_DIF_OK(dif_spi_device_pop_flash_command_fifo(&spi_device, &command));
  // Check command against the ones we expect.
  // Call command-specific handlers, probably, which validate the commands. Then
  // execute.
  if (command == kSpiDeviceFlashOpWriteStatus1) {
    handle_write_status(status, /*offset=*/0, command);
  } else if (command == kSpiDeviceFlashOpWriteStatus2) {
    handle_write_status(status, /*offset=*/8, command);
  } else if (command == kSpiDeviceFlashOpWriteStatus3) {
    handle_write_status(status, /*offset=*/16, command);
  } else if (command == kSpiDeviceFlashOpChipErase) {
    handle_chip_erase();
  } else if (command == kSpiDeviceFlashOpSectorErase) {
    handle_sector_erase();
  } else if (command == kSpiDeviceFlashOpPageProgram) {
    handle_page_program();
  } else {
    CHECK(false, "Received unexpected command 0x%x", command);
  }

  CHECK_DIF_OK(dif_spi_device_irq_set_enabled(
      &spi_device.dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty,
      kDifToggleEnabled));
}

/**
 * Check that the command FIFO is not empty, and mask the interrupt for deferred
 * processing.
 *
 * Runs in interrupt context.
 */
void spi_device_isr(void) {
  bool cmdfifo_not_empty;
  CHECK_DIF_OK(dif_spi_device_irq_is_pending(
      &spi_device.dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty,
      &cmdfifo_not_empty));
  CHECK(cmdfifo_not_empty);
  CHECK_DIF_OK(dif_spi_device_irq_set_enabled(
      &spi_device.dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty,
      kDifToggleDisabled));
}

/**
 * Handle SPI device interrupts.
 *
 * Runs in interrupt context.
 */
void ottf_external_isr(void) {
  const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&rv_plic, kPlicTarget, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  switch (peripheral) {
    case kTopEarlgreyPlicPeripheralSpiDevice:
      // Only the UploadCmdfifoNotEmpty interrupt is expected.
      CHECK(plic_irq_id == kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty);
      spi_device_isr();
      break;
    default:
      break;
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, kPlicTarget, plic_irq_id));
}

bool test_main(void) {
  // Initialize the pinmux.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  pinmux_testutils_configure_pads(&pinmux, pinmux_pad_config,
                                  ARRAYSIZE(pinmux_pad_config));
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

  // Initialize the PLIC.
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));

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
  bool upload_write_commands = (kUploadWriteCommands != 0);
  CHECK_STATUS_OK(spi_device_testutils_configure_passthrough(
      &spi_device, kFilteredCommands, upload_write_commands));

  // Enable all spi_device and spi_host interrupts, and check that they do not
  // trigger unless command upload is enabled.
  dif_spi_device_irq_t all_spi_device_irqs[] = {
      kDifSpiDeviceIrqGenericRxFull,         kDifSpiDeviceIrqGenericRxWatermark,
      kDifSpiDeviceIrqGenericTxWatermark,    kDifSpiDeviceIrqGenericRxError,
      kDifSpiDeviceIrqGenericRxOverflow,     kDifSpiDeviceIrqGenericTxUnderflow,
      kDifSpiDeviceIrqUploadCmdfifoNotEmpty, kDifSpiDeviceIrqReadbufWatermark,
      kDifSpiDeviceIrqReadbufFlip,           kDifSpiDeviceIrqTpmHeaderNotEmpty,
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

  dif_rv_plic_irq_id_t spi_irqs[] = {
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxFull,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericTxWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxError,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxOverflow,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericTxUnderflow,
      kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty,
      kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip,
      kTopEarlgreyPlicIrqIdSpiHost0Error,
      kTopEarlgreyPlicIrqIdSpiHost0SpiEvent,
  };
  for (int i = 0; i < ARRAYSIZE(spi_irqs); ++i) {
    dif_rv_plic_irq_id_t irq = spi_irqs[i];
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        &rv_plic, irq, kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&rv_plic, irq, 0x1));
  }
  irq_external_ctrl(/*en=*/true);

  // Send the DV environment a specific message for synchronization. The
  // sequencer can pick this up and know it can begin sending SPI flash
  // transactions.
  LOG_INFO("Test setup complete.");

  while (true) {
    bool cmdfifo_not_empty_irq_pending;
    irq_global_ctrl(/*en=*/false);
    CHECK_DIF_OK(dif_spi_device_irq_is_pending(
        &spi_device.dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty,
        &cmdfifo_not_empty_irq_pending));
    if (!cmdfifo_not_empty_irq_pending) {
      wait_for_interrupt();
    }
    irq_global_ctrl(/*en=*/true);
    spi_device_process_upload_fifo();
  }
  return true;
}
