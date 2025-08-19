// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>
#include <string.h>

#include "dt/dt_api.h"         // Generated
#include "dt/dt_pinmux.h"      // Generated
#include "dt/dt_rv_plic.h"     // Generated
#include "dt/dt_spi_device.h"  // Generated
#include "dt/dt_spi_host.h"    // Generated
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
#include "sw/device/lib/testing/spi_host_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

// Bit map of command slots to be filtered. This is supplied by the DV
// environment.
static const volatile uint32_t kFilteredCommands;

// Whether to upload write commands and have software relay them.
static const volatile uint8_t kUploadWriteCommands;

// Which readpipeline_mode should be used for read commands.
static const volatile uint8_t kReadPipelineMode;

static const uint32_t kPlicTarget = 0;
static dif_pinmux_t pinmux;
static dt_pinmux_t kPinmuxDt = (dt_pinmux_t)0;
static_assert(kDtPinmuxCount >= 1, "This test requires Pinmux");
static dif_rv_plic_t rv_plic;
static dt_rv_plic_t kRvPlicDt = (dt_rv_plic_t)0;
static_assert(kDtRvPlicCount >= 1, "This test requires a RV PLIC");
static dif_spi_device_handle_t spi_device;
static dt_spi_device_t kSpiDeviceDt = (dt_spi_device_t)0;
static_assert(kDtSpiDeviceCount >= 1,
              "This test requires one SPI Device instance");
static dif_spi_host_t spi_hosts[kDtSpiHostCount];
static dt_spi_host_t kSpiHost0Dt = (dt_spi_host_t)0;
static_assert(kDtSpiHostCount >= 1,
              "This test requiest at least one SPI Host instance");

// Enable pull-ups for spi_host data pins to avoid floating inputs.
static const pinmux_pad_attributes_t pinmux_pad_config[] = {
#if defined(OPENTITAN_IS_EARLGREY)
    {
        .pad = kDtPadIob1,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kDtPadIob3,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling does not need these pads pulled-up
#else
#error "spi_passthrough_test does not support this top"
#endif
    {
        .pad = kDtPadSpiHost0Sd0,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kDtPadSpiHost0Sd1,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kDtPadSpiHost0Sd2,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
    {
        .pad = kDtPadSpiHost0Sd3,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp,
    },
};

#if defined(OPENTITAN_IS_EARLGREY)
/**
 * A convenience struct to associate a mux selection that connects a pad and
 * peripheral. This can be used for an input mux or an output mux.
 */
typedef struct pinmux_select {
  dt_pad_t pad;
  dt_spi_host_t peripheral_dt;
  dt_spi_host_periph_io_t peripheral_sig;
} pinmux_select_t;

static const pinmux_select_t pinmux_out_config[] = {
    {
        .pad = kDtPadIob0,
        .peripheral_dt = kDtSpiHost1,
        .peripheral_sig = kDtSpiHostPeriphIoCsb,
    },
    {
        .pad = kDtPadIob2,
        .peripheral_dt = kDtSpiHost1,
        .peripheral_sig = kDtSpiHostPeriphIoSck,
    },
    {
        .pad = kDtPadIob1,
        .peripheral_dt = kDtSpiHost1,
        .peripheral_sig = kDtSpiHostPeriphIoSd0,
    },
    {
        .pad = kDtPadIob3,
        .peripheral_dt = kDtSpiHost1,
        .peripheral_sig = kDtSpiHostPeriphIoSd1,
    },
    // These peripheral I/Os are not assigned for tests.
    //     {
    //         .pad = ???,
    //         .peripheral_dt = kDtSpiHost1,
    //         .peripheral_sig = kDtSpiHostPeriphIoSd2,
    //     },
    //     {
    //         .pad = ???,
    //         .peripheral_dt = kDtSpiHost1,
    //         .peripheral_sig = kDtSpiHostPeriphIoSd3,
    //     },
};

static const pinmux_select_t pinmux_in_config[] = {
    {
        .pad = kDtPadIob1,
        .peripheral_dt = kDtSpiHost1,
        .peripheral_sig = kDtSpiHostPeriphIoSd0,
    },
    {
        .pad = kDtPadIob3,
        .peripheral_dt = kDtSpiHost1,
        .peripheral_sig = kDtSpiHostPeriphIoSd1,
    },
    // These peripheral I/Os are not assigned for tests.
    //     {
    //         .pad = ???,
    //         .peripheral_dt = kDtSpiHost1,
    //         .peripheral_sig = kDtSpiHostPeriphIoSd2,
    //     },
    //     {
    //         .pad = ???,
    //         .peripheral_dt = kDtSpiHost1,
    //         .peripheral_sig = kDtSpiHostPeriphIoSd3,
    //     },
};
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has 1 SPI host, so SpiHost1 does not exist
#else
#error "spi_passthrough_test does not support this top"
#endif

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
  CHECK_DIF_OK(dif_spi_device_read_flash_payload_buffer(
      &spi_device, start_offset, occupancy, &payload));

  status &= (0xffu << offset);
  status |= ((uint32_t)(payload) << offset);
  CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(&spi_device, status));

  CHECK_STATUS_OK(spi_flash_testutils_issue_write_enable(&spi_hosts[0]));

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
  CHECK_DIF_OK(dif_spi_host_transaction(&spi_hosts[0], /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));
  CHECK_STATUS_OK(spi_flash_testutils_wait_until_not_busy(&spi_hosts[0]));
  CHECK_DIF_OK(dif_spi_device_clear_flash_busy_bit(&spi_device));
}

/**
 * Handle an incoming Chip Erase command.
 *
 * Relays the command out to the downstream SPI flash.
 */
void handle_chip_erase(void) {
  CHECK_STATUS_OK(spi_flash_testutils_erase_chip(&spi_hosts[0]));
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
      spi_flash_testutils_erase_sector(&spi_hosts[0], address, addr_is_4b));
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
  CHECK_DIF_OK(dif_spi_device_read_flash_payload_buffer(
      &spi_device, start_offset, payload_occupancy, payload));

  dif_toggle_t addr4b_enabled;
  CHECK_DIF_OK(
      dif_spi_device_get_4b_address_mode(&spi_device, &addr4b_enabled));

  bool addr_is_4b = dif_toggle_to_bool(addr4b_enabled);
  CHECK_STATUS_OK(spi_flash_testutils_program_page(
      &spi_hosts[0], payload, payload_occupancy, address, addr_is_4b));
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
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&rv_plic, kPlicTarget, &plic_irq_id));

  dt_instance_id_t peripheral_id = dt_plic_id_to_instance_id(plic_irq_id);
  if (peripheral_id == dt_spi_device_instance_id(kSpiDeviceDt)) {
    dt_spi_device_irq_t irq =
        dt_spi_device_irq_from_plic_id(kSpiDeviceDt, plic_irq_id);
    CHECK(irq == kDtSpiDeviceIrqUploadCmdfifoNotEmpty);
    spi_device_isr();
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, kPlicTarget, plic_irq_id));
}

bool test_main(void) {
  // Initialize the pinmux.
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
  pinmux_testutils_init(&pinmux);
  pinmux_testutils_configure_pads(&pinmux, pinmux_pad_config,
                                  ARRAYSIZE(pinmux_pad_config));
#if defined(OPENTITAN_IS_EARLGREY)
  for (int i = 0; i < ARRAYSIZE(pinmux_in_config); ++i) {
    pinmux_select_t setting = pinmux_in_config[i];
    dt_periph_io_t peripheral =
        dt_spi_host_periph_io(setting.peripheral_dt, setting.peripheral_sig);
    CHECK_DIF_OK(dif_pinmux_mio_select_input(&pinmux, peripheral, setting.pad));
  }
  for (int i = 0; i < ARRAYSIZE(pinmux_out_config); ++i) {
    pinmux_select_t setting = pinmux_out_config[i];
    dt_periph_io_t peripheral =
        dt_spi_host_periph_io(setting.peripheral_dt, setting.peripheral_sig);
    CHECK_DIF_OK(
        dif_pinmux_mio_select_output(&pinmux, setting.pad, peripheral));
  }
#elif defined(OPENTITAN_IS_DARJEELING)
// Darjeeling only has 1 SPI Host, and so does not need these pinmux settings
#else
#error "spi_passthrough_test does not support this top"
#endif

  // Configure fast slew rate, strong drive strength, and weak pull-ups for SPI
  // Host 0 pads.
  CHECK_STATUS_OK(spi_host_testutils_configure_host0_pad_attrs(&pinmux));

  // Configure fast slew rate and strong drive strength for SPI device pads.
  CHECK_STATUS_OK(spi_device_testutils_configure_pad_attrs(&pinmux));

  // Initialize the PLIC.
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));

  // Initialize the spi_host devices.
  for (size_t i = 0; i < kDtSpiHostCount; i++) {
    dt_spi_host_t spi_host_dt = (dt_spi_host_t)i;
    uint32_t clock_freq =
        dt_clock_frequency(dt_spi_host_clock(spi_host_dt, kDtSpiHostClockClk));
    CHECK_DIF_OK(dif_spi_host_init_from_dt(spi_host_dt, &spi_hosts[i]));
    init_spi_host(&spi_hosts[i], clock_freq);
  }

  // Initialize spi_device.
  CHECK_DIF_OK(dif_spi_device_init_from_dt(kSpiDeviceDt, &spi_device.dev));
  bool upload_write_commands = (kUploadWriteCommands != 0);

  CHECK_STATUS_OK(spi_device_testutils_configure_passthrough(
      &spi_device, kFilteredCommands, upload_write_commands));
  CHECK_STATUS_OK(spi_device_testutils_configure_read_pipeline(
      &spi_device, (dif_spi_device_read_pipeline_mode_t)kReadPipelineMode,
      (dif_spi_device_read_pipeline_mode_t)kReadPipelineMode));

  // Enable all spi_device and spi_host interrupts, and check that they do not
  // trigger unless command upload is enabled.
  for (int i = 0; i < kDtSpiDeviceIrqCount; ++i) {
    dt_spi_device_irq_t spi_irq = (dt_spi_device_irq_t)i;
    CHECK_DIF_OK(dif_spi_device_irq_set_enabled(&spi_device.dev, spi_irq,
                                                kDifToggleEnabled));
    dif_rv_plic_irq_id_t irq =
        dt_spi_device_irq_to_plic_id(kSpiDeviceDt, spi_irq);
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, irq, kPlicTarget,
                                             kDifToggleEnabled));
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&rv_plic, irq, 0x1));
  }
  for (int i = 0; i < kDtSpiHostIrqCount; ++i) {
    dt_spi_host_irq_t spi_irq = (dt_spi_host_irq_t)i;
    CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_hosts[0], spi_irq,
                                              kDifToggleEnabled));
    dif_rv_plic_irq_id_t irq = dt_spi_host_irq_to_plic_id(kSpiHost0Dt, spi_irq);
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, irq, kPlicTarget,
                                             kDifToggleEnabled));
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
