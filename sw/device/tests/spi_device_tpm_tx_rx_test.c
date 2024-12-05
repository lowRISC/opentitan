// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_spi_device_handle_t spi_device;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;

// Enum for TPM command
typedef enum {
  kTpmWriteCommand = 0x0,
  kTpmReadCommand = 0x80,
  kTpmCommandMask = 0xbf
} tpm_cmd_t;

enum {
  kIterations = 10,
  kTpmCommandRwMask = 0x80,
  kTpmCommandSizeMask = 0x3f,
};

const static dif_spi_device_tpm_config_t kTpmConfig = {
    .interface = kDifSpiDeviceTpmInterfaceCrb,
    .disable_return_by_hardware = false,
    .disable_address_prefix_check = false,
    .disable_locality_check = false};

static volatile bool header_interrupt_received = false;

static void en_plic_irqs(dif_rv_plic_t *plic) {
  // Enable functional interrupts as well as error interrupts to make sure
  // everything is behaving as expected.
  const top_earlgrey_plic_irq_id_t kIrqs[] = {
      kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty,
      kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty,
      kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow,
      kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip,
      kTopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty};

  for (uint32_t i = 0; i < ARRAYSIZE(kIrqs); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        plic, kIrqs[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

    // Assign a default priority
    CHECK_DIF_OK(
        dif_rv_plic_irq_set_priority(plic, kIrqs[i], kDifRvPlicMaxPriority));
  }

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

static void en_spi_device_irqs(dif_spi_device_t *spi_device) {
  const dif_spi_device_irq_t kIrqs[] = {kDifSpiDeviceIrqUploadCmdfifoNotEmpty,
                                        kDifSpiDeviceIrqUploadPayloadNotEmpty,
                                        kDifSpiDeviceIrqUploadPayloadOverflow,
                                        kDifSpiDeviceIrqReadbufWatermark,
                                        kDifSpiDeviceIrqReadbufFlip,
                                        kDifSpiDeviceIrqTpmHeaderNotEmpty};

  for (uint32_t i = 0; i <= ARRAYSIZE(kIrqs); ++i) {
    CHECK_DIF_OK(dif_spi_device_irq_set_enabled(spi_device, kIrqs[i],
                                                kDifToggleEnabled));
  }
}

void ottf_external_isr(uint32_t *exc_info) {
  plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                             .hart_id = kTopEarlgreyPlicTargetIbex0};

  // We should only be receiving the tpm header interrupt during this test, but
  // the tpm rdfifo cmd end intr_state will go high for read FIFO commands.
  spi_device_isr_ctx_t spi_device_ctx = {
      .spi_device = &spi_device.dev,
      .plic_spi_device_start_irq_id =
          kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty,
      .expected_irq = kDifSpiDeviceIrqTpmHeaderNotEmpty,
      .is_only_irq = false};

  top_earlgrey_plic_peripheral_t peripheral;
  dif_spi_device_irq_t spi_device_irq;
  isr_testutils_spi_device_isr(plic_ctx, spi_device_ctx, false, &peripheral,
                               &spi_device_irq);

  switch (spi_device_irq) {
    case kDifSpiDeviceIrqTpmHeaderNotEmpty:
      header_interrupt_received = true;
      // Disable interrupt until work is handled.
      CHECK_DIF_OK(dif_spi_device_irq_set_enabled(
          &spi_device.dev, kDifSpiDeviceIrqTpmHeaderNotEmpty,
          kDifToggleDisabled));
      break;
    default:
      LOG_ERROR("Unexpected interrupt: %d", spi_device_irq);
      break;
  }
}

static void ack_spi_tpm_header_irq(dif_spi_device_handle_t *spi_device) {
  // Clear interrupt state and re-enable interrupt.
  header_interrupt_received = false;
  CHECK_DIF_OK(dif_spi_device_irq_acknowledge(
      &spi_device->dev, kDifSpiDeviceIrqTpmHeaderNotEmpty));
  CHECK_DIF_OK(dif_spi_device_irq_set_enabled(
      &spi_device->dev, kDifSpiDeviceIrqTpmHeaderNotEmpty, kDifToggleEnabled));
}

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi_device));

  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  // Set IoA7 for tpm csb.
  // Longer term this needs to migrate to a top specific, platform specific
  // setting.
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInSpiDeviceTpmCsb,
      kTopEarlgreyPinmuxInselIoa7));

  if (kDeviceType == kDeviceSimDV) {
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 0,
        .drive_strength = 0,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp};

    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyMuxedPadsIoa7,
                                            kDifPinmuxPadKindMio, in_attr,
                                            &out_attr));
  }

  // Configure fast slew rate and strong drive strength for SPI device pads.
  CHECK_STATUS_OK(spi_device_testutils_configure_pad_attrs(&pinmux));

  CHECK_DIF_OK(
      dif_spi_device_tpm_configure(&spi_device, kDifToggleEnabled, kTpmConfig));

  // enable interrupts
  en_plic_irqs(&plic);
  en_spi_device_irqs(&spi_device.dev);

  // Sync message with testbench to begin.
  LOG_INFO("SYNC: Begin TPM Test");

  for (uint32_t i = 0; i < kIterations; i++) {
    LOG_INFO("Iteration %d", i);

    // Wait for write interrupt.
    ATOMIC_WAIT_FOR_INTERRUPT(header_interrupt_received);

    // Check what command we have received. Store it as expected variables
    // and compare when the read command is issued.
    uint8_t write_command = 0;
    uint32_t write_addr = 0;
    CHECK_DIF_OK(dif_spi_device_tpm_get_command(&spi_device, &write_command,
                                                &write_addr));
    CHECK((write_command & kTpmCommandRwMask) == kTpmWriteCommand,
          "Expected write command, received read");

    // Poll for write data to complete.
    uint32_t num_bytes = (write_command & kTpmCommandSizeMask) + 1;
    LOG_INFO("Expecting %d bytes from tpm write", num_bytes);

    uint8_t buf[64] = {0};
    dif_result_t status = kDifOutOfRange;
    while (status == kDifOutOfRange) {
      status = dif_spi_device_tpm_read_data(&spi_device, num_bytes, buf);
    };
    CHECK_DIF_OK(status);

    // Finished processing the write command
    CHECK_DIF_OK(dif_spi_device_tpm_free_write_fifo(&spi_device));
    ack_spi_tpm_header_irq(&spi_device);

    LOG_INFO("SYNC: Waiting Read");
    // Wait for read interrupt.
    ATOMIC_WAIT_FOR_INTERRUPT(header_interrupt_received);

    uint8_t read_command = 0;
    uint32_t read_addr = 0;
    CHECK_DIF_OK(
        dif_spi_device_tpm_get_command(&spi_device, &read_command, &read_addr));
    // Send the written data right back out for reads.
    CHECK_DIF_OK(dif_spi_device_tpm_write_data(&spi_device, num_bytes, buf));
    ack_spi_tpm_header_irq(&spi_device);

    // Make sure the received command matches expectation
    read_command &= kTpmCommandMask;
    LOG_INFO("Expected 0x%x, received 0x%x",
             (kTpmReadCommand | (num_bytes - 1)), read_command);
    CHECK((kTpmReadCommand | (num_bytes - 1)) == read_command,
          "Expected read command, received write");
    CHECK(write_addr == read_addr, "Received address did not match");
  }

  return true;
}
