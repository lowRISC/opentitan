// Copyright lowRISC contributors.
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
} tpm_cmd_t;

const static uint8_t kIterations = 10;
const static uint8_t kTpmCommandRwMask = 0x80;
const static uint8_t kTpmCommandSizeMask = 0x3f;

const static dif_spi_device_tpm_config_t tpm_config = {
    .interface = kDifSpiDeviceTpmInterfaceCrb,
    .disable_return_by_hardware = false,
    .disable_address_prefix_check = false,
    .disable_locality_check = false};

static volatile bool header_interrupt_received = false;

static void en_plic_irqs(dif_rv_plic_t *plic) {
  // Enable functional interrupts as well as error interrupts to make sure
  // everything is behaving as expected.
  top_earlgrey_plic_irq_id_t plic_irqs[] = {
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxFull,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericTxWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxError,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericRxOverflow,
      kTopEarlgreyPlicIrqIdSpiDeviceGenericTxUnderflow,
      kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty,
      kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty,
      kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow,
      kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark,
      kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip,
      kTopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty};

  for (uint32_t i = 0; i < ARRAYSIZE(plic_irqs); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
        plic, plic_irqs[i], kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

    // Assign a default priority
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, plic_irqs[i],
                                              kDifRvPlicMaxPriority));
  }

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

static void en_spi_device_irqs(dif_spi_device_t *spi_device) {
  dif_spi_device_irq_t spi_device_irqs[] = {
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
      kDifSpiDeviceIrqTpmHeaderNotEmpty};

  for (uint32_t i = 0; i <= ARRAYSIZE(spi_device_irqs); ++i) {
    CHECK_DIF_OK(dif_spi_device_irq_set_enabled(spi_device, spi_device_irqs[i],
                                                kDifToggleEnabled));
  }
}

void ottf_external_isr(void) {
  plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                             .hart_id = kTopEarlgreyPlicTargetIbex0};

  // We should only be receiving the tpm header interrupt during this test.
  spi_device_isr_ctx_t spi_device_ctx = {
      .spi_device = &spi_device.dev,
      .plic_spi_device_start_irq_id =
          kTopEarlgreyPlicIrqIdSpiDeviceGenericRxFull,
      .expected_irq = kDifSpiDeviceIrqTpmHeaderNotEmpty,
      .is_only_irq = true};

  top_earlgrey_plic_peripheral_t peripheral;
  dif_spi_device_irq_t spi_device_irq;
  isr_testutils_spi_device_isr(plic_ctx, spi_device_ctx, &peripheral,
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

// This routine is needed to make sure that an interrupt does not sneak in
// and jump excution away between the boolean check and the actual invocation
// of wait_for_interrupt.
static void atomic_wait_for_interrupt(void) {
  irq_global_ctrl(false);
  if (!header_interrupt_received) {
    wait_for_interrupt();
  }
  irq_global_ctrl(true);
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

  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {
      .slew_rate = 0,
      .drive_strength = 0,
      .flags = kDifPinmuxPadAttrPullResistorEnable |
               kDifPinmuxPadAttrPullResistorUp};

  CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyMuxedPadsIoa7,
                                          kDifPinmuxPadKindMio, in_attr,
                                          &out_attr));

  CHECK_DIF_OK(
      dif_spi_device_tpm_configure(&spi_device, kDifToggleEnabled, tpm_config));

  // enable interrupts
  en_plic_irqs(&plic);
  en_spi_device_irqs(&spi_device.dev);

  // Sync message with testbench to begin.
  LOG_INFO("Begin TPM Test");

  for (uint32_t i = 0; i < kIterations; i++) {
    LOG_INFO("Iteration %d", i);

    // Wait for write interrupt.
    atomic_wait_for_interrupt();

    // Check what comamnd we have received. Store it as expected variables
    // and compare when the read command is issued.
    uint8_t write_command;
    uint32_t write_addr;
    CHECK_DIF_OK(dif_spi_device_tpm_get_command(&spi_device, &write_command,
                                                &write_addr));
    CHECK((write_command & kTpmCommandRwMask) == kTpmWriteCommand,
          "Expected write command, received read");

    // Poll for write data to complete.
    uint32_t num_bytes = (write_command & kTpmCommandSizeMask) + 1;
    LOG_INFO("Expecting %d bytes from tpm write", num_bytes);

    uint8_t buf[64];
    dif_result_t status = kDifOutOfRange;
    while (status == kDifOutOfRange) {
      status = dif_spi_device_tpm_read_data(&spi_device, num_bytes, buf);
    };
    CHECK_DIF_OK(status);

    // Finished processing the write command
    ack_spi_tpm_header_irq(&spi_device);

    // Wait for read interrupt.
    atomic_wait_for_interrupt();
    // Send the written data right back out for reads.
    CHECK_DIF_OK(dif_spi_device_tpm_write_data(&spi_device, num_bytes, buf));

    uint8_t read_command;
    uint32_t read_addr;
    CHECK_DIF_OK(
        dif_spi_device_tpm_get_command(&spi_device, &read_command, &read_addr));
    ack_spi_tpm_header_irq(&spi_device);

    // Make sure the received command matches expectation
    LOG_INFO("Expected 0x%x, received 0x%x",
             (kTpmReadCommand | (num_bytes - 1)), read_command);
    CHECK((kTpmReadCommand | (num_bytes - 1)) == read_command,
          "Expected read command, received write");
    CHECK(write_addr == read_addr, "Received address did not match");
  }

  return true;
};
