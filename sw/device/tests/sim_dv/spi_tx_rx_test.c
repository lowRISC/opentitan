// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define SPI_DEVICE_DATASET_SIZE 128
#define SPI_DEVICE_NUM_IRQS 6

static const uint16_t kFifoLen = 0x400;
static dif_plic_t plic0;
static dif_spi_device_t spi_device;

// A set of bytes to be send out by spi_device.
// This array will be override with random values in UVM sequence.
static const uint8_t spi_device_tx_data[SPI_DEVICE_DATASET_SIZE] = {
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

// The set of bytes expected to be received by spi_device from spi_host.
// This array will be override with random values in UVM sequence.
static const uint8_t exp_spi_device_rx_data[SPI_DEVICE_DATASET_SIZE] = {
    0x1b, 0x95, 0xc5, 0xb5, 0x8a, 0xa4, 0xa8, 0x9f, 0x6a, 0x7d, 0x6b, 0x0c,
    0xcd, 0xd5, 0xa6, 0x8f, 0x07, 0x3a, 0x9e, 0x82, 0xe6, 0xa2, 0x2b, 0xe0,
    0x0c, 0x30, 0xe8, 0x5a, 0x05, 0x14, 0x79, 0x8a, 0xFf, 0x88, 0x29, 0xda,
    0xc8, 0xdd, 0x82, 0xd5, 0x68, 0xa5, 0x9d, 0x5a, 0x48, 0x02, 0x7f, 0x24,
    0x32, 0xaf, 0x9d, 0xca, 0xa7, 0x06, 0x0c, 0x96, 0x65, 0x18, 0xe4, 0x7f,
    0x26, 0x44, 0xf3, 0x14, 0xC1, 0xe7, 0xd9, 0x82, 0xf7, 0x64, 0xe8, 0x68,
    0xf9, 0x6c, 0xa9, 0xe7, 0xd1, 0x9b, 0xac, 0xe1, 0xFd, 0xd8, 0x59, 0xb7,
    0x8e, 0xdc, 0x24, 0xb8, 0xa7, 0xaf, 0x20, 0xee, 0x6c, 0x61, 0x48, 0x41,
    0xB4, 0x62, 0x3c, 0xcb, 0x2c, 0xbb, 0xe4, 0x44, 0x97, 0x8a, 0x5e, 0x2f,
    0x7f, 0x2b, 0x10, 0xcc, 0x7d, 0x89, 0x32, 0xfd, 0xfd, 0x58, 0x7f, 0xd8,
    0xc7, 0x33, 0xd1, 0x6a, 0xc7, 0xba, 0x78, 0x69,
};

// Set our expectation & event indications of the interrupts we intend to
// exercise in this test. These are declared volatile since they are used by the
// interrupt handler.
static volatile bool expected_irqs[SPI_DEVICE_NUM_IRQS];
static volatile bool fired_irqs[SPI_DEVICE_NUM_IRQS];

/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default external irq handler in
 * `sw/device/lib/handler.h`.
 */
void handler_irq_external(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_plic_irq_id_t plic_irq_id;
  CHECK(dif_plic_irq_claim(&plic0, kTopEarlgreyPlicTargetIbex0, &plic_irq_id) ==
            kDifPlicOk,
        "dif_plic_irq_claim failed");

  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == kTopEarlgreyPlicPeripheralSpiDevice,
        "Interurpt from unexpected peripheral: %d", peripheral);

  // Correlate the interrupt fired at PLIC with SPI DEVICE.
  dif_spi_device_irq_t spi_device_irq = 0;
  switch (plic_irq_id) {
    case kTopEarlgreyPlicIrqIdSpiDeviceRxf:
      spi_device_irq = kDifSpiDeviceIrqRxFull;
      CHECK(expected_irqs[spi_device_irq], "Unexpected RX full interrupt");
      break;
    case kTopEarlgreyPlicIrqIdSpiDeviceRxlvl:
      spi_device_irq = kDifSpiDeviceIrqRxAboveLevel;
      CHECK(expected_irqs[spi_device_irq],
            "Unexpected RX above level interrupt");
      break;
    case kTopEarlgreyPlicIrqIdSpiDeviceTxlvl:
      spi_device_irq = kDifSpiDeviceIrqTxBelowLevel;
      CHECK(expected_irqs[spi_device_irq],
            "Unexpected TX below level interrupt");
      break;
    case kTopEarlgreyPlicIrqIdSpiDeviceRxerr:
      spi_device_irq = kDifSpiDeviceIrqRxError;
      CHECK(expected_irqs[spi_device_irq], "Unexpected RX error interrupt");
      break;
    case kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow:
      spi_device_irq = kDifSpiDeviceIrqRxOverflow;
      CHECK(expected_irqs[spi_device_irq], "Unexpected RX overflow interrupt");
      break;
    case kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow:
      spi_device_irq = kDifSpiDeviceIrqTxUnderflow;
      CHECK(expected_irqs[spi_device_irq], "Unexpected TX underflow interrupt");
      break;
    default:
      LOG_ERROR("Unexpected interrupt (at PLIC): %d", plic_irq_id);
      test_status_set(kTestStatusFailed);
  }
  fired_irqs[spi_device_irq] = true;

  // Check if the same interrupt fired at SPI DEVICE as well.
  bool flag_out;
  CHECK(dif_spi_device_irq_is_pending(&spi_device, spi_device_irq, &flag_out) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_state_get failed");
  CHECK(flag_out,
        "SPI_DEVICE interrupt fired at PLIC did not fire at SPI_DEVICE");

  // Clear the interrupt at SPI DEVICE.
  CHECK(dif_spi_device_irq_acknowledge(&spi_device, spi_device_irq) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_state_clear failed");

  // Complete the IRQ at PLIC.
  CHECK(dif_plic_irq_complete(&plic0, kTopEarlgreyPlicTargetIbex0,
                              &plic_irq_id) == kDifPlicOk,
        "dif_plic_irq_complete failed");
}

/**
 * Initializes SPI_DEVICE and enables the relevant interrupts.
 */
static void spi_device_init_with_irqs(mmio_region_t base_addr,
                                      dif_spi_device_t *spi_device) {
  LOG_INFO("Initializing the SPI_DEVICE.");
  dif_spi_device_config_t spi_device_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_fifo_timeout = 63,
      .rx_fifo_len = kFifoLen,
      .tx_fifo_len = kFifoLen,
  };

  CHECK(dif_spi_device_init((dif_spi_device_params_t){base_addr}, spi_device) ==
            kDifSpiDeviceOk,
        "spi device init failed");

  CHECK(dif_spi_device_configure(spi_device, spi_device_config) ==
            kDifSpiDeviceOk,
        "spi device init failed");

  CHECK(dif_spi_device_irq_set_enabled(spi_device, kDifSpiDeviceIrqRxFull,
                                       kDifSpiDeviceToggleEnabled) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_enable RxFull failed");
  CHECK(dif_spi_device_irq_set_enabled(spi_device, kDifSpiDeviceIrqRxAboveLevel,
                                       kDifSpiDeviceToggleEnabled) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_enable RxAboveLevel failed");
  CHECK(dif_spi_device_irq_set_enabled(spi_device, kDifSpiDeviceIrqTxBelowLevel,
                                       kDifSpiDeviceToggleEnabled) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_enable TxBelowLevel failed");
  CHECK(dif_spi_device_irq_set_enabled(spi_device, kDifSpiDeviceIrqRxError,
                                       kDifSpiDeviceToggleEnabled) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_enable RxError failed");
  CHECK(dif_spi_device_irq_set_enabled(spi_device, kDifSpiDeviceIrqRxOverflow,
                                       kDifSpiDeviceToggleEnabled) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_enable RxOverflow failed");
  CHECK(dif_spi_device_irq_set_enabled(spi_device, kDifSpiDeviceIrqTxUnderflow,
                                       kDifSpiDeviceToggleEnabled) ==
            kDifSpiDeviceOk,
        "dif_spi_device_irq_enable TxUnderflow failed");

  // Initialize the volatile irq variables.
  for (int i = 0; i < SPI_DEVICE_NUM_IRQS; i++) {
    expected_irqs[i] = false;
    fired_irqs[i] = false;
  }
}

/**
 * Initializes PLIC and enables the relevant SPI DEVICE interrupts.
 */
static void plic_init_with_irqs(mmio_region_t base_addr, dif_plic_t *plic) {
  LOG_INFO("Initializing the PLIC.");

  CHECK(dif_plic_init((dif_plic_params_t){.base_addr = base_addr}, plic) ==
            kDifPlicOk,
        "dif_plic_init failed");

  // Enable SPI_DEVICE interrupts at PLIC as edge triggered.
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxf,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxlvl,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdSpiDeviceTxlvl,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxerr,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(
      dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow,
                               kDifPlicIrqTriggerEdge) == kDifPlicOk,
      "dif_plic_irq_set_trigger failed");

  // Set the priority of SPI DEVICE interrupts at PLIC to be >=1 (so ensure the
  // target does get interrupted).
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxf,
                                  kDifPlicMaxPriority) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxlvl,
                                  kDifPlicMaxPriority) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdSpiDeviceTxlvl,
                                  kDifPlicMaxPriority) == kDifPlicOk,
        , "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxerr,
                                  kDifPlicMaxPriority) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(
      dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow,
                                kDifPlicMaxPriority) == kDifPlicOk,
      "dif_plic_irq_set_priority failed");
  CHECK(
      dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow,
                                kDifPlicMaxPriority) == kDifPlicOk,
      "dif_plic_irq_set_priority failed");

  // Set the threshold for the Ibex to 0.
  CHECK(dif_plic_target_set_threshold(plic, kTopEarlgreyPlicTargetIbex0, 0x0) ==
            kDifPlicOk,
        "dif_plic_target_set_threshold failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxf,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxlvl,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdSpiDeviceTxlvl,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxerr,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(
            plic, kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow,
            kTopEarlgreyPlicTargetIbex0, kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");
}

static bool exp_irqs_fired(void) {
  return fired_irqs[kDifSpiDeviceIrqRxAboveLevel] &&
         fired_irqs[kDifSpiDeviceIrqTxBelowLevel] &&
         fired_irqs[kDifSpiDeviceIrqRxOverflow] &&
         fired_irqs[kDifSpiDeviceIrqTxUnderflow] &&
         fired_irqs[kDifSpiDeviceIrqRxFull];
}

static bool execute_test(const dif_spi_device_t *spi_device) {
  LOG_INFO("Executing the test.");

  size_t bytes_transferred = 0;
  CHECK(dif_spi_device_send(spi_device, spi_device_tx_data,
                            SPI_DEVICE_DATASET_SIZE,
                            &bytes_transferred) == kDifSpiDeviceOk);
  if (bytes_transferred != SPI_DEVICE_DATASET_SIZE) {
    LOG_ERROR(
        "SPI_DEVICE TX_FIFO transferred bytes mismatched: {act: %0d, exp: %0d}",
        bytes_transferred, SPI_DEVICE_DATASET_SIZE);
  } else {
    LOG_INFO("Transferred %0d bytes to SPI_DEVICE TX_FIFO.", bytes_transferred);
  }

  CHECK(dif_spi_device_set_irq_levels(spi_device, SPI_DEVICE_DATASET_SIZE,
                                      SPI_DEVICE_DATASET_SIZE / 2) ==
        kDifSpiDeviceOk);
  expected_irqs[kDifSpiDeviceIrqTxBelowLevel] = true;

  bool read_rx_fifo_done = false;
  while (!read_rx_fifo_done || !exp_irqs_fired()) {
    // set rx tx level back to default value so TxBelowLevel irq won't trigger
    if (fired_irqs[kDifSpiDeviceIrqTxBelowLevel] &&
        expected_irqs[kDifSpiDeviceIrqTxBelowLevel]) {
      CHECK(dif_spi_device_set_irq_levels(spi_device, SPI_DEVICE_DATASET_SIZE,
                                          0) == kDifSpiDeviceOk);
      expected_irqs[kDifSpiDeviceIrqTxBelowLevel] = false;
      expected_irqs[kDifSpiDeviceIrqRxAboveLevel] = true;
      LOG_INFO("SPI_DEVICE tx_below_level interrupt fired.");
    }

    // wait for SPI_HOST to send 128 bytes and trigger RxAboveLevel irq
    if (fired_irqs[kDifSpiDeviceIrqRxAboveLevel] &&
        expected_irqs[kDifSpiDeviceIrqRxAboveLevel]) {
      expected_irqs[kDifSpiDeviceIrqRxAboveLevel] = false;
      LOG_INFO("SPI_DEVICE rx_above_level interrupt fired.");
    }

    // when 128 bytes received in RX_FIFO from SPI_HOST,
    // read out and compare against the expected data
    if (fired_irqs[kDifSpiDeviceIrqRxAboveLevel] && !read_rx_fifo_done) {
      size_t bytes_recved = 0;
      uint8_t spi_device_rx_data[SPI_DEVICE_DATASET_SIZE];
      CHECK(dif_spi_device_recv(spi_device, spi_device_rx_data,
                                SPI_DEVICE_DATASET_SIZE,
                                &bytes_recved) == kDifSpiDeviceOk);
      if (bytes_recved == SPI_DEVICE_DATASET_SIZE) {
        LOG_INFO("Received %0d bytes from SPI_DEVICE RX_FIFO.", bytes_recved);
        read_rx_fifo_done = true;
      } else {
        LOG_ERROR(
            "SPI_DEVICE RX_FIFO recvd bytes mismatched: {act: %0d, exp: %0d}",
            bytes_recved, SPI_DEVICE_DATASET_SIZE);
      }
      // expect SPI_HOST to send another 1024 bytes to fill RX SRAM FIFO
      expected_irqs[kDifSpiDeviceIrqTxUnderflow] = true;
      fired_irqs[kDifSpiDeviceIrqRxAboveLevel] = false;

      // Check data consistency.
      LOG_INFO("Checking the received SPI_HOST RX_FIFO data for consistency.");
      for (int i = 0; i < SPI_DEVICE_DATASET_SIZE; ++i) {
        CHECK(spi_device_rx_data[i] == exp_spi_device_rx_data[i],
              "SPI_DEVICE RX_FIFO data[%0d] mismatched: {act: %x, exp: %x}", i,
              spi_device_rx_data[i], exp_spi_device_rx_data[i]);
      }
    }

    if (read_rx_fifo_done && fired_irqs[kDifSpiDeviceIrqTxUnderflow]) {
      expected_irqs[kDifSpiDeviceIrqRxAboveLevel] = true;
      // TxUnderflow will fire every cycle, so disable this interrupt once fired
      CHECK(dif_spi_device_irq_set_enabled(
                spi_device, kDifSpiDeviceIrqTxUnderflow,
                kDifSpiDeviceToggleDisabled) == kDifSpiDeviceOk,
            "dif_spi_device_irq_disable TxBelowLevel failed");
      expected_irqs[kDifSpiDeviceIrqTxUnderflow] = false;
      LOG_INFO("SPI_DEVICE Tx Below level interrupt fired.");
    }

    if (read_rx_fifo_done && fired_irqs[kDifSpiDeviceIrqRxAboveLevel]) {
      expected_irqs[kDifSpiDeviceIrqRxAboveLevel] = false;
      expected_irqs[kDifSpiDeviceIrqRxFull] = true;
      LOG_INFO("SPI_DEVICE RX Above level interrupt fired.");
    }

    // After RX SRAM FIFO full, expect RX async FIFO overflow irq
    if (fired_irqs[kDifSpiDeviceIrqRxFull] &&
        !fired_irqs[kDifSpiDeviceIrqRxOverflow]) {
      expected_irqs[kDifSpiDeviceIrqRxFull] = false;
      expected_irqs[kDifSpiDeviceIrqRxOverflow] = true;
      LOG_INFO("SPI_DEVICE RX_FIFO full interrupt fired.");
    }

    wait_for_interrupt();
  }

  return true;
}

const test_config_t kTestConfig;

bool test_main(void) {
  mmio_region_t spi_device_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  // Initialize SPI_DEVICE
  spi_device_init_with_irqs(spi_device_base_addr, &spi_device);

  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  // Initialize the PLIC
  plic_init_with_irqs(plic_base_addr, &plic0);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return execute_test(&spi_device);
}
