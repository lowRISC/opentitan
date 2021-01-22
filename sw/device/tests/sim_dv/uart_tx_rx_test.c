// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define UART_DATASET_SIZE 128

static dif_uart_t uart;
static dif_plic_t plic;

/**
 * UART TX RX test
 *
 * This test sends and receives a known dataset over UART. The size of the
 * dataset is indicated with UART_DATASET_SIZE. The dataset is agreed upon by
 * the device (a.k.a. the OpenTitan chip) and the host (a.k.a. the simulation
 * device, such as DV testbench) communicating with it. Data transmitted over
 * TX is checked for correctness at the host, and likewise, data sent by the
 * host is checked for correctness at the device (in this SW test). The data
 * transmitted over TX and RX ports may occur simultaneously. The test ensures
 * that the TX watermark, RX watermark and TX empty interrupts are seen.
 * At the end, the host transmits another set of random data (greater than the
 * RX fifo size) which the device drops, to generate the RX overflow condition.
 * The test passes when the datasets at both ends match the expected and all
 * required interrupts are seen.
 */

/**
 * UART test data transfer direction
 *
 * Enumeration indicating the direction of transfer of test data.
 */
typedef enum uart_direction {
  kUartSend = 0,
  kUartReceive,
} uart_direction_t;

// TODO: Make these datasets random.

// A set of bytes to be send out of TX.
static const uint8_t uart_tx_data[UART_DATASET_SIZE] = {
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

// The set of bytes expected to be received over RX.
static const uint8_t exp_uart_rx_data[UART_DATASET_SIZE] = {
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
static volatile bool exp_uart_irq_tx_watermark;
static volatile bool uart_irq_tx_watermark_fired;
static volatile bool exp_uart_irq_rx_watermark;
static volatile bool uart_irq_rx_watermark_fired;
static volatile bool exp_uart_irq_tx_empty;
static volatile bool uart_irq_tx_empty_fired;
static volatile bool exp_uart_irq_rx_overflow;
static volatile bool uart_irq_rx_overflow_fired;

/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default external irq handler in
 * `sw/device/lib/handler.h`.
 */
void handler_irq_external(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_plic_irq_id_t plic_irq_id;
  CHECK(dif_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0, &plic_irq_id) ==
            kDifPlicOk,
        "dif_plic_irq_claim failed");

  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == kTopEarlgreyPlicPeripheralUart0,
        "Interurpt from unexpected peripheral: %d", peripheral);

  // Correlate the interrupt fired at PLIC with UART.
  dif_uart_irq_t uart_irq;
  switch (plic_irq_id) {
    case kTopEarlgreyPlicIrqIdUart0TxWatermark:
      CHECK(exp_uart_irq_tx_watermark, "Unexpected TX watermark interrupt");
      uart_irq_tx_watermark_fired = true;
      uart_irq = kDifUartIrqTxWatermark;
      break;
    case kTopEarlgreyPlicIrqIdUart0RxWatermark:
      CHECK(exp_uart_irq_rx_watermark, "Unexpected RX watermark interrupt");
      uart_irq_rx_watermark_fired = true;
      uart_irq = kDifUartIrqRxWatermark;
      break;
    case kTopEarlgreyPlicIrqIdUart0TxEmpty:
      CHECK(exp_uart_irq_tx_empty, "Unexpected TX empty interrupt");
      uart_irq_tx_empty_fired = true;
      uart_irq = kDifUartIrqTxEmpty;
      break;
    case kTopEarlgreyPlicIrqIdUart0RxOverflow:
      CHECK(exp_uart_irq_rx_overflow, "Unexpected RX overflow interrupt");
      uart_irq_rx_overflow_fired = true;
      uart_irq = kDifUartIrqRxOverflow;
      break;
    default:
      LOG_ERROR("Unexpected interrupt (at PLIC): %d", plic_irq_id);
      test_status_set(kTestStatusFailed);
      // The `abort()` call below is redundant. It is added to prevent the
      // compilation error due to not initializing the `uart_irq` enum variable
      // above. See issue #2157 for moe details.
      abort();
  }

  // Check if the same interrupt fired at UART as well.
  bool is_pending;
  CHECK(dif_uart_irq_is_pending(&uart, uart_irq, &is_pending) == kDifUartOk,
        "dif_uart_irq_is_pending failed");
  CHECK(is_pending, "UART interrupt fired at PLIC did not fire at UART");

  // Clear the interrupt at UART.
  CHECK(dif_uart_irq_acknowledge(&uart, uart_irq) == kDifUartOk,
        "dif_uart_irq_acknowledge failed");

  // Complete the IRQ at PLIC.
  CHECK(dif_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0,
                              &plic_irq_id) == kDifPlicOk,
        "dif_plic_irq_complete failed");
}

/**
 * Initializes UART and enables the relevant interrupts.
 */
static void uart_init_with_irqs(mmio_region_t base_addr, dif_uart_t *uart) {
  LOG_INFO("Initializing the UART.");

  CHECK(dif_uart_init(
            (dif_uart_params_t){
                .base_addr = base_addr,
            },
            uart) == kDifUartOk,
        "dif_uart_init failed");
  CHECK(dif_uart_configure(uart,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifUartToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifUartConfigOk,
        "dif_uart_configure failed");

  // Set the TX and RX watermark to 16 bytes.
  CHECK(dif_uart_watermark_tx_set(uart, kDifUartWatermarkByte16) == kDifUartOk,
        "dif_uart_watermark_tx_set failed");
  CHECK(dif_uart_watermark_rx_set(uart, kDifUartWatermarkByte16) == kDifUartOk,
        "dif_uart_watermark_rx_set failed");

  // Enable these UART interrupts - TX/TX watermark, TX empty and RX overflow.
  CHECK(dif_uart_irq_set_enabled(uart, kDifUartIrqTxWatermark,
                                 kDifUartToggleEnabled) == kDifUartOk,
        "dif_uart_irq_set_enabled failed");
  CHECK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                 kDifUartToggleEnabled) == kDifUartOk,
        "dif_uart_irq_set_enabled failed");
  CHECK(dif_uart_irq_set_enabled(uart, kDifUartIrqTxEmpty,
                                 kDifUartToggleEnabled) == kDifUartOk,
        "dif_uart_irq_set_enabled failed");
  CHECK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxOverflow,
                                 kDifUartToggleEnabled) == kDifUartOk,
        "dif_uart_irq_set_enabled failed");
}

/**
 * Initializes PLIC and enables the relevant UART interrupts.
 */
static void plic_init_with_irqs(mmio_region_t base_addr, dif_plic_t *plic) {
  LOG_INFO("Initializing the PLIC.");

  CHECK(dif_plic_init((dif_plic_params_t){.base_addr = base_addr}, plic) ==
            kDifPlicOk,
        "dif_plic_init failed");

  // Enable UART interrupts at PLIC as edge triggered.
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0TxWatermark,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxWatermark,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0TxEmpty,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxFrameErr,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxBreakErr,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxTimeout,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");
  CHECK(dif_plic_irq_set_trigger(plic, kTopEarlgreyPlicIrqIdUart0RxParityErr,
                                 kDifPlicIrqTriggerEdge) == kDifPlicOk,
        "dif_plic_irq_set_trigger failed");

  // Set the priority of UART interrupts at PLIC to be >=1 (so ensure the target
  // does get interrupted).
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0TxWatermark,
                                  0x1) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxWatermark,
                                  0x2) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0TxEmpty,
                                  0x3) == kDifPlicOk,
        , "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                  0x1) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxFrameErr,
                                  0x2) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxBreakErr,
                                  0x3) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxTimeout,
                                  0x1) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");
  CHECK(dif_plic_irq_set_priority(plic, kTopEarlgreyPlicIrqIdUart0RxParityErr,
                                  0x2) == kDifPlicOk,
        "dif_plic_irq_set_priority failed");

  // Set the threshold for the Ibex to 0.
  CHECK(dif_plic_target_set_threshold(plic, kTopEarlgreyPlicTargetIbex0, 0x0) ==
            kDifPlicOk,
        "dif_plic_target_set_threshold failed");

  // Enable all UART interrupts at the PLIC.
  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0TxWatermark,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxWatermark,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0TxEmpty,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxOverflow,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxFrameErr,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxBreakErr,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxTimeout,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");

  CHECK(dif_plic_irq_set_enabled(plic, kTopEarlgreyPlicIrqIdUart0RxParityErr,
                                 kTopEarlgreyPlicTargetIbex0,
                                 kDifPlicToggleEnabled) == kDifPlicOk,
        "dif_plic_irq_set_enabled failed");
}

/**
 * Continue ongoing transmission of bytes.
 *
 * This is a wrapper around `dif_uart_bytes_send|receive()` functions. It picks
 * up an ongoing transfer of data starting at `dataset_index` location until
 * the UART can no longer accept any more data to be sent / return any more
 * data received, depending on the direction of the data transfer indicated with
 * the `uart_direction` argument. It uses the `bytes_written` / `bytes_read`
 * value to advance the `dataset_index` for the next round. It updates the
 * `transfer_done` arg to indicate if the ongoing transfer has completed.
 */
static bool uart_transfer_ongoing_bytes(const dif_uart_t *uart,
                                        uart_direction_t uart_direction,
                                        uint8_t *data, size_t dataset_size,
                                        size_t *dataset_index,
                                        bool *transfer_done) {
  size_t bytes_remaining = dataset_size - *dataset_index;
  size_t bytes_transferred = 0;
  bool result = false;
  switch (uart_direction) {
    case kUartSend:
      result = dif_uart_bytes_send(uart, &data[*dataset_index], bytes_remaining,
                                   &bytes_transferred) == kDifUartOk;
      break;
    case kUartReceive:
      result =
          dif_uart_bytes_receive(uart, bytes_remaining, &data[*dataset_index],
                                 &bytes_transferred) == kDifUartOk;
      break;
    default:
      LOG_FATAL("Invalid UART data transfer direction!");
  }
  *dataset_index += bytes_transferred;
  *transfer_done = *dataset_index == dataset_size;
  return result;
}

static bool execute_test(const dif_uart_t *uart) {
  bool uart_tx_done = false;
  size_t uart_tx_bytes_written = 0;
  exp_uart_irq_tx_watermark = true;
  // Set the flag below to true to allow TX data to be sent the first time in
  // the if comdition below. Subsequently, TX watermark interrupt will trigger
  // more data to be sent.
  uart_irq_tx_watermark_fired = true;
  exp_uart_irq_tx_empty = false;
  uart_irq_tx_empty_fired = false;

  bool uart_rx_done = false;
  size_t uart_rx_bytes_read = 0;
  exp_uart_irq_rx_watermark = true;
  // Set the flag below to true to allow RX data to be received the first time
  // in the if comdition below. Subsequently, RX watermark interrupt will
  // trigger more data to be received.
  uart_irq_rx_watermark_fired = true;
  exp_uart_irq_rx_overflow = false;
  uart_irq_rx_overflow_fired = false;

  // A set of bytes actually received over RX.
  uint8_t uart_rx_data[UART_DATASET_SIZE];

  LOG_INFO("Executing the test.");
  while (!uart_tx_done || !uart_rx_done || !uart_irq_tx_empty_fired ||
         !uart_irq_rx_overflow_fired) {
    if (!uart_tx_done && uart_irq_tx_watermark_fired) {
      uart_irq_tx_watermark_fired = false;

      // Send the remaining uart_tx_data as and when the TX watermark fires.
      CHECK(uart_transfer_ongoing_bytes(
          uart, kUartSend, (uint8_t *)uart_tx_data, UART_DATASET_SIZE,
          &uart_tx_bytes_written, &uart_tx_done));

      if (uart_tx_done) {
        // At this point, we have sent the required number of bytes.
        // Expect the TX empty interrupt to fire at some point.
        exp_uart_irq_tx_empty = true;
      }
    }

    if (!uart_rx_done && uart_irq_rx_watermark_fired) {
      uart_irq_rx_watermark_fired = false;

      // Receive the remaining uart_rx_data as and when the RX watermark fires.
      CHECK(uart_transfer_ongoing_bytes(uart, kUartReceive, uart_rx_data,
                                        UART_DATASET_SIZE, &uart_rx_bytes_read,
                                        &uart_rx_done));

      if (uart_rx_done) {
        exp_uart_irq_rx_watermark = false;
        // At this point we have received the required number of bytes.
        // We disable the RX watermark interrupt and let the fifo
        // overflow by dropping all future incoming data.
        CHECK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                       kDifUartToggleDisabled) == kDifUartOk,
              "dif_uart_irq_set_enabled failed");
        // Expect the RX overflow interrupt to fire at some point.
        exp_uart_irq_rx_overflow = true;
      }
    }

    if (uart_irq_tx_empty_fired) {
      exp_uart_irq_tx_watermark = false;
      exp_uart_irq_tx_empty = false;
    }

    if (uart_irq_rx_overflow_fired) {
      exp_uart_irq_rx_overflow = false;
    }

    // Wait for the next interrupt to arrive.
    // This check here is necessary as rx interrupts may sometimes occur ahead
    // of tx interrupts.  When this happens, the tx handling code above is not
    // triggerd and as a result an unexpected tx_empty interrupt is fired later.
    if (!uart_irq_rx_watermark_fired && !uart_irq_tx_watermark_fired) {
      wait_for_interrupt();
    }
  }

  // Check data consistency.
  LOG_INFO("Checking the received UART RX data for consistency.");
  for (int i = 0; i < UART_DATASET_SIZE; ++i) {
    CHECK(uart_rx_data[i] == exp_uart_rx_data[i],
          "UART RX data[%0d] mismatched: {act: %x, exp: %x}", i,
          uart_rx_data[i], exp_uart_rx_data[i]);
  }

  // If we reached here, then the test passed.
  return true;
}

const test_config_t kTestConfig;

bool test_main(void) {
  LOG_INFO("UART TX RX test");

  // Initialize the UART.
  mmio_region_t uart_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR);
  uart_init_with_irqs(uart_base_addr, &uart);

  // Initialize the PLIC.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  plic_init_with_irqs(plic_base_addr, &plic);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Execute the test.
  return execute_test(&uart);
}
