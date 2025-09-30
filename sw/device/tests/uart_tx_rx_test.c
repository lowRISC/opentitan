// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/lc_ctrl.h"
#include "hw/top/dt/uart.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/uart_testutils.h"

#define UART_DATASET_SIZE 64

static dif_clkmgr_t clkmgr;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;
static dif_uart_t uart;

static_assert(kDtUartCount >= 2, "This test needs at least 2 UART instance");

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

/**
 * Indicates the UART instance under test.
 *
 * When running in `dv_sim`, the external DV testbench finds this symbol's
 * address and modifies it via backdoor, to test a different UART instance with
 * the same test SW image. Hence, we add the `volatile` keyword to prevent the
 * compiler from optimizing it out.
 *
 * The `const` is needed to put it in the .rodata section, otherwise it gets
 * placed in .data section in the main SRAM. We cannot backdoor write anything
 * in SRAM at the start of the test because the CRT init code wipes it to 0s.
 */
OTTF_BACKDOOR_VAR_DV uint8_t kUartIdxDv = 0xff;
/**
 * Outside of DV simulation environments, the `kUartIdx` symbol needs to be
 * _non_ `const` so that we can modify it via OTTF commands. `kUartIdx` is used
 * as the source of truth in the test but we copy the value from `kUartIdxDv`
 * to here if it has been set.
 */
static volatile uint8_t kUartIdx = 0xff;

/**
 * Indicates the baud rate of the UART under test; this is set within the
 * `dv_sim` environment but the override is not used on physical hardware.
 */
OTTF_BACKDOOR_VAR_DV uint64_t kUartBaudrateDV = 0u;
/**
 * Indicates the clock frequency of the UART under test; this is set within
 * the `dv_sim` environment but the override is not used on physical hardware.
 */
OTTF_BACKDOOR_VAR_DV uint64_t kUartClockFreqHzDV = 0u;

/**
 * Indicates if ext_clk is used and what speed.
 *
 * Similar to `kUartIdx`, this may be overridden in DV testbench
 */
static volatile const bool kUseExtClk = false;
static volatile const bool kUseLowSpeedSel = false;

// A set of bytes to be send out of TX.
//
// The first byte must be FF so we can differentiate this blob from ASCII sent
// by the ROM when it starts. FF is not UTF-8 / ASCII.
static volatile const uint8_t kUartTxData[UART_DATASET_SIZE] = {
    0xff, 0x50, 0xc6, 0xb4, 0xbe, 0x16, 0xed, 0x55, 0x16, 0x1d, 0xe6,
    0x1c, 0xde, 0x9f, 0xfd, 0x24, 0x89, 0x81, 0x4d, 0x0d, 0x1a, 0x12,
    0x4f, 0x57, 0xea, 0xd6, 0x6f, 0xc0, 0x7d, 0x46, 0xe7, 0x37, 0x81,
    0xd3, 0x8e, 0x16, 0xad, 0x7b, 0xd0, 0xe2, 0x4f, 0xff, 0x39, 0xe6,
    0x71, 0x3c, 0x82, 0x04, 0xec, 0x3a, 0x27, 0xcc, 0x3d, 0x58, 0x0e,
    0x56, 0xd2, 0xd2, 0xb9, 0xa3, 0xb5, 0x3d, 0xc0, 0x40,
};

// The set of bytes expected to be received over RX.
static volatile const uint8_t kExpUartRxData[UART_DATASET_SIZE] = {
    0x1b, 0x95, 0xc5, 0xb5, 0x8a, 0xa4, 0xa8, 0x9f, 0x6a, 0x7d, 0x6b,
    0x0c, 0xcd, 0xd5, 0xa6, 0x8f, 0x07, 0x3a, 0x9e, 0x82, 0xe6, 0xa2,
    0x2b, 0xe0, 0x0c, 0x30, 0xe8, 0x5a, 0x05, 0x14, 0x79, 0x8a, 0xFf,
    0x88, 0x29, 0xda, 0xc8, 0xdd, 0x82, 0xd5, 0x68, 0xa5, 0x9d, 0x5a,
    0x48, 0x02, 0x7f, 0x24, 0x32, 0xaf, 0x9d, 0xca, 0xa7, 0x06, 0x0c,
    0x96, 0x65, 0x18, 0xe4, 0x7f, 0x26, 0x44, 0xf3, 0x14,
};

// There are multiple uart instances in the chip. These variables will be
// updated according to the uart we select.
static dt_uart_t uart_dt;

static const uint32_t kPlicTarget = 0;

/**
 * Set our expectation & event indications of the interrupts we intend to
 * exercise in this test. These are declared volatile since they are used by the
 * ISR.
 */
static volatile bool exp_uart_irq_tx_watermark;
static volatile bool uart_irq_tx_watermark_fired;
static volatile bool exp_uart_irq_tx_empty;
static volatile bool uart_irq_tx_empty_fired;
static volatile bool exp_uart_irq_rx_watermark;
static volatile bool uart_irq_rx_watermark_fired;
static volatile bool exp_uart_irq_tx_done;
static volatile bool uart_irq_tx_done_fired;
static volatile bool exp_uart_irq_rx_overflow;
static volatile bool uart_irq_rx_overflow_fired;

enum {
  kCommandTimeout = 5000000,  // microseconds
};

/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default OTTF IRQ handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t plic_irq_id) {
  // Check if it is the right peripheral.
  if (devid != dt_uart_instance_id(uart_dt)) {
    return false;
  }

  // Correlate the interrupt fired at PLIC with UART.
  dt_uart_irq_t uart_irq = dt_uart_irq_from_plic_id(uart_dt, plic_irq_id);
  dif_uart_irq_t dif_uart_irq;

  switch (uart_irq) {
    case kDtUartIrqTxWatermark:
      CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart, kDifUartIrqTxWatermark,
                                            kDifToggleDisabled));
      CHECK(exp_uart_irq_tx_watermark, "Unexpected TX watermark interrupt");
      uart_irq_tx_watermark_fired = true;
      dif_uart_irq = kDifUartIrqTxWatermark;
      break;
    case kDtUartIrqTxEmpty:
      CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart, kDifUartIrqTxEmpty,
                                            kDifToggleDisabled));
      CHECK(exp_uart_irq_tx_empty, "Unexpected TX empty interrupt");
      uart_irq_tx_empty_fired = true;
      dif_uart_irq = kDifUartIrqTxEmpty;
      break;
    case kDtUartIrqRxWatermark:
      CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart, kDifUartIrqRxWatermark,
                                            kDifToggleDisabled));
      CHECK(exp_uart_irq_rx_watermark, "Unexpected RX watermark interrupt");
      uart_irq_rx_watermark_fired = true;
      dif_uart_irq = kDifUartIrqRxWatermark;
      break;
    case kDtUartIrqTxDone:
      CHECK(exp_uart_irq_tx_done, "Unexpected TX done interrupt");
      uart_irq_tx_done_fired = true;
      dif_uart_irq = kDifUartIrqTxDone;
      break;
    case kDtUartIrqRxOverflow:
      CHECK(exp_uart_irq_rx_overflow, "Unexpected RX overflow interrupt");
      uart_irq_rx_overflow_fired = true;
      dif_uart_irq = kDifUartIrqRxOverflow;
      break;
    default:
      LOG_ERROR("Unexpected interrupt (at PLIC): %d", plic_irq_id);
      test_status_set(kTestStatusFailed);
      return false;
  }

  // Check if the same interrupt fired at UART as well.
  bool is_pending;
  CHECK_DIF_OK(dif_uart_irq_is_pending(&uart, dif_uart_irq, &is_pending));
  CHECK(is_pending, "UART interrupt fired at PLIC did not fire at UART");

  // Clear the interrupt at UART.
  CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart, dif_uart_irq));

  return true;
}

/**
 * Initializes UART and enables the relevant interrupts.
 */
static void uart_init_with_irqs(dt_uart_t uart_dt, dif_uart_t *uart,
                                uint32_t uartBaudrate, uint32_t uartFreqHz) {
  LOG_INFO("Initializing the UART.");

  CHECK_DIF_OK(dif_uart_init_from_dt(uart_dt, uart));
  CHECK_DIF_OK(dif_uart_configure(uart, (dif_uart_config_t){
                                            .baudrate = (uint32_t)uartBaudrate,
                                            .clk_freq_hz = (uint32_t)uartFreqHz,
                                            .parity_enable = kDifToggleDisabled,
                                            .parity = kDifUartParityEven,
                                            .tx_enable = kDifToggleEnabled,
                                            .rx_enable = kDifToggleEnabled,
                                        }));

  // Set the TX and RX watermark to 16 bytes.
  CHECK_DIF_OK(dif_uart_watermark_tx_set(uart, kDifUartWatermarkByte16));
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kDifUartWatermarkByte16));

  // Enable these UART interrupts - RX watermark, TX empty and RX overflow.
  // TX watermark is enabled once the TX buffer has been written (otherwise it
  // will fire immediately).
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_irq_set_enabled(uart, kDifUartIrqTxDone, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_irq_set_enabled(uart, kDifUartIrqRxOverflow, kDifToggleEnabled));
}

/**
 * Initializes PLIC and enables the relevant UART interrupts.
 */
static void plic_init_with_irqs(dt_uart_t uart_dt, dif_rv_plic_t *plic) {
  LOG_INFO("Initializing the PLIC.");

  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, plic));

  // Set the priority of UART interrupts at PLIC to be >=1 (so ensure the target
  // does get interrupted).
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxWatermark), 0x1));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxEmpty), 0x1));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxWatermark), 0x2));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxDone), 0x3));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxOverflow), 0x1));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxFrameErr), 0x2));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxBreakErr), 0x3));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxTimeout), 0x1));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxParityErr), 0x2));

  // Set the threshold for the Ibex to 0.
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(plic, kPlicTarget, 0x0));

  // Enable all UART interrupts at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxWatermark), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxEmpty), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxWatermark), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqTxDone), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxOverflow), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxFrameErr), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxBreakErr), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxTimeout), kPlicTarget,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxParityErr), kPlicTarget,
      kDifToggleEnabled));
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
                                        size_t max_xfer_size,
                                        bool *transfer_done) {
  size_t bytes_remaining = dataset_size - *dataset_index;
  size_t bytes_to_xfer =
      max_xfer_size < bytes_remaining ? max_xfer_size : bytes_remaining;
  size_t bytes_transferred = 0;
  bool result = false;
  switch (uart_direction) {
    case kUartSend:
      result = dif_uart_bytes_send(uart, &data[*dataset_index], bytes_to_xfer,
                                   &bytes_transferred) == kDifOk;

      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqTxWatermark,
                                            kDifToggleEnabled));
      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqTxEmpty,
                                            kDifToggleEnabled));
      break;
    case kUartReceive:
      result =
          dif_uart_bytes_receive(uart, bytes_to_xfer, &data[*dataset_index],
                                 &bytes_transferred) == kDifOk;

      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                            kDifToggleEnabled));
      break;
    default:
      LOG_FATAL("Invalid UART data transfer direction!");
  }
  *dataset_index += bytes_transferred;
  *transfer_done = *dataset_index == dataset_size;
  return result;
}

static void execute_test(const dif_uart_t *uart) {
  bool uart_tx_done = false;
  size_t uart_tx_bytes_written = 0;
  exp_uart_irq_tx_watermark = true;
  exp_uart_irq_tx_empty = true;
  // Set the flag below to true to allow TX data to be sent the first time in
  // the if condition below. Subsequently, TX watermark interrupt will trigger
  // more data to be sent.
  uart_irq_tx_watermark_fired = true;
  exp_uart_irq_tx_done = false;
  uart_irq_tx_done_fired = false;

  bool uart_rx_done = false;
  size_t uart_rx_bytes_read = 0;
  exp_uart_irq_rx_watermark = true;
  // Set the flag below to true to allow RX data to be received the first time
  // in the if condition below. Subsequently, RX watermark interrupt will
  // trigger more data to be received.
  uart_irq_rx_watermark_fired = true;
  exp_uart_irq_rx_overflow = false;
  uart_irq_rx_overflow_fired = false;

  // A set of bytes actually received over RX.
  uint8_t uart_rx_data[UART_DATASET_SIZE];

  LOG_INFO("Executing the test.");
  while (!uart_tx_done || !uart_rx_done || !uart_irq_tx_done_fired ||
         !uart_irq_rx_overflow_fired) {
    if (!uart_tx_done && uart_irq_tx_watermark_fired) {
      uart_irq_tx_watermark_fired = false;

      // Send the remaining kUartTxData as and when the TX watermark fires.
      // Intentionally limit the transfer size to 32 bytes at a time. This means
      // we see multiple TX watermark interrupts in the test.
      CHECK(uart_transfer_ongoing_bytes(
          uart, kUartSend, (uint8_t *)kUartTxData, UART_DATASET_SIZE,
          &uart_tx_bytes_written, 32, &uart_tx_done));

      if (uart_tx_done) {
        // At this point, we have sent the required number of bytes.
        // Expect the TX empty interrupt to fire at some point.
        exp_uart_irq_tx_done = true;
      }
    }

    if (!uart_rx_done && uart_irq_rx_watermark_fired) {
      uart_irq_rx_watermark_fired = false;

      // When RX watermark fires, read the data, but if remaining items are less
      // than 16, RX watermark won't fire. In that case, keep reading until all
      // item are received.
      do {
        CHECK(uart_transfer_ongoing_bytes(
            uart, kUartReceive, uart_rx_data, UART_DATASET_SIZE,
            &uart_rx_bytes_read, UART_DATASET_SIZE, &uart_rx_done));
      } while (!uart_rx_done && (UART_DATASET_SIZE - uart_rx_bytes_read < 16));

      if (uart_rx_done) {
        exp_uart_irq_rx_watermark = false;
        // At this point we have received the required number of bytes.
        // We disable the RX watermark interrupt and let the fifo
        // overflow by dropping all future incoming data.
        CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                              kDifToggleDisabled));
        // Expect the RX overflow interrupt to fire at some point.
        exp_uart_irq_rx_overflow = true;
      }
    }

    if (uart_irq_tx_done_fired) {
      exp_uart_irq_tx_watermark = false;
      exp_uart_irq_tx_empty = false;
      exp_uart_irq_tx_done = false;
      // To reach this point the TX empty interrupt must have fired
      CHECK(uart_irq_tx_empty_fired == true, "TX empty interrupt did not fire");
    }

    if (uart_irq_rx_overflow_fired) {
      exp_uart_irq_rx_overflow = false;
    }

    // Wait for the next interrupt to arrive.
    // This check here is necessary as rx interrupts may sometimes occur ahead
    // of tx interrupts.  When this happens, the tx handling code above is not
    // triggered and as a result an unexpected tx_done interrupt is fired
    // later.
    if (!uart_irq_rx_watermark_fired && !uart_irq_tx_watermark_fired &&
        !uart_irq_rx_overflow_fired) {
      wait_for_interrupt();
    }
  }

  // Check data consistency.
  LOG_INFO("Checking the received UART RX data for consistency.");
  for (int i = 0; i < UART_DATASET_SIZE; ++i) {
    CHECK(uart_rx_data[i] == kExpUartRxData[i],
          "UART RX data[%d] mismatched: {act: %x, exp: %x}", i, uart_rx_data[i],
          kExpUartRxData[i]);
  }
}

void config_external_clock(const dif_clkmgr_t *clkmgr) {
  dif_lc_ctrl_t lc;
  CHECK_DIF_OK(dif_lc_ctrl_init_from_dt(kDtLcCtrl, &lc));

  LOG_INFO("Read and check LC state.");
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));
  CHECK(curr_state == kDifLcCtrlStateRma || curr_state == kDifLcCtrlStateDev,
        "LC State isn't in {kDifLcCtrlStateRma, kDifLcCtrlStateDev}!");

  CHECK_STATUS_OK(
      clkmgr_testutils_enable_external_clock_blocking(clkmgr, kUseLowSpeedSel));
}

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

bool test_main(void) {
  CHECK_DIF_OK(dif_clkmgr_init_from_dt(kDtClkmgrAon, &clkmgr));
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxAon, &pinmux));

  if (kUartIdxDv != 0xff) {
    kUartIdx = kUartIdxDv;
  } else {
    OTTF_WAIT_FOR(kUartIdx != 0xff, kCommandTimeout);
  }

  // Use the default UART baud rate and clock frequency for the target device.
  uint64_t uartBaudrate = kUartBaudrate;
  uint64_t uartFreqHz = kClockFreqPeripheralHz;

  // Collect the target baud rate and the clock frequency of the UART
  // peripheral, since the `sim_dv` environment may have modified these for
  // more extensive testing.
  if (kUartBaudrateDV) {
    uartBaudrate = kUartBaudrateDV;
  }
  if (kUartClockFreqHzDV) {
    uartFreqHz = kUartClockFreqHzDV;
  }
  CHECK(uartBaudrate <= UINT32_MAX, "uartBaudrate must fit in uint32_t");
  CHECK(uartFreqHz <= UINT32_MAX, "uartFreqHz must fit in uint32_t");

  // Convert UART index to DT instance
  CHECK(kUartIdx < kDtUartCount, "UART index out of bounds");
  uart_dt = (dt_uart_t)kUartIdx;

  // If we're testing UART0 we need to move the console to UART1.
  if (kUartIdx == 0 && kDeviceType != kDeviceSimDV) {
    CHECK_STATUS_OK(
        uart_testutils_select_pinmux(&pinmux, 1, kUartPinmuxChannelConsole));
    ottf_console_configure_uart(ottf_console_get(),
                                dt_uart_primary_reg_block(kDtUart1));
  }

  LOG_INFO("Test UART%d", kUartIdx);

  // Attach the UART under test.
  CHECK_STATUS_OK(
      uart_testutils_select_pinmux(&pinmux, kUartIdx, kUartPinmuxChannelDut));

  if (kUseExtClk) {
    config_external_clock(&clkmgr);
  }
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, kUseExtClk, kUseLowSpeedSel));

  // Initialize the UART.
  uart_init_with_irqs(uart_dt, &uart, (uint32_t)uartBaudrate,
                      (uint32_t)uartFreqHz);

  // Initialize the PLIC.
  plic_init_with_irqs(uart_dt, &plic);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Execute the test.
  execute_test(&uart);
  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));

  return true;
}
