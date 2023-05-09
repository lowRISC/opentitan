// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// TODO, remove it once pinout configuration is provided
#include "pinmux_regs.h"

#define UART_DATASET_SIZE 128

static dif_uart_t uart;
static dif_rv_plic_t plic;

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
 * From the software / compiler's perspective, this is a constant (hence the
 * `const` qualifier). However, the external DV testbench finds this symbol's
 * address and modifies it via backdoor, to test a different UART instance with
 * the same test SW image. Hence, we add the `volatile` keyword to prevent the
 * compiler from optimizing it out.
 * The `const` is needed to put it in the .rodata section, otherwise it gets
 * placed in .data section in the main SRAM. We cannot backdoor write anything
 * in SRAM at the start of the test because the CRT init code wipes it to 0s.
 */
static volatile const uint8_t kUartIdx = 0x0;

/**
 * Indicates if ext_clk is used and what speed.
 *
 * Similar to `kUartIdx`, this may be overridden in DV testbench
 */
static volatile const bool kUseExtClk = false;
static volatile const bool kUseLowSpeedSel = false;

// A set of bytes to be send out of TX.
static const uint8_t kUartTxData[UART_DATASET_SIZE] = {
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
static const uint8_t kExpUartRxData[UART_DATASET_SIZE] = {
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

// There are multiple uart instances in the chip. These variables will be
// updated according to the uart we select.
static volatile uint32_t uart_base_addr;
static volatile uint32_t uart_peripheral_id;
static volatile uint32_t uart_irq_tx_watermartk_id;
static volatile uint32_t uart_irq_rx_watermartk_id;
static volatile uint32_t uart_irq_tx_empty_id;
static volatile uint32_t uart_irq_rx_overflow_id;
static volatile uint32_t uart_irq_rx_frame_err_id;
static volatile uint32_t uart_irq_rx_frame_err_id;
static volatile uint32_t uart_irq_rx_break_err_id;
static volatile uint32_t uart_irq_rx_timeout_id;
static volatile uint32_t uart_irq_rx_parity_err_id;

/**
 * Set our expectation & event indications of the interrupts we intend to
 * exercise in this test. These are declared volatile since they are used by the
 * ISR.
 */
static volatile bool exp_uart_irq_tx_watermark;
static volatile bool uart_irq_tx_watermark_fired;
static volatile bool exp_uart_irq_rx_watermark;
static volatile bool uart_irq_rx_watermark_fired;
static volatile bool exp_uart_irq_tx_empty;
static volatile bool uart_irq_tx_empty_fired;
static volatile bool exp_uart_irq_rx_overflow;
static volatile bool uart_irq_rx_overflow_fired;

// Configures the pinmux to connect the UART instance to chip IOs based on the
// ChromeOS pinout configuration.
//
// The pinout configuration is documented here:
// https://github.com/lowRISC/opentitan/blob/master/hw/top_earlgrey/data/top_earlgrey.hjson
// TODO: Pinout configuration APIs based on customer usecases will be
// auto-generated in future. This function is a stop-gap solution until that is
// made available.
static void pinmux_connect_uart_to_pads(uint32_t rx_pin_in_idx,
                                        uint32_t rx_uart_idx,
                                        uint32_t tx_pin_out_idx,
                                        uint32_t tx_uart_idx) {
  mmio_region_t reg32 = mmio_region_from_addr(
      TOP_EARLGREY_PINMUX_AON_BASE_ADDR + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET);
  uint32_t reg_value = rx_pin_in_idx;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  ptrdiff_t reg_offset = (ptrdiff_t)rx_uart_idx << 2;
  uint32_t mask = PINMUX_MIO_PERIPH_INSEL_0_IN_0_MASK;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);

  reg32 = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR +
                                PINMUX_MIO_OUTSEL_0_REG_OFFSET);
  reg_value = tx_uart_idx;
  // We've got one insel configuration field per register. Hence, we have to
  // convert the enumeration index into a byte address using << 2.
  reg_offset = (ptrdiff_t)tx_pin_out_idx << 2;
  mask = PINMUX_MIO_OUTSEL_0_OUT_0_MASK;
  mmio_region_write32(reg32, reg_offset, reg_value & mask);
}

void update_uart_base_addr_and_irq_id(void) {
  switch (kUartIdx) {
    case 0:
      uart_base_addr = TOP_EARLGREY_UART0_BASE_ADDR;
      uart_peripheral_id = kTopEarlgreyPlicPeripheralUart0;
      uart_irq_tx_watermartk_id = kTopEarlgreyPlicIrqIdUart0TxWatermark;
      uart_irq_rx_watermartk_id = kTopEarlgreyPlicIrqIdUart0RxWatermark;
      uart_irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart0TxEmpty;
      uart_irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart0RxOverflow;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart0RxFrameErr;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart0RxFrameErr;
      uart_irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart0RxBreakErr;
      uart_irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart0RxTimeout;
      uart_irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart0RxParityErr;
      break;
    case 1:
      uart_base_addr = TOP_EARLGREY_UART1_BASE_ADDR;
      uart_peripheral_id = kTopEarlgreyPlicPeripheralUart1;
      uart_irq_tx_watermartk_id = kTopEarlgreyPlicIrqIdUart1TxWatermark;
      uart_irq_rx_watermartk_id = kTopEarlgreyPlicIrqIdUart1RxWatermark;
      uart_irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart1TxEmpty;
      uart_irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart1RxOverflow;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart1RxFrameErr;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart1RxFrameErr;
      uart_irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart1RxBreakErr;
      uart_irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart1RxTimeout;
      uart_irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart1RxParityErr;
      break;
    case 2:
      uart_base_addr = TOP_EARLGREY_UART2_BASE_ADDR;
      uart_peripheral_id = kTopEarlgreyPlicPeripheralUart2;
      uart_irq_tx_watermartk_id = kTopEarlgreyPlicIrqIdUart2TxWatermark;
      uart_irq_rx_watermartk_id = kTopEarlgreyPlicIrqIdUart2RxWatermark;
      uart_irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart2TxEmpty;
      uart_irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart2RxOverflow;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart2RxFrameErr;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart2RxFrameErr;
      uart_irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart2RxBreakErr;
      uart_irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart2RxTimeout;
      uart_irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart2RxParityErr;
      break;
    case 3:
      uart_base_addr = TOP_EARLGREY_UART3_BASE_ADDR;
      uart_peripheral_id = kTopEarlgreyPlicPeripheralUart3;
      uart_irq_tx_watermartk_id = kTopEarlgreyPlicIrqIdUart3TxWatermark;
      uart_irq_rx_watermartk_id = kTopEarlgreyPlicIrqIdUart3RxWatermark;
      uart_irq_tx_empty_id = kTopEarlgreyPlicIrqIdUart3TxEmpty;
      uart_irq_rx_overflow_id = kTopEarlgreyPlicIrqIdUart3RxOverflow;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart3RxFrameErr;
      uart_irq_rx_frame_err_id = kTopEarlgreyPlicIrqIdUart3RxFrameErr;
      uart_irq_rx_break_err_id = kTopEarlgreyPlicIrqIdUart3RxBreakErr;
      uart_irq_rx_timeout_id = kTopEarlgreyPlicIrqIdUart3RxTimeout;
      uart_irq_rx_parity_err_id = kTopEarlgreyPlicIrqIdUart3RxParityErr;
      break;
    default:
      LOG_FATAL("Unsupported uart ID %x", kUartIdx);
  }
}
/**
 * Provides external irq handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 */
void ottf_external_isr(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(
      dif_rv_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0, &plic_irq_id));

  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == uart_peripheral_id,
        "Interurpt from unexpected peripheral: %d", peripheral);

  // Correlate the interrupt fired at PLIC with UART.
  dif_uart_irq_t uart_irq;
  if (plic_irq_id == uart_irq_tx_watermartk_id) {
    CHECK(exp_uart_irq_tx_watermark, "Unexpected TX watermark interrupt");
    uart_irq_tx_watermark_fired = true;
    uart_irq = kDifUartIrqTxWatermark;
  } else if (plic_irq_id == uart_irq_rx_watermartk_id) {
    CHECK(exp_uart_irq_rx_watermark, "Unexpected RX watermark interrupt");
    uart_irq_rx_watermark_fired = true;
    uart_irq = kDifUartIrqRxWatermark;
  } else if (plic_irq_id == uart_irq_tx_empty_id) {
    CHECK(exp_uart_irq_tx_empty, "Unexpected TX empty interrupt");
    uart_irq_tx_empty_fired = true;
    uart_irq = kDifUartIrqTxEmpty;
  } else if (plic_irq_id == uart_irq_rx_overflow_id) {
    CHECK(exp_uart_irq_rx_overflow, "Unexpected RX overflow interrupt");
    uart_irq_rx_overflow_fired = true;
    uart_irq = kDifUartIrqRxOverflow;
  } else {
    LOG_ERROR("Unexpected interrupt (at PLIC): %d", plic_irq_id);
    test_status_set(kTestStatusFailed);
    // The `abort()` call below is redundant. It is added to prevent the
    // compilation error due to not initializing the `uart_irq` enum variable
    // above. See issue #2157 for moe details.
    abort();
  }

  // Check if the same interrupt fired at UART as well.
  bool is_pending;
  CHECK_DIF_OK(dif_uart_irq_is_pending(&uart, uart_irq, &is_pending));
  CHECK(is_pending, "UART interrupt fired at PLIC did not fire at UART");

  // Clear the interrupt at UART.
  CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart, uart_irq));

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0,
                                        plic_irq_id));
}

/**
 * Initializes UART and enables the relevant interrupts.
 */
static void uart_init_with_irqs(mmio_region_t base_addr, dif_uart_t *uart) {
  LOG_INFO("Initializing the UART.");

  CHECK_DIF_OK(dif_uart_init(base_addr, uart));
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      uart, (dif_uart_config_t){
                .baudrate = (uint32_t)kUartBaudrate,
                .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                .parity_enable = kDifToggleDisabled,
                .parity = kDifUartParityEven,
                .tx_enable = kDifToggleEnabled,
                .rx_enable = kDifToggleEnabled,
            }));

  // Set the TX and RX watermark to 16 bytes.
  CHECK_DIF_OK(dif_uart_watermark_tx_set(uart, kDifUartWatermarkByte16));
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kDifUartWatermarkByte16));

  // Enable these UART interrupts - TX/TX watermark, TX empty and RX overflow.
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqTxWatermark,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_irq_set_enabled(uart, kDifUartIrqTxEmpty, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_irq_set_enabled(uart, kDifUartIrqRxOverflow, kDifToggleEnabled));
}

/**
 * Initializes PLIC and enables the relevant UART interrupts.
 */
static void plic_init_with_irqs(mmio_region_t base_addr, dif_rv_plic_t *plic) {
  LOG_INFO("Initializing the PLIC. %08x", uart_irq_tx_watermartk_id);

  CHECK_DIF_OK(dif_rv_plic_init(base_addr, plic));

  // Set the priority of UART interrupts at PLIC to be >=1 (so ensure the target
  // does get interrupted).
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, uart_irq_tx_watermartk_id, 0x1));
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, uart_irq_rx_watermartk_id, 0x2));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, uart_irq_tx_empty_id, 0x3));
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, uart_irq_rx_overflow_id, 0x1));
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, uart_irq_rx_frame_err_id, 0x2));
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, uart_irq_rx_break_err_id, 0x3));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(plic, uart_irq_rx_timeout_id, 0x1));
  CHECK_DIF_OK(
      dif_rv_plic_irq_set_priority(plic, uart_irq_rx_parity_err_id, 0x2));

  // Set the threshold for the Ibex to 0.
  CHECK_DIF_OK(
      dif_rv_plic_target_set_threshold(plic, kTopEarlgreyPlicTargetIbex0, 0x0));

  // Enable all UART interrupts at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_tx_watermartk_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_rx_watermartk_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_tx_empty_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_rx_overflow_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_rx_frame_err_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_rx_break_err_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_rx_timeout_id,
                                           kTopEarlgreyPlicTargetIbex0,
                                           kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic, uart_irq_rx_parity_err_id,
                                           kTopEarlgreyPlicTargetIbex0,
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
                                        bool *transfer_done) {
  size_t bytes_remaining = dataset_size - *dataset_index;
  size_t bytes_transferred = 0;
  bool result = false;
  switch (uart_direction) {
    case kUartSend:
      result = dif_uart_bytes_send(uart, &data[*dataset_index], bytes_remaining,
                                   &bytes_transferred) == kDifOk;
      break;
    case kUartReceive:
      result =
          dif_uart_bytes_receive(uart, bytes_remaining, &data[*dataset_index],
                                 &bytes_transferred) == kDifOk;
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

      // Send the remaining kUartTxData as and when the TX watermark fires.
      CHECK(uart_transfer_ongoing_bytes(uart, kUartSend, (uint8_t *)kUartTxData,
                                        UART_DATASET_SIZE,
                                        &uart_tx_bytes_written, &uart_tx_done));

      if (uart_tx_done) {
        // At this point, we have sent the required number of bytes.
        // Expect the TX empty interrupt to fire at some point.
        exp_uart_irq_tx_empty = true;
      }
    }

    if (!uart_rx_done && uart_irq_rx_watermark_fired) {
      uart_irq_rx_watermark_fired = false;

      // When RX watermark fires, read the data, but if remaining items are less
      // than 16, RX watermark won't fire. In that case, keep reading until all
      // item are received.
      do {
        CHECK(uart_transfer_ongoing_bytes(uart, kUartReceive, uart_rx_data,
                                          UART_DATASET_SIZE,
                                          &uart_rx_bytes_read, &uart_rx_done));
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
    CHECK(uart_rx_data[i] == kExpUartRxData[i],
          "UART RX data[%d] mismatched: {act: %x, exp: %x}", i, uart_rx_data[i],
          kExpUartRxData[i]);
  }
}

void config_external_clock(const dif_clkmgr_t *clkmgr) {
  dif_lc_ctrl_t lc;
  mmio_region_t lc_ctrl_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_ctrl_base_addr, &lc));

  LOG_INFO("Read and check LC state.");
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));
  CHECK(curr_state == kDifLcCtrlStateRma,
        "LC State isn't in kDifLcCtrlStateRma!");

  CHECK_STATUS_OK(
      clkmgr_testutils_enable_external_clock_blocking(clkmgr, kUseLowSpeedSel));
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  mmio_region_t clkmgr_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(clkmgr_base_addr, &clkmgr));

  update_uart_base_addr_and_irq_id();

  LOG_INFO("Test UART%d with base_addr: %08x", kUartIdx, uart_base_addr);

  pinmux_connect_uart_to_pads(
      kTopEarlgreyPinmuxInselIoc3, kTopEarlgreyPinmuxPeripheralInUart0Rx,
      kTopEarlgreyPinmuxMioOutIoc4, kTopEarlgreyPinmuxOutselUart0Tx);
  pinmux_connect_uart_to_pads(
      kTopEarlgreyPinmuxInselIob4, kTopEarlgreyPinmuxPeripheralInUart1Rx,
      kTopEarlgreyPinmuxMioOutIob5, kTopEarlgreyPinmuxOutselUart1Tx);
  // TODO: the UARTs below still need to be mapped to the correct location.
  pinmux_connect_uart_to_pads(
      kTopEarlgreyPinmuxInselIoa4, kTopEarlgreyPinmuxPeripheralInUart2Rx,
      kTopEarlgreyPinmuxMioOutIoa5, kTopEarlgreyPinmuxOutselUart2Tx);
  pinmux_connect_uart_to_pads(
      kTopEarlgreyPinmuxInselIoa0, kTopEarlgreyPinmuxPeripheralInUart3Rx,
      kTopEarlgreyPinmuxMioOutIoa1, kTopEarlgreyPinmuxOutselUart3Tx);

  if (kUseExtClk) {
    config_external_clock(&clkmgr);
  }
  CHECK_STATUS_OK(clkmgr_testutils_enable_clock_counts_with_expected_thresholds(
      &clkmgr, /*jitter_enabled=*/false, kUseExtClk, kUseLowSpeedSel));

  // Initialize the UART.
  mmio_region_t chosen_uart_region = mmio_region_from_addr(uart_base_addr);
  uart_init_with_irqs(chosen_uart_region, &uart);

  // Initialize the PLIC.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  plic_init_with_irqs(plic_base_addr, &plic);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Execute the test.
  execute_test(&uart);

  CHECK_STATUS_OK(clkmgr_testutils_check_measurement_counts(&clkmgr));

  return true;
}
