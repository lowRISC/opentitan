// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_api.h"      // Generated
#include "dt/dt_pinmux.h"   // Generated
#include "dt/dt_rv_plic.h"  // Generated
#include "dt/dt_uart.h"     // Generated
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/uart_testutils.h"

static dif_pinmux_t pinmux;
static dif_rv_plic_t rv_plic;
static dif_uart_t uart;
static dt_uart_t uart_dt;

// Parameters of the test to be set at the beginning.
// Parity settings are:
// - 0 => Odd
// - 1 => Even
// - 2 => Disabled
static volatile uint8_t parity = UINT8_MAX;
static volatile uint8_t uart_idx = UINT8_MAX;

static const uint32_t kPlicTarget = 0;

// Whether we expect and have received the RX parity error interrupt.
static volatile bool uart_irq_rx_parity_err_expected = false;
static volatile bool uart_irq_rx_parity_err_fired = false;
// Whether we expect and have received the RX line break error interrupt.
static volatile bool uart_irq_rx_break_err_expected = false;
static volatile bool uart_irq_rx_break_err_fired = false;

enum {
  // Timeout for ujson commands.
  kCommandTimeoutMicros = 5 * 1000 * 1000,
  // Timeout for a parity error to be received.
  kParityErrTimeoutMicros = 1 * 1000 * 1000,
};

typedef enum test_phase {
  kTestPhaseCfg,
  kTestPhaseSend,
  kTestPhaseRecv,
  kTestPhaseRecvErr,
  kTestPhaseBreakErr,
  kTestPhaseBreakErrDone,
} test_phase_t;
static volatile uint8_t test_phase = kTestPhaseCfg;

// Some random bytes that will be sent and received to check the parity.
static const uint8_t kUartData[32] = {
    0x3f, 0x39, 0xb0, 0x4e, 0xa6, 0xce, 0xe5, 0xb7, 0x94, 0x48, 0xec,
    0xb5, 0x48, 0x5c, 0x08, 0x5b, 0xcd, 0x47, 0xae, 0x80, 0xbb, 0x49,
    0xa1, 0x7c, 0x39, 0x20, 0xd1, 0x6d, 0x2f, 0x4f, 0x94, 0xd8,
};

// Configure the `rx_parity_err` and `rx_break_err` interrupts for the UART
// under test.
static status_t configure_interrupts(void) {
  TRY(dif_uart_irq_disable_all(&uart, NULL));

  TRY(dif_uart_irq_set_enabled(&uart, kDifUartIrqRxParityErr,
                               kDifToggleEnabled));
  TRY(dif_uart_irq_set_enabled(&uart, kDifUartIrqRxBreakErr,
                               kDifToggleEnabled));

  TRY(dif_rv_plic_irq_set_priority(
      &rv_plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxParityErr), 0x1));
  TRY(dif_rv_plic_irq_set_priority(
      &rv_plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxBreakErr), 0x1));

  TRY(dif_rv_plic_irq_set_enabled(
      &rv_plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxParityErr),
      kPlicTarget, kDifToggleEnabled));
  TRY(dif_rv_plic_irq_set_enabled(
      &rv_plic, dt_uart_irq_to_plic_id(uart_dt, kDtUartIrqRxBreakErr),
      kPlicTarget, kDifToggleEnabled));

  TRY(dif_rv_plic_target_set_threshold(&rv_plic, kPlicTarget, 0x0));

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}

// This function overrides the default OTTF external ISR.
//
// It handles the `rx_parity_err` and `rx_break_err` interrupts and checks they
// came from the correct UART. If the interrupts were expected, we let the main
// thread know that they were triggered.
void ottf_external_isr(uint32_t *exc_info) {
  // Claim the interrupt.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&rv_plic, kPlicTarget, &plic_irq_id));

  // Check the interrupt fired on the correct UART.
  dt_instance_id_t peripheral = dt_plic_id_to_instance_id(plic_irq_id);

  // Handle interrupts for the console UART separately.
  if (peripheral != dt_uart_instance_id(uart_dt)) {
    ottf_console_flow_control_isr(exc_info);
  }

  // Check it was the parity error that fired and that we expected it.
  uint32_t uart_irq_id = dt_uart_irq_from_plic_id(uart_dt, plic_irq_id);
  if (uart_irq_id == kDifUartIrqRxParityErr) {
    CHECK(uart_irq_rx_parity_err_expected, "Unexpected parity error interrupt");
    uart_irq_rx_parity_err_fired = true;
  } else if (uart_irq_id == kDifUartIrqRxBreakErr) {
    CHECK(uart_irq_rx_break_err_expected, "Unexpected break error interrupt");
    uart_irq_rx_break_err_fired = true;
  } else {
    CHECK(false, "Unexpected interrupt from UART: %d", plic_irq_id);
  }

  // Check that the same interrupt fired at the UART as well.
  bool is_pending;
  CHECK_DIF_OK(dif_uart_irq_is_pending(&uart, uart_irq_id, &is_pending));
  CHECK(is_pending, "UART interrupt fired at PLIC did not fire at UART");

  // Acknowledge interrupt.
  CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart, uart_irq_id));
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, kPlicTarget, plic_irq_id));
}

// Body of the test:
// 1. Send some data and have the host check its parity.
// 2. Receive some data with the correct parity and check it.
// 3. Receive some data with the wrong parity and check the interrupt fired.
// 4. Wait for the host to trigger a line break error.
static status_t execute_test(void) {
  // Wait for host to sync and then send the expected bytes.
  OTTF_WAIT_FOR(test_phase == kTestPhaseSend, kCommandTimeoutMicros);

  size_t bytes_to_send = ARRAYSIZE(kUartData);
  uint8_t *send_buf = (uint8_t *)kUartData;

  LOG_INFO("Sending data...");
  while (bytes_to_send > 0) {
    size_t bytes_sent = 0;
    TRY(dif_uart_bytes_send(&uart, send_buf, bytes_to_send, &bytes_sent));
    bytes_to_send -= bytes_sent;
    send_buf += bytes_sent;
  }

  // Wait for the host to sync and try receive the expected bytes.
  OTTF_WAIT_FOR(test_phase == kTestPhaseRecv, kCommandTimeoutMicros);

  size_t bytes_to_recv = ARRAYSIZE(kUartData);
  uint8_t recv_buf[ARRAYSIZE(kUartData)] = {0};
  uint8_t *recv_ptr = recv_buf;

  LOG_INFO("Receiving data with correct parity...");
  while (bytes_to_recv > 0) {
    size_t len = 0;
    TRY(dif_uart_bytes_receive(&uart, bytes_to_recv, recv_ptr, &len));
    bytes_to_recv -= len;
    recv_ptr += len;
  }

  TRY_CHECK_ARRAYS_EQ(recv_buf, kUartData, ARRAYSIZE(kUartData));

  // Only expect a parity error if parity was enabled.
  if (parity < 2) {
    // Wait for host to sync and then receive data but now expecting the parity
    // error interrupt to trigger.
    uart_irq_rx_parity_err_expected = true;
    OTTF_WAIT_FOR(test_phase == kTestPhaseRecvErr, kCommandTimeoutMicros);

    LOG_INFO("Receiving data with wrong parity");
    ATOMIC_WAIT_FOR_INTERRUPT(uart_irq_rx_parity_err_fired);
  }

  // We test the RX line break error interrupt at all supported levels.
  dif_uart_rx_break_level_t break_levels[4] = {
      kDifUartRxBreakLevel2,
      kDifUartRxBreakLevel4,
      kDifUartRxBreakLevel8,
      kDifUartRxBreakLevel16,
  };

  for (int i = 0; i < ARRAYSIZE(break_levels); i++) {
    TRY(dif_uart_rx_break_level_set(&uart, break_levels[i]));

    // Wait for host to sync and then expect to receive a line break.
    uart_irq_rx_break_err_expected = true;
    OTTF_WAIT_FOR(test_phase == kTestPhaseBreakErr, kCommandTimeoutMicros);

    LOG_INFO("Waiting for line break");
    ATOMIC_WAIT_FOR_INTERRUPT(uart_irq_rx_break_err_fired);

    test_phase = kTestPhaseBreakErrDone;
  }

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

bool test_main(void) {
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxAon, &pinmux));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &rv_plic));

  // Wait for host to tell us which parity and UART to test.
  OTTF_WAIT_FOR(uart_idx != UINT8_MAX && parity != UINT8_MAX,
                kCommandTimeoutMicros);

  CHECK(kDtUart0 <= uart_idx && uart_idx < kDtUartCount,
        "uart_idx %d out of range", uart_idx);
  uart_dt = (dt_uart_t)uart_idx;
  CHECK_DIF_OK(dif_uart_init_from_dt(uart_dt, &uart));

  // If we're testing UART0 we need to move the console to UART1.
  if (uart_idx == 0) {
    CHECK_STATUS_OK(
        uart_testutils_select_pinmux(&pinmux, 1, kUartPinmuxChannelConsole));
    ottf_console_configure_uart(TOP_EARLGREY_UART1_BASE_ADDR);
  }

  CHECK_STATUS_OK(
      uart_testutils_select_pinmux(&pinmux, uart_idx, kUartPinmuxChannelDut));

  dif_toggle_t parity_enable =
      parity < 2 ? kDifToggleEnabled : kDifToggleDisabled;
  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = dt_clock_frequency(kDtClockIo),
                 .parity_enable = parity_enable,
                 .parity = parity,
                 .tx_enable = kDifToggleDisabled,
                 .rx_enable = kDifToggleDisabled,
             }));

  CHECK_DIF_OK(dif_uart_fifo_reset(&uart, kDifUartDatapathAll));
  CHECK_DIF_OK(
      dif_uart_set_enable(&uart, kDifUartDatapathAll, kDifToggleEnabled));

  CHECK_STATUS_OK(configure_interrupts());

  LOG_INFO("UART%d configured", uart_idx);

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, execute_test);
  return status_ok(result);
}
