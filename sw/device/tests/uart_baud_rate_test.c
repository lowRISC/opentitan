// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "dt/dt_api.h"
#include "dt/dt_pinmux.h"
#include "dt/dt_uart.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"
#include "sw/device/lib/testing/uart_testutils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint8_t kSendData[] = "UART baud test!";
static const uint32_t kBauds[11] = {4800, 9600, 19200, 38400, 57600, 115200,
                                    230400, 128000, 256000,
                                    // These baud rates will only work on
                                    // silicon, the FPGA cannot go fast enough:
                                    1000000, 1500000};

enum {
  kTestTimeoutMillis = 500000,
};

typedef enum test_phase {
  kTestPhaseInit,
  kTestPhaseCfg,
  kTestPhaseSend,
  kTestPhaseRecv,
  kTestPhaseDone,
} test_phase_t;

static volatile uint8_t test_phase = kTestPhaseInit;
static volatile uint8_t uart_idx = UINT8_MAX;
static volatile uint32_t baud_rate = UINT32_MAX;

static dif_uart_t uart;
static dif_pinmux_t pinmux;

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

// Send all bytes in `kSendData`, and check that they are received via the
// loopback mechanism.
static status_t test_uart_baud(void) {
  test_phase = kTestPhaseCfg;

  TRY(dif_uart_configure(&uart,
                         (dif_uart_config_t){
                             .baudrate = (uint32_t)baud_rate,
                             .clk_freq_hz = dt_clock_frequency(kDtClockIo),
                             .parity_enable = kDifToggleDisabled,
                             .parity = kDifUartParityEven,
                             .tx_enable = kDifToggleEnabled,
                             .rx_enable = kDifToggleEnabled,
                         }));

  TRY(dif_uart_fifo_reset(&uart, kDifUartDatapathAll));

  LOG_INFO("Configured UART%d with Baud rate %d", uart_idx, baud_rate);

  OTTF_WAIT_FOR(test_phase == kTestPhaseSend, kTestTimeoutMillis);

  LOG_INFO("Sending data...");
  TRY(dif_uart_bytes_send(&uart, kSendData, sizeof(kSendData), NULL));
  LOG_INFO("Data sent");

  OTTF_WAIT_FOR(test_phase == kTestPhaseRecv, kTestTimeoutMillis);

  LOG_INFO("Receiving data...");
  uint8_t data[sizeof(kSendData)] = {0};
  for (size_t i = 0; i < sizeof(data); ++i) {
    TRY(dif_uart_byte_receive_polled(&uart, &data[i]));
  }
  TRY_CHECK_ARRAYS_EQ(data, kSendData, sizeof(kSendData));

  test_phase = kTestPhaseDone;

  return OK_STATUS();
}

bool test_main(void) {
  OTTF_WAIT_FOR(uart_idx != 0xff, kTestTimeoutMillis);

  CHECK(kDtUart0 <= uart_idx && uart_idx < kDtUartCount,
        "uart_idx %d out of range", uart_idx);
  CHECK_DIF_OK(dif_uart_init_from_dt((dt_uart_t)uart_idx, &uart));

  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxAon, &pinmux));

  // When UART0 is tested, switch OTTF console to UART1.
  if (uart_idx == 0) {
    CHECK_STATUS_OK(
        uart_testutils_select_pinmux(&pinmux, 1, kUartPinmuxChannelConsole));
    ottf_console_configure_uart(dt_uart_primary_reg_block(kDtUart1));
  }

  CHECK_STATUS_OK(
      uart_testutils_select_pinmux(&pinmux, uart_idx, kUartPinmuxChannelDut));

  // We only want to run the highest bauds (1MBd and 1.5MBd) on chips going
  // at the real speed (24MHz). FPGAs clocking slower cannot test these.
  size_t baud_count = ARRAYSIZE(kBauds);
  if (dt_clock_frequency(kDtClockIo) < 24 * 1000 * 1000) {
    baud_count -= 2;
  }

  // Check every baud rate is sent and received okay.
  status_t result = OK_STATUS();
  for (size_t baud_idx = 0; baud_idx < baud_count; ++baud_idx) {
    baud_rate = kBauds[baud_idx];
    EXECUTE_TEST(result, test_uart_baud);
  }
  return status_ok(result);
}
