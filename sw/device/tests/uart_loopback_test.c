// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"
#include "sw/device/lib/testing/uart_testutils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint8_t kSendData[] = "Loopback test!";
static const uint32_t kBaseAddrs[4] = {
    TOP_EARLGREY_UART0_BASE_ADDR,
    TOP_EARLGREY_UART1_BASE_ADDR,
    TOP_EARLGREY_UART2_BASE_ADDR,
    TOP_EARLGREY_UART3_BASE_ADDR,
};
enum {
  kTestTimeoutMicros = 1000000,
};

typedef enum test_phases {
  kTestPhaseCfg,
  kTestPhaseLine,
  kTestPhaseSystem,
  kTestPhaseDone,
} test_phase_t;

static volatile uint8_t uart_idx = 0xff;
static volatile uint8_t test_phase = kTestPhaseCfg;

static dif_uart_t uart;
static dif_pinmux_t pinmux;

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

bool test_main(void) {
  mmio_region_t base_addr;

  // Wait for the testbench to set the `uart_idx`.
  OTTF_WAIT_FOR(uart_idx != 0xff, kTestTimeoutMicros);

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux));

  // If we're testing UART0 we need to move the console to UART1.
  if (uart_idx == 0) {
    CHECK_STATUS_OK(
        uart_testutils_select_pinmux(&pinmux, 1, kUartPinmuxChannelConsole));
    ottf_console_configure_uart(TOP_EARLGREY_UART1_BASE_ADDR);
  }

  // Attach the UART under test to the DUT channel.
  CHECK_STATUS_OK(
      uart_testutils_select_pinmux(&pinmux, uart_idx, kUartPinmuxChannelDut));

  base_addr = mmio_region_from_addr(kBaseAddrs[uart_idx]);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart));

  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                 .parity_enable = kDifToggleDisabled,
                 .parity = kDifUartParityEven,
                 .tx_enable = kDifToggleDisabled,
                 .rx_enable = kDifToggleDisabled,
             }));

  LOG_INFO("UART%d configured", uart_idx);

  // First, enable the line loopback which echoes whatever is received to it.
  // Enable the TX line once it's enabled.
  CHECK_DIF_OK(
      dif_uart_loopback_set(&uart, kDifUartLoopbackLine, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_set_enable(&uart, kDifUartDatapathTx, kDifToggleEnabled));

  CHECK_DIF_OK(dif_uart_fifo_reset(&uart, kDifUartDatapathAll));

  OTTF_WAIT_FOR(test_phase == kTestPhaseLine, kTestTimeoutMicros);
  LOG_INFO("Testing the line loopback");

  // Wait for the line test to be finished before configuring the UART for the
  // system loopback.
  OTTF_WAIT_FOR(test_phase == kTestPhaseSystem, kTestTimeoutMicros);
  LOG_INFO("Testing the system loopback");

  CHECK_DIF_OK(
      dif_uart_loopback_set(&uart, kDifUartLoopbackSystem, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_set_enable(&uart, kDifUartDatapathRx, kDifToggleEnabled));

  CHECK_DIF_OK(dif_uart_fifo_reset(&uart, kDifUartDatapathAll));

  for (int i = 0; i < sizeof(kSendData); ++i) {
    CHECK_DIF_OK(dif_uart_byte_send_polled(&uart, kSendData[i]));

    uint8_t receive_byte;
    CHECK_DIF_OK(dif_uart_byte_receive_polled(&uart, &receive_byte));
    CHECK(kSendData[i] == receive_byte, "expected %c, got %c", kSendData[i],
          receive_byte);
  }

  test_phase = kTestPhaseDone;

  return true;
}
