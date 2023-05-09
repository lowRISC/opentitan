// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static const uint8_t kSendData[] = "Smoke test!";

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = false,
                        .console.test_may_clobber = true, );

bool test_main(void) {
  dif_uart_t uart;
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart, (dif_uart_config_t){
                 .baudrate = (uint32_t)kUartBaudrate,
                 .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                 .parity_enable = kDifToggleDisabled,
                 .parity = kDifUartParityEven,
                 .tx_enable = kDifToggleEnabled,
                 .rx_enable = kDifToggleEnabled,
             }));
  CHECK_DIF_OK(
      dif_uart_loopback_set(&uart, kDifUartLoopbackSystem, kDifToggleEnabled));
  CHECK_DIF_OK(dif_uart_fifo_reset(&uart, kDifUartDatapathAll));

  // Send all bytes in `kSendData`, and check that they are received via
  // the loopback mechanism.
  for (int i = 0; i < sizeof(kSendData); ++i) {
    CHECK_DIF_OK(dif_uart_byte_send_polled(&uart, kSendData[i]));

    uint8_t receive_byte;
    CHECK_DIF_OK(dif_uart_byte_receive_polled(&uart, &receive_byte));
    CHECK(receive_byte == kSendData[i]);
  }

  return true;
}
