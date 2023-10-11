// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/devicetables/dt.h"
#include "sw/device/lib/devicetables/dt_uart.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/devicetables/dt_pinmux.h"

static const uint8_t kSendData[] = "Smoke test!";

OTTF_DEFINE_TEST_CONFIG(.enable_concurrency = false,
                        .console.test_may_clobber = true, );

bool test_main(void) {
  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(mmio_region_from_addr(dt_device_reg_addr(
                                   dt_get_device(kDtDeviceTypePinmux, 0), 0)),
                               &pinmux));
  dt_device_t uart0 = dt_get_device(kDtDeviceTypeUart, 0);
  for (uint32_t i = 0; i < kDtUartPinctrlOutputCount; ++i) {
    dt_pinctrl_cfg_t cfg = dt_pinctrl_get_padmux_config(uart0, i);
    if (dt_pinctrl_cfg_is_empty(cfg)) {
      continue;
    }
    dif_pinmux_index_t mux = dt_pinctrl_mux_from_cfg(cfg);
    dif_pinmux_index_t sel = dt_pinctrl_selection_from_cfg(cfg);
    CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, mux, sel));
  }
  for (uint32_t i = 0; i < kDtUartPinctrlInputCount; ++i) {
    dt_pinctrl_cfg_t cfg = dt_pinctrl_get_periphmux_config(uart0, i);
    if (dt_pinctrl_cfg_is_empty(cfg)) {
      continue;
    }
    dif_pinmux_index_t mux = dt_pinctrl_mux_from_cfg(cfg);
    dif_pinmux_index_t sel = dt_pinctrl_selection_from_cfg(cfg);
    CHECK_DIF_OK(dif_pinmux_input_select(&pinmux, mux, sel));
  }

  dif_uart_t uart;
  uint32_t base_addr = dt_device_reg_addr(uart0, 0);
  CHECK_DIF_OK(dif_uart_init(mmio_region_from_addr(base_addr), &uart));
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
