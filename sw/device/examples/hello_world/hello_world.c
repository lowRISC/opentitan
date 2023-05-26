// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_gpio_t gpio;
static dif_pinmux_t pinmux;
static dif_spi_device_handle_t spi;
static dif_uart_t uart;

static dif_pinmux_index_t leds[] = {
    kTopEarlgreyPinmuxMioOutIor10,
    kTopEarlgreyPinmuxMioOutIor11,
    kTopEarlgreyPinmuxMioOutIor12,
    kTopEarlgreyPinmuxMioOutIor13,
};

static dif_pinmux_index_t switches[] = {
    kTopEarlgreyPinmuxInselIob6,
    kTopEarlgreyPinmuxInselIob9,
    kTopEarlgreyPinmuxInselIob10,
    kTopEarlgreyPinmuxInselIor5,
};

void configure_pinmux(void) {
  pinmux_testutils_init(&pinmux);
  // Hook up some LEDs.
  for (size_t i = 0; i < ARRAYSIZE(leds); ++i) {
    dif_pinmux_index_t gpio = kTopEarlgreyPinmuxOutselGpioGpio0 + i;
    CHECK_DIF_OK(dif_pinmux_output_select(&pinmux, leds[i], gpio));
  }
  // Hook up DIP switches.
  for (size_t i = 0; i < ARRAYSIZE(switches); ++i) {
    dif_pinmux_index_t gpio = kTopEarlgreyPinmuxPeripheralInGpioGpio8 + i;
    CHECK_DIF_OK(dif_pinmux_input_select(&pinmux, gpio, switches[i]));
  }
}

void _ottf_main(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  configure_pinmux();

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
  base_uart_stdout(&uart);

  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi));
  dif_spi_device_config_t spi_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModeGeneric,
      .mode_cfg =
          {
              .generic =
                  {
                      .rx_fifo_commit_wait = 63,
                      .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
                      .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
                  },
          },
  };
  CHECK_DIF_OK(dif_spi_device_configure(&spi, spi_config));

  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  // Enable GPIO: 0-3 is output; 8-11 is input.
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, 0xF));

  // Add DATE and TIME because I keep fooling myself with old versions
  LOG_INFO("Hello World!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  demo_gpio_startup(&gpio);

  // Now have UART <-> Buttons/LEDs demo
  // all LEDs off
  CHECK_DIF_OK(dif_gpio_write_all(&gpio, 0x0000));
  LOG_INFO("Try out USERDIP switches 0-thru-3 on the board");
  LOG_INFO("or type anything into the console window.");
  LOG_INFO(
      "The LEDs show the lower nibble of the ASCII code of the last "
      "character.");

  CHECK_DIF_OK(dif_spi_device_send(&spi, "SPI!", 4,
                                   /*bytes_sent=*/NULL));

  uint32_t gpio_state = 0;
  while (true) {
    busy_spin_micros(10 * 1000);  // 10 ms
    gpio_state = demo_gpio_to_log_echo(&gpio, gpio_state);
    demo_spi_to_log_echo(&spi);
    demo_uart_to_uart_and_gpio_echo(&uart, &gpio);
  }
}
