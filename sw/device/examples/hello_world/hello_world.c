// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/log.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/check.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_status.h"
#include "sw/device/lib/uart.h"

static dif_gpio_t gpio;
static dif_spi_device_t spi;

int main(int argc, char **argv) {
  uart_init(kUartBaudrate);
  base_set_stdout(uart_stdout);

  pinmux_init();

  mmio_region_t spi_reg = mmio_region_from_addr(0x40020000);
  dif_spi_device_config_t spi_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_fifo_timeout = 63,
      .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
      .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
  };
  CHECK(dif_spi_device_init(spi_reg, &spi_config, &spi) ==
        kDifSpiDeviceResultOk);

  dif_gpio_config_t gpio_config = {
      .base_addr = mmio_region_from_addr(0x40010000),
  };
  CHECK(dif_gpio_init(&gpio_config, &gpio) == kDifGpioOk);
  // Enable GPIO: 0-7 and 16 is input; 8-15 is output.
  CHECK(dif_gpio_output_mode_all_set(&gpio, 0x0ff00) == kDifGpioOk);
  // Add DATE and TIME because I keep fooling myself with old versions
  LOG_INFO("Hello World!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  demo_gpio_startup(&gpio);

  // Now have UART <-> Buttons/LEDs demo
  // all LEDs off
  CHECK(dif_gpio_all_write(&gpio, 0x0000) == kDifGpioOk);
  LOG_INFO("Try out the switches on the board");
  LOG_INFO("or type anything into the console window.");
  LOG_INFO("The LEDs show the ASCII code of the last character.");

  CHECK(dif_spi_device_send(&spi, "SPI!", 4, /*bytes_sent=*/NULL) ==
        kDifSpiDeviceResultOk);

  uint32_t gpio_state = 0;
  while (true) {
    usleep(10 * 1000);  // 10 ms
    gpio_state = demo_gpio_to_log_echo(&gpio, gpio_state);
    demo_spi_to_log_echo(&spi);
    demo_uart_to_uart_and_gpio_echo(&gpio);
  }
}
