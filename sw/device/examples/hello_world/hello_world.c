// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/examples/demos.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_gpio_t gpio;
static dif_spi_device_t spi;
static dif_spi_device_config_t spi_config;
static dif_uart_t uart;

int main(int argc, char **argv) {
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart));
  CHECK_DIF_OK(
      dif_uart_configure(&uart, (dif_uart_config_t){
                                    .baudrate = kUartBaudrate,
                                    .clk_freq_hz = kClockFreqPeripheralHz,
                                    .parity_enable = kDifToggleDisabled,
                                    .parity = kDifUartParityEven,
                                }));
  base_uart_stdout(&uart);

  pinmux_init();

  CHECK_DIF_OK(dif_spi_device_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi));
  spi_config.clock_polarity = kDifSpiDeviceEdgePositive;
  spi_config.data_phase = kDifSpiDeviceEdgeNegative;
  spi_config.tx_order = kDifSpiDeviceBitOrderMsbToLsb;
  spi_config.rx_order = kDifSpiDeviceBitOrderMsbToLsb;
  spi_config.rx_fifo_timeout = 63;
  spi_config.rx_fifo_len = kDifSpiDeviceBufferLen / 2;
  spi_config.tx_fifo_len = kDifSpiDeviceBufferLen / 2;
  CHECK_DIF_OK(dif_spi_device_configure(&spi, &spi_config));

  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  // Enable GPIO: 0-7 and 16 is input; 8-15 is output.
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, 0x0ff00));

  // Add DATE and TIME because I keep fooling myself with old versions
  LOG_INFO("Hello World!");
  LOG_INFO("Built at: " __DATE__ ", " __TIME__);

  demo_gpio_startup(&gpio);

  // Now have UART <-> Buttons/LEDs demo
  // all LEDs off
  CHECK_DIF_OK(dif_gpio_write_all(&gpio, 0x0000));
  LOG_INFO("Try out the switches on the board");
  LOG_INFO("or type anything into the console window.");
  LOG_INFO("The LEDs show the ASCII code of the last character.");

  CHECK_DIF_OK(dif_spi_device_send(&spi, &spi_config, "SPI!", 4,
                                   /*bytes_sent=*/NULL));

  uint32_t gpio_state = 0;
  while (true) {
    busy_spin_micros(10 * 1000);  // 10 ms
    gpio_state = demo_gpio_to_log_echo(&gpio, gpio_state);
    demo_spi_to_log_echo(&spi, &spi_config);
    demo_uart_to_uart_and_gpio_echo(&uart, &gpio);
  }
}
