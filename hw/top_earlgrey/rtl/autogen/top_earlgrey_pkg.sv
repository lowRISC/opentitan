// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package top_earlgrey_pkg;

  // Base addresses of all peripherals.
  parameter TOP_EARLGREY_UART_BASE_ADDR = 32'h40000000;
  parameter TOP_EARLGREY_GPIO_BASE_ADDR = 32'h40010000;
  parameter TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'h40020000;
  parameter TOP_EARLGREY_FLASH_CTRL_BASE_ADDR = 32'h40030000;
  parameter TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'h40080000;
  parameter TOP_EARLGREY_I2C_BASE_ADDR = 32'h40050000;
  parameter TOP_EARLGREY_AES_BASE_ADDR = 32'h40110000;
  parameter TOP_EARLGREY_HMAC_BASE_ADDR = 32'h40120000;
  parameter TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'h40090000;
  parameter TOP_EARLGREY_PINMUX_AON_BASE_ADDR = 32'h40070000;
  parameter TOP_EARLGREY_PADCTRL_AON_BASE_ADDR = 32'h40160000;
  parameter TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'h40130000;
  parameter TOP_EARLGREY_PWRMGR_BASE_ADDR = 32'h400A0000;
  parameter TOP_EARLGREY_RSTMGR_BASE_ADDR = 32'h400B0000;
  parameter TOP_EARLGREY_CLKMGR_BASE_ADDR = 32'h400C0000;
  parameter TOP_EARLGREY_NMI_GEN_BASE_ADDR = 32'h40140000;
  parameter TOP_EARLGREY_USBDEV_AON_BASE_ADDR = 32'h40150000;
  parameter TOP_EARLGREY_PATTGEN_BASE_ADDR = 32'h400E0000;
  parameter TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'h40170000;

  // Enumeration for DIO pins.
  typedef enum {
    TopEarlgreyDioPinUsbdevAonDn = 0,
    TopEarlgreyDioPinUsbdevAonDp = 1,
    TopEarlgreyDioPinUsbdevAonD = 2,
    TopEarlgreyDioPinUsbdevAonSuspend = 3,
    TopEarlgreyDioPinUsbdevAonTxModeSe = 4,
    TopEarlgreyDioPinUsbdevAonDnPullup = 5,
    TopEarlgreyDioPinUsbdevAonDpPullup = 6,
    TopEarlgreyDioPinUsbdevAonSe0 = 7,
    TopEarlgreyDioPinUsbdevAonSense = 8,
    TopEarlgreyDioPinUartTx = 9,
    TopEarlgreyDioPinUartRx = 10,
    TopEarlgreyDioPinSpiDeviceMiso = 11,
    TopEarlgreyDioPinSpiDeviceMosi = 12,
    TopEarlgreyDioPinSpiDeviceCsb = 13,
    TopEarlgreyDioPinSpiDeviceSck = 14,
    TopEarlgreyDioPinCount = 15
  } top_earlgrey_dio_pin_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
