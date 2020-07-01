// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package top_earlgrey_pkg;

  // Base addresses of all peripherals.
  parameter TOP_EARLGREY_UART_BASE_ADDR = 32'h40000000;
  parameter TOP_EARLGREY_UART1_BASE_ADDR = 32'h40010000;
  parameter TOP_EARLGREY_UART2_BASE_ADDR = 32'h40020000;
  parameter TOP_EARLGREY_UART3_BASE_ADDR = 32'h40030000;
  parameter TOP_EARLGREY_GPIO_BASE_ADDR = 32'h40040000;
  parameter TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'h40050000;
  parameter TOP_EARLGREY_FLASH_CTRL_BASE_ADDR = 32'h41000000;
  parameter TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'h40100000;
  parameter TOP_EARLGREY_I2C0_BASE_ADDR = 32'h40080000;
  parameter TOP_EARLGREY_I2C1_BASE_ADDR = 32'h40090000;
  parameter TOP_EARLGREY_I2C2_BASE_ADDR = 32'h400A0000;
  parameter TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR = 32'h40110000;
  parameter TOP_EARLGREY_OTP_CTRL_BASE_ADDR = 32'h40130000;
  parameter TOP_EARLGREY_AES_BASE_ADDR = 32'h41100000;
  parameter TOP_EARLGREY_HMAC_BASE_ADDR = 32'h41110000;
  parameter TOP_EARLGREY_KMAC_BASE_ADDR = 32'h41120000;
  parameter TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'h41010000;
  parameter TOP_EARLGREY_PINMUX_AON_BASE_ADDR = 32'h40460000;
  parameter TOP_EARLGREY_PADCTRL_AON_BASE_ADDR = 32'h40470000;
  parameter TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'h41170000;
  parameter TOP_EARLGREY_PWRMGR_AON_BASE_ADDR = 32'h40400000;
  parameter TOP_EARLGREY_RSTMGR_AON_BASE_ADDR = 32'h40410000;
  parameter TOP_EARLGREY_CLKMGR_AON_BASE_ADDR = 32'h40420000;
  parameter TOP_EARLGREY_RBOX_AON_BASE_ADDR = 32'h40430000;
  parameter TOP_EARLGREY_NMI_GEN_BASE_ADDR = 32'h41180000;
  parameter TOP_EARLGREY_USBDEV_AON_BASE_ADDR = 32'h40500000;
  parameter TOP_EARLGREY_PATTGEN_BASE_ADDR = 32'h400E0000;
  parameter TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'h41130000;
  parameter TOP_EARLGREY_CSRNG_BASE_ADDR = 32'h41150000;
  parameter TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR = 32'h41160000;

  // Enumeration for DIO pins.
  typedef enum {
    TopEarlgreyDioPinRboxAonPwrbOut = 0,
    TopEarlgreyDioPinRboxAonKey2Out = 1,
    TopEarlgreyDioPinRboxAonKey1Out = 2,
    TopEarlgreyDioPinRboxAonKey0Out = 3,
    TopEarlgreyDioPinRboxAonFlashWpL = 4,
    TopEarlgreyDioPinRboxAonEcRstL = 5,
    TopEarlgreyDioPinRboxAonEcInRw = 6,
    TopEarlgreyDioPinRboxAonBatEn = 7,
    TopEarlgreyDioPinRboxAonPwrbIn = 8,
    TopEarlgreyDioPinRboxAonKey2In = 9,
    TopEarlgreyDioPinRboxAonKey1In = 10,
    TopEarlgreyDioPinRboxAonKey0In = 11,
    TopEarlgreyDioPinRboxAonEcEnteringRw = 12,
    TopEarlgreyDioPinRboxAonAcPresent = 13,
    TopEarlgreyDioPinUsbdevAonDn = 14,
    TopEarlgreyDioPinUsbdevAonDp = 15,
    TopEarlgreyDioPinUsbdevAonD = 16,
    TopEarlgreyDioPinUsbdevAonSuspend = 17,
    TopEarlgreyDioPinUsbdevAonTxModeSe = 18,
    TopEarlgreyDioPinUsbdevAonDnPullup = 19,
    TopEarlgreyDioPinUsbdevAonDpPullup = 20,
    TopEarlgreyDioPinUsbdevAonSe0 = 21,
    TopEarlgreyDioPinUsbdevAonSense = 22,
    TopEarlgreyDioPinUartTx = 23,
    TopEarlgreyDioPinUartRx = 24,
    TopEarlgreyDioPinSpiDeviceMiso = 25,
    TopEarlgreyDioPinSpiDeviceMosi = 26,
    TopEarlgreyDioPinSpiDeviceCsb = 27,
    TopEarlgreyDioPinSpiDeviceSck = 28,
    TopEarlgreyDioPinCount = 29
  } top_earlgrey_dio_pin_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
