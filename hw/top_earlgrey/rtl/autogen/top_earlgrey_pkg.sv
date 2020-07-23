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
  parameter TOP_EARLGREY_SPI_HOST0_BASE_ADDR = 32'h40060000;
  parameter TOP_EARLGREY_SPI_HOST1_BASE_ADDR = 32'h40070000;
  parameter TOP_EARLGREY_FLASH_CTRL_BASE_ADDR = 32'h41000000;
  parameter TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'h40100000;
  parameter TOP_EARLGREY_I2C0_BASE_ADDR = 32'h40080000;
  parameter TOP_EARLGREY_I2C1_BASE_ADDR = 32'h40090000;
  parameter TOP_EARLGREY_I2C2_BASE_ADDR = 32'h400A0000;
  parameter TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR = 32'h40110000;
  parameter TOP_EARLGREY_OTP_CTRL_BASE_ADDR = 32'h40130000;
  parameter TOP_EARLGREY_LIFECYCLE_BASE_ADDR = 32'h40140000;
  parameter TOP_EARLGREY_AES_BASE_ADDR = 32'h41100000;
  parameter TOP_EARLGREY_HMAC_BASE_ADDR = 32'h41110000;
  parameter TOP_EARLGREY_KMAC_BASE_ADDR = 32'h41120000;
  parameter TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'h41010000;
  parameter TOP_EARLGREY_PINMUX_AON_BASE_ADDR = 32'h40460000;
  parameter TOP_EARLGREY_PADCTRL_AON_BASE_ADDR = 32'h40470000;
  parameter TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'h41170000;
  parameter TOP_EARLGREY_PWRMGR_AON_BASE_ADDR = 32'h40400000;
  parameter TOP_EARLGREY_RSTMGR_AON_BASE_ADDR = 32'h40410000;
  parameter TOP_EARLGREY_CLKMGR_AON_BASE_ADDR = 32'h400C0000;
  parameter TOP_EARLGREY_RBOX_AON_BASE_ADDR = 32'h40430000;
  parameter TOP_EARLGREY_DCD_AON_BASE_ADDR = 32'h40440000;
  parameter TOP_EARLGREY_PWM_AON_BASE_ADDR = 32'h40450000;
  parameter TOP_EARLGREY_TIMER_AON_BASE_ADDR = 32'h40480000;
  parameter TOP_EARLGREY_NMI_GEN_BASE_ADDR = 32'h41180000;
  parameter TOP_EARLGREY_USBDEV_AON_BASE_ADDR = 32'h40500000;
  parameter TOP_EARLGREY_PATTGEN_BASE_ADDR = 32'h400E0000;
  parameter TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'h41130000;
  parameter TOP_EARLGREY_CSRNG_BASE_ADDR = 32'h41150000;
  parameter TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR = 32'h41160000;
  parameter TOP_EARLGREY_OTBN_BASE_ADDR = 32'h50000000;

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
    TopEarlgreyDioPinSpiHost0S0 = 9,
TopEarlgreyDioPinSpiHost0S1 = 10,
TopEarlgreyDioPinSpiHost0S2 = 11,
TopEarlgreyDioPinSpiHost0S3 = 12,

    TopEarlgreyDioPinSpiHost0Csb = 13,
    TopEarlgreyDioPinSpiHost0Sck = 14,
    TopEarlgreyDioPinSpiDeviceS0 = 15,
TopEarlgreyDioPinSpiDeviceS1 = 16,
TopEarlgreyDioPinSpiDeviceS2 = 17,
TopEarlgreyDioPinSpiDeviceS3 = 18,

    TopEarlgreyDioPinSpiDeviceCsb = 19,
    TopEarlgreyDioPinSpiDeviceSck = 20,
    TopEarlgreyDioPinCount = 21
  } top_earlgrey_dio_pin_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
