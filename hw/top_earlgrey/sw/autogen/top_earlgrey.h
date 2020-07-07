// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_

#define PINMUX_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO 32
#define NUM_DIO 29

#define PINMUX_GPIO_GPIO_0_IN 0
#define PINMUX_GPIO_GPIO_1_IN 1
#define PINMUX_GPIO_GPIO_2_IN 2
#define PINMUX_GPIO_GPIO_3_IN 3
#define PINMUX_GPIO_GPIO_4_IN 4
#define PINMUX_GPIO_GPIO_5_IN 5
#define PINMUX_GPIO_GPIO_6_IN 6
#define PINMUX_GPIO_GPIO_7_IN 7
#define PINMUX_GPIO_GPIO_8_IN 8
#define PINMUX_GPIO_GPIO_9_IN 9
#define PINMUX_GPIO_GPIO_10_IN 10
#define PINMUX_GPIO_GPIO_11_IN 11
#define PINMUX_GPIO_GPIO_12_IN 12
#define PINMUX_GPIO_GPIO_13_IN 13
#define PINMUX_GPIO_GPIO_14_IN 14
#define PINMUX_GPIO_GPIO_15_IN 15
#define PINMUX_GPIO_GPIO_16_IN 16
#define PINMUX_GPIO_GPIO_17_IN 17
#define PINMUX_GPIO_GPIO_18_IN 18
#define PINMUX_GPIO_GPIO_19_IN 19
#define PINMUX_GPIO_GPIO_20_IN 20
#define PINMUX_GPIO_GPIO_21_IN 21
#define PINMUX_GPIO_GPIO_22_IN 22
#define PINMUX_GPIO_GPIO_23_IN 23
#define PINMUX_GPIO_GPIO_24_IN 24
#define PINMUX_GPIO_GPIO_25_IN 25
#define PINMUX_GPIO_GPIO_26_IN 26
#define PINMUX_GPIO_GPIO_27_IN 27
#define PINMUX_GPIO_GPIO_28_IN 28
#define PINMUX_GPIO_GPIO_29_IN 29
#define PINMUX_GPIO_GPIO_30_IN 30
#define PINMUX_GPIO_GPIO_31_IN 31
#define PINMUX_I2C0_SDA_IN 33
#define PINMUX_I2C0_SCL_IN 34
#define PINMUX_I2C1_SDA_IN 35
#define PINMUX_I2C1_SCL_IN 36
#define PINMUX_I2C2_SDA_IN 37
#define PINMUX_I2C2_SCL_IN 38
#define PINMUX_UART1_RX_IN 39
#define PINMUX_UART2_RX_IN 40
#define PINMUX_UART3_RX_IN 41

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

// PERIPH_OUTSEL ranges from 0 to NUM_MIO + 3 -1}
// 0, 1 and 2 are tied to value 0, 1 and high-impedance

#define PINMUX_VALUE_0_OUT 0
#define PINMUX_VALUE_1_OUT 1
#define PINMUX_VALUE_Z_OUT 2
#define PINMUX_GPIO_GPIO_0_OUT 3
#define PINMUX_GPIO_GPIO_1_OUT 4
#define PINMUX_GPIO_GPIO_2_OUT 5
#define PINMUX_GPIO_GPIO_3_OUT 6
#define PINMUX_GPIO_GPIO_4_OUT 7
#define PINMUX_GPIO_GPIO_5_OUT 8
#define PINMUX_GPIO_GPIO_6_OUT 9
#define PINMUX_GPIO_GPIO_7_OUT 10
#define PINMUX_GPIO_GPIO_8_OUT 11
#define PINMUX_GPIO_GPIO_9_OUT 12
#define PINMUX_GPIO_GPIO_10_OUT 13
#define PINMUX_GPIO_GPIO_11_OUT 14
#define PINMUX_GPIO_GPIO_12_OUT 15
#define PINMUX_GPIO_GPIO_13_OUT 16
#define PINMUX_GPIO_GPIO_14_OUT 17
#define PINMUX_GPIO_GPIO_15_OUT 18
#define PINMUX_GPIO_GPIO_16_OUT 19
#define PINMUX_GPIO_GPIO_17_OUT 20
#define PINMUX_GPIO_GPIO_18_OUT 21
#define PINMUX_GPIO_GPIO_19_OUT 22
#define PINMUX_GPIO_GPIO_20_OUT 23
#define PINMUX_GPIO_GPIO_21_OUT 24
#define PINMUX_GPIO_GPIO_22_OUT 25
#define PINMUX_GPIO_GPIO_23_OUT 26
#define PINMUX_GPIO_GPIO_24_OUT 27
#define PINMUX_GPIO_GPIO_25_OUT 28
#define PINMUX_GPIO_GPIO_26_OUT 29
#define PINMUX_GPIO_GPIO_27_OUT 30
#define PINMUX_GPIO_GPIO_28_OUT 31
#define PINMUX_GPIO_GPIO_29_OUT 32
#define PINMUX_GPIO_GPIO_30_OUT 33
#define PINMUX_GPIO_GPIO_31_OUT 34
#define PINMUX_I2C0_SDA_OUT 36
#define PINMUX_I2C0_SCL_OUT 37
#define PINMUX_I2C1_SDA_OUT 38
#define PINMUX_I2C1_SCL_OUT 39
#define PINMUX_I2C2_SDA_OUT 40
#define PINMUX_I2C2_SCL_OUT 41
#define PINMUX_UART1_TX_OUT 42
#define PINMUX_UART2_TX_OUT 43
#define PINMUX_UART3_TX_OUT 44

/**
 * Base address for uart peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART_BASE_ADDR 0x40000000u

/**
 * Base address for uart1 peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART1_BASE_ADDR 0x40010000u

/**
 * Base address for uart2 peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART2_BASE_ADDR 0x40020000u

/**
 * Base address for uart3 peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART3_BASE_ADDR 0x40030000u

/**
 * Base address for gpio peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_GPIO_BASE_ADDR 0x40040000u

/**
 * Base address for spi_device peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_DEVICE_BASE_ADDR 0x40050000u

/**
 * Base address for flash_ctrl peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_FLASH_CTRL_BASE_ADDR 0x41000000u

/**
 * Base address for rv_timer peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_TIMER_BASE_ADDR 0x40100000u

/**
 * Base address for i2c0 peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I2C0_BASE_ADDR 0x40080000u

/**
 * Base address for i2c1 peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I2C1_BASE_ADDR 0x40090000u

/**
 * Base address for i2c2 peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I2C2_BASE_ADDR 0x400A0000u

/**
 * Base address for sensor_ctrl peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR 0x40110000u

/**
 * Base address for otp_ctrl peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTP_CTRL_BASE_ADDR 0x40130000u

/**
 * Base address for aes peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AES_BASE_ADDR 0x41100000u

/**
 * Base address for hmac peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_HMAC_BASE_ADDR 0x41110000u

/**
 * Base address for kmac peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_KMAC_BASE_ADDR 0x41120000u

/**
 * Base address for rv_plic peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_PLIC_BASE_ADDR 0x41010000u

/**
 * Base address for pinmux_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PINMUX_AON_BASE_ADDR 0x40460000u

/**
 * Base address for padctrl_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PADCTRL_AON_BASE_ADDR 0x40470000u

/**
 * Base address for alert_handler peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR 0x41170000u

/**
 * Base address for pwrmgr_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PWRMGR_AON_BASE_ADDR 0x40400000u

/**
 * Base address for rstmgr_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RSTMGR_AON_BASE_ADDR 0x40410000u

/**
 * Base address for clkmgr_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CLKMGR_AON_BASE_ADDR 0x40420000u

/**
 * Base address for rbox_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RBOX_AON_BASE_ADDR 0x40430000u

/**
 * Base address for timer_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_TIMER_AON_BASE_ADDR 0x40480000u

/**
 * Base address for nmi_gen peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_NMI_GEN_BASE_ADDR 0x41180000u

/**
 * Base address for usbdev_aon peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_USBDEV_AON_BASE_ADDR 0x40500000u

/**
 * Base address for pattgen peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PATTGEN_BASE_ADDR 0x400E0000u

/**
 * Base address for keymgr peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_KEYMGR_BASE_ADDR 0x41130000u

/**
 * Base address for csrng peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CSRNG_BASE_ADDR 0x41150000u

/**
 * Base address for entropy_src peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR 0x41160000u

/**
 * Base address for otbn peripheral in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTBN_BASE_ADDR 0x50000000u


/**
 * PLIC Interrupt source peripheral enumeration.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_earlgrey_plic_peripheral {
  kTopEarlgreyPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopEarlgreyPlicPeripheralGpio = 1, /**< gpio */
  kTopEarlgreyPlicPeripheralUart = 2, /**< uart */
  kTopEarlgreyPlicPeripheralSpiDevice = 3, /**< spi_device */
  kTopEarlgreyPlicPeripheralFlashCtrl = 4, /**< flash_ctrl */
  kTopEarlgreyPlicPeripheralKeymgr = 5, /**< keymgr */
  kTopEarlgreyPlicPeripheralHmac = 6, /**< hmac */
  kTopEarlgreyPlicPeripheralKmac = 7, /**< kmac */
  kTopEarlgreyPlicPeripheralAlertHandler = 8, /**< alert_handler */
  kTopEarlgreyPlicPeripheralNmiGen = 9, /**< nmi_gen */
  kTopEarlgreyPlicPeripheralUsbdevAon = 10, /**< usbdev_aon */
  kTopEarlgreyPlicPeripheralPwrmgrAon = 11, /**< pwrmgr_aon */
  kTopEarlgreyPlicPeripheralOtpCtrl = 12, /**< otp_ctrl */
  kTopEarlgreyPlicPeripheralUart1 = 13, /**< uart1 */
  kTopEarlgreyPlicPeripheralUart2 = 14, /**< uart2 */
  kTopEarlgreyPlicPeripheralUart3 = 15, /**< uart3 */
  kTopEarlgreyPlicPeripheralI2c0 = 16, /**< i2c0 */
  kTopEarlgreyPlicPeripheralI2c1 = 17, /**< i2c1 */
  kTopEarlgreyPlicPeripheralI2c2 = 18, /**< i2c2 */
  kTopEarlgreyPlicPeripheralOtbn = 19, /**< otbn */
  kTopEarlgreyPlicPeripheralLast = 19, /**< \internal Final PLIC peripheral */
} top_earlgrey_plic_peripheral_t;

/**
 * PLIC Interrupt Ids Enumeration
 *
 * Enumeration of all PLIC interrupt source IDs. The IRQ IDs belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_plic_irq_id {
  kTopEarlgreyPlicIrqIdNone = 0, /**< No Interrupt */
  kTopEarlgreyPlicIrqIdGpioGpio0 = 1, /**< gpio_gpio 0 */
  kTopEarlgreyPlicIrqIdGpioGpio1 = 2, /**< gpio_gpio 1 */
  kTopEarlgreyPlicIrqIdGpioGpio2 = 3, /**< gpio_gpio 2 */
  kTopEarlgreyPlicIrqIdGpioGpio3 = 4, /**< gpio_gpio 3 */
  kTopEarlgreyPlicIrqIdGpioGpio4 = 5, /**< gpio_gpio 4 */
  kTopEarlgreyPlicIrqIdGpioGpio5 = 6, /**< gpio_gpio 5 */
  kTopEarlgreyPlicIrqIdGpioGpio6 = 7, /**< gpio_gpio 6 */
  kTopEarlgreyPlicIrqIdGpioGpio7 = 8, /**< gpio_gpio 7 */
  kTopEarlgreyPlicIrqIdGpioGpio8 = 9, /**< gpio_gpio 8 */
  kTopEarlgreyPlicIrqIdGpioGpio9 = 10, /**< gpio_gpio 9 */
  kTopEarlgreyPlicIrqIdGpioGpio10 = 11, /**< gpio_gpio 10 */
  kTopEarlgreyPlicIrqIdGpioGpio11 = 12, /**< gpio_gpio 11 */
  kTopEarlgreyPlicIrqIdGpioGpio12 = 13, /**< gpio_gpio 12 */
  kTopEarlgreyPlicIrqIdGpioGpio13 = 14, /**< gpio_gpio 13 */
  kTopEarlgreyPlicIrqIdGpioGpio14 = 15, /**< gpio_gpio 14 */
  kTopEarlgreyPlicIrqIdGpioGpio15 = 16, /**< gpio_gpio 15 */
  kTopEarlgreyPlicIrqIdGpioGpio16 = 17, /**< gpio_gpio 16 */
  kTopEarlgreyPlicIrqIdGpioGpio17 = 18, /**< gpio_gpio 17 */
  kTopEarlgreyPlicIrqIdGpioGpio18 = 19, /**< gpio_gpio 18 */
  kTopEarlgreyPlicIrqIdGpioGpio19 = 20, /**< gpio_gpio 19 */
  kTopEarlgreyPlicIrqIdGpioGpio20 = 21, /**< gpio_gpio 20 */
  kTopEarlgreyPlicIrqIdGpioGpio21 = 22, /**< gpio_gpio 21 */
  kTopEarlgreyPlicIrqIdGpioGpio22 = 23, /**< gpio_gpio 22 */
  kTopEarlgreyPlicIrqIdGpioGpio23 = 24, /**< gpio_gpio 23 */
  kTopEarlgreyPlicIrqIdGpioGpio24 = 25, /**< gpio_gpio 24 */
  kTopEarlgreyPlicIrqIdGpioGpio25 = 26, /**< gpio_gpio 25 */
  kTopEarlgreyPlicIrqIdGpioGpio26 = 27, /**< gpio_gpio 26 */
  kTopEarlgreyPlicIrqIdGpioGpio27 = 28, /**< gpio_gpio 27 */
  kTopEarlgreyPlicIrqIdGpioGpio28 = 29, /**< gpio_gpio 28 */
  kTopEarlgreyPlicIrqIdGpioGpio29 = 30, /**< gpio_gpio 29 */
  kTopEarlgreyPlicIrqIdGpioGpio30 = 31, /**< gpio_gpio 30 */
  kTopEarlgreyPlicIrqIdGpioGpio31 = 32, /**< gpio_gpio 31 */
  kTopEarlgreyPlicIrqIdUartTxWatermark = 33, /**< uart_tx_watermark */
  kTopEarlgreyPlicIrqIdUartRxWatermark = 34, /**< uart_rx_watermark */
  kTopEarlgreyPlicIrqIdUartTxEmpty = 35, /**< uart_tx_empty */
  kTopEarlgreyPlicIrqIdUartRxOverflow = 36, /**< uart_rx_overflow */
  kTopEarlgreyPlicIrqIdUartRxFrameErr = 37, /**< uart_rx_frame_err */
  kTopEarlgreyPlicIrqIdUartRxBreakErr = 38, /**< uart_rx_break_err */
  kTopEarlgreyPlicIrqIdUartRxTimeout = 39, /**< uart_rx_timeout */
  kTopEarlgreyPlicIrqIdUartRxParityErr = 40, /**< uart_rx_parity_err */
  kTopEarlgreyPlicIrqIdSpiDeviceRxf = 41, /**< spi_device_rxf */
  kTopEarlgreyPlicIrqIdSpiDeviceRxlvl = 42, /**< spi_device_rxlvl */
  kTopEarlgreyPlicIrqIdSpiDeviceTxlvl = 43, /**< spi_device_txlvl */
  kTopEarlgreyPlicIrqIdSpiDeviceRxerr = 44, /**< spi_device_rxerr */
  kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow = 45, /**< spi_device_rxoverflow */
  kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow = 46, /**< spi_device_txunderflow */
  kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty = 47, /**< flash_ctrl_prog_empty */
  kTopEarlgreyPlicIrqIdFlashCtrlProgLvl = 48, /**< flash_ctrl_prog_lvl */
  kTopEarlgreyPlicIrqIdFlashCtrlRdFull = 49, /**< flash_ctrl_rd_full */
  kTopEarlgreyPlicIrqIdFlashCtrlRdLvl = 50, /**< flash_ctrl_rd_lvl */
  kTopEarlgreyPlicIrqIdFlashCtrlOpDone = 51, /**< flash_ctrl_op_done */
  kTopEarlgreyPlicIrqIdFlashCtrlOpError = 52, /**< flash_ctrl_op_error */
  kTopEarlgreyPlicIrqIdKeymgrOpDone = 53, /**< keymgr_op_done */
  kTopEarlgreyPlicIrqIdHmacHmacDone = 54, /**< hmac_hmac_done */
  kTopEarlgreyPlicIrqIdHmacFifoEmpty = 55, /**< hmac_fifo_empty */
  kTopEarlgreyPlicIrqIdHmacHmacErr = 56, /**< hmac_hmac_err */
  kTopEarlgreyPlicIrqIdKmacKmacDone = 57, /**< kmac_kmac_done */
  kTopEarlgreyPlicIrqIdKmacFifoEmpty = 58, /**< kmac_fifo_empty */
  kTopEarlgreyPlicIrqIdKmacKmacErr = 59, /**< kmac_kmac_err */
  kTopEarlgreyPlicIrqIdAlertHandlerClassa = 60, /**< alert_handler_classa */
  kTopEarlgreyPlicIrqIdAlertHandlerClassb = 61, /**< alert_handler_classb */
  kTopEarlgreyPlicIrqIdAlertHandlerClassc = 62, /**< alert_handler_classc */
  kTopEarlgreyPlicIrqIdAlertHandlerClassd = 63, /**< alert_handler_classd */
  kTopEarlgreyPlicIrqIdNmiGenEsc0 = 64, /**< nmi_gen_esc0 */
  kTopEarlgreyPlicIrqIdNmiGenEsc1 = 65, /**< nmi_gen_esc1 */
  kTopEarlgreyPlicIrqIdNmiGenEsc2 = 66, /**< nmi_gen_esc2 */
  kTopEarlgreyPlicIrqIdNmiGenEsc3 = 67, /**< nmi_gen_esc3 */
  kTopEarlgreyPlicIrqIdUsbdevAonPktReceived = 68, /**< usbdev_aon_pkt_received */
  kTopEarlgreyPlicIrqIdUsbdevAonPktSent = 69, /**< usbdev_aon_pkt_sent */
  kTopEarlgreyPlicIrqIdUsbdevAonDisconnected = 70, /**< usbdev_aon_disconnected */
  kTopEarlgreyPlicIrqIdUsbdevAonHostLost = 71, /**< usbdev_aon_host_lost */
  kTopEarlgreyPlicIrqIdUsbdevAonLinkReset = 72, /**< usbdev_aon_link_reset */
  kTopEarlgreyPlicIrqIdUsbdevAonLinkSuspend = 73, /**< usbdev_aon_link_suspend */
  kTopEarlgreyPlicIrqIdUsbdevAonLinkResume = 74, /**< usbdev_aon_link_resume */
  kTopEarlgreyPlicIrqIdUsbdevAonAvEmpty = 75, /**< usbdev_aon_av_empty */
  kTopEarlgreyPlicIrqIdUsbdevAonRxFull = 76, /**< usbdev_aon_rx_full */
  kTopEarlgreyPlicIrqIdUsbdevAonAvOverflow = 77, /**< usbdev_aon_av_overflow */
  kTopEarlgreyPlicIrqIdUsbdevAonLinkInErr = 78, /**< usbdev_aon_link_in_err */
  kTopEarlgreyPlicIrqIdUsbdevAonRxCrcErr = 79, /**< usbdev_aon_rx_crc_err */
  kTopEarlgreyPlicIrqIdUsbdevAonRxPidErr = 80, /**< usbdev_aon_rx_pid_err */
  kTopEarlgreyPlicIrqIdUsbdevAonRxBitstuffErr = 81, /**< usbdev_aon_rx_bitstuff_err */
  kTopEarlgreyPlicIrqIdUsbdevAonFrame = 82, /**< usbdev_aon_frame */
  kTopEarlgreyPlicIrqIdUsbdevAonConnected = 83, /**< usbdev_aon_connected */
  kTopEarlgreyPlicIrqIdPwrmgrAonWakeup = 84, /**< pwrmgr_aon_wakeup */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpAccessDone = 85, /**< otp_ctrl_otp_access_done */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpCtrlErr = 86, /**< otp_ctrl_otp_ctrl_err */
  kTopEarlgreyPlicIrqIdUart1TxWatermark = 87, /**< uart1_tx_watermark */
  kTopEarlgreyPlicIrqIdUart1RxWatermark = 88, /**< uart1_rx_watermark */
  kTopEarlgreyPlicIrqIdUart1TxEmpty = 89, /**< uart1_tx_empty */
  kTopEarlgreyPlicIrqIdUart1RxOverflow = 90, /**< uart1_rx_overflow */
  kTopEarlgreyPlicIrqIdUart1RxFrameErr = 91, /**< uart1_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart1RxBreakErr = 92, /**< uart1_rx_break_err */
  kTopEarlgreyPlicIrqIdUart1RxTimeout = 93, /**< uart1_rx_timeout */
  kTopEarlgreyPlicIrqIdUart1RxParityErr = 94, /**< uart1_rx_parity_err */
  kTopEarlgreyPlicIrqIdUart2TxWatermark = 95, /**< uart2_tx_watermark */
  kTopEarlgreyPlicIrqIdUart2RxWatermark = 96, /**< uart2_rx_watermark */
  kTopEarlgreyPlicIrqIdUart2TxEmpty = 97, /**< uart2_tx_empty */
  kTopEarlgreyPlicIrqIdUart2RxOverflow = 98, /**< uart2_rx_overflow */
  kTopEarlgreyPlicIrqIdUart2RxFrameErr = 99, /**< uart2_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart2RxBreakErr = 100, /**< uart2_rx_break_err */
  kTopEarlgreyPlicIrqIdUart2RxTimeout = 101, /**< uart2_rx_timeout */
  kTopEarlgreyPlicIrqIdUart2RxParityErr = 102, /**< uart2_rx_parity_err */
  kTopEarlgreyPlicIrqIdUart3TxWatermark = 103, /**< uart3_tx_watermark */
  kTopEarlgreyPlicIrqIdUart3RxWatermark = 104, /**< uart3_rx_watermark */
  kTopEarlgreyPlicIrqIdUart3TxEmpty = 105, /**< uart3_tx_empty */
  kTopEarlgreyPlicIrqIdUart3RxOverflow = 106, /**< uart3_rx_overflow */
  kTopEarlgreyPlicIrqIdUart3RxFrameErr = 107, /**< uart3_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart3RxBreakErr = 108, /**< uart3_rx_break_err */
  kTopEarlgreyPlicIrqIdUart3RxTimeout = 109, /**< uart3_rx_timeout */
  kTopEarlgreyPlicIrqIdUart3RxParityErr = 110, /**< uart3_rx_parity_err */
  kTopEarlgreyPlicIrqIdI2c0FmtWatermark = 111, /**< i2c0_fmt_watermark */
  kTopEarlgreyPlicIrqIdI2c0RxWatermark = 112, /**< i2c0_rx_watermark */
  kTopEarlgreyPlicIrqIdI2c0FmtOverflow = 113, /**< i2c0_fmt_overflow */
  kTopEarlgreyPlicIrqIdI2c0RxOverflow = 114, /**< i2c0_rx_overflow */
  kTopEarlgreyPlicIrqIdI2c0Nak = 115, /**< i2c0_nak */
  kTopEarlgreyPlicIrqIdI2c0SclInterference = 116, /**< i2c0_scl_interference */
  kTopEarlgreyPlicIrqIdI2c0SdaInterference = 117, /**< i2c0_sda_interference */
  kTopEarlgreyPlicIrqIdI2c0StretchTimeout = 118, /**< i2c0_stretch_timeout */
  kTopEarlgreyPlicIrqIdI2c0SdaUnstable = 119, /**< i2c0_sda_unstable */
  kTopEarlgreyPlicIrqIdI2c1FmtWatermark = 120, /**< i2c1_fmt_watermark */
  kTopEarlgreyPlicIrqIdI2c1RxWatermark = 121, /**< i2c1_rx_watermark */
  kTopEarlgreyPlicIrqIdI2c1FmtOverflow = 122, /**< i2c1_fmt_overflow */
  kTopEarlgreyPlicIrqIdI2c1RxOverflow = 123, /**< i2c1_rx_overflow */
  kTopEarlgreyPlicIrqIdI2c1Nak = 124, /**< i2c1_nak */
  kTopEarlgreyPlicIrqIdI2c1SclInterference = 125, /**< i2c1_scl_interference */
  kTopEarlgreyPlicIrqIdI2c1SdaInterference = 126, /**< i2c1_sda_interference */
  kTopEarlgreyPlicIrqIdI2c1StretchTimeout = 127, /**< i2c1_stretch_timeout */
  kTopEarlgreyPlicIrqIdI2c1SdaUnstable = 128, /**< i2c1_sda_unstable */
  kTopEarlgreyPlicIrqIdI2c2FmtWatermark = 129, /**< i2c2_fmt_watermark */
  kTopEarlgreyPlicIrqIdI2c2RxWatermark = 130, /**< i2c2_rx_watermark */
  kTopEarlgreyPlicIrqIdI2c2FmtOverflow = 131, /**< i2c2_fmt_overflow */
  kTopEarlgreyPlicIrqIdI2c2RxOverflow = 132, /**< i2c2_rx_overflow */
  kTopEarlgreyPlicIrqIdI2c2Nak = 133, /**< i2c2_nak */
  kTopEarlgreyPlicIrqIdI2c2SclInterference = 134, /**< i2c2_scl_interference */
  kTopEarlgreyPlicIrqIdI2c2SdaInterference = 135, /**< i2c2_sda_interference */
  kTopEarlgreyPlicIrqIdI2c2StretchTimeout = 136, /**< i2c2_stretch_timeout */
  kTopEarlgreyPlicIrqIdI2c2SdaUnstable = 137, /**< i2c2_sda_unstable */
  kTopEarlgreyPlicIrqIdOtbnDone = 138, /**< otbn_done */
  kTopEarlgreyPlicIrqIdOtbnErr = 139, /**< otbn_err */
  kTopEarlgreyPlicIrqIdLast = 139, /**< \internal The Last Valid Interrupt ID. */
} top_earlgrey_plic_irq_id_t;

/**
 * PLIC Interrupt Id to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
extern const top_earlgrey_plic_peripheral_t
    top_earlgrey_plic_interrupt_for_peripheral[140];

/**
 * PLIC external interrupt target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access dependent on the target.
 */
typedef enum top_earlgrey_plic_target {
  kTopEarlgreyPlicTargetIbex0 = 0, /**< Ibex Core 0 */
  kTopEarlgreyPlicTargetLast = 0, /**< \internal Final PLIC target */
} top_earlgrey_plic_target_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_
