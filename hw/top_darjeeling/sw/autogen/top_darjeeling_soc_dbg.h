// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
// -o hw/top_darjeeling

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_

/**
 * @file
 * @brief Top-specific Definitions
 *
 * This file contains preprocessor and type definitions for use within the
 * device C/C++ codebase.
 *
 * These definitions are for information that depends on the top-specific chip
 * configuration, which includes:
 * - Device Memory Information (for Peripherals and Memory)
 * - PLIC Interrupt ID Names and Source Mappings
 * - Pinmux Pin/Select Names
 * - Power Manager Wakeups
 */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Peripheral base address for dmi device on lc_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR 0x20000u

/**
 * Peripheral size for dmi device on lc_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR and
 * `TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR + TOP_DARJEELING_LC_CTRL_DMI_SIZE_BYTES`.
 */
#define TOP_DARJEELING_LC_CTRL_DMI_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for dbg device on rv_dm in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_DM_DBG_BASE_ADDR 0x0u

/**
 * Peripheral size for dbg device on rv_dm in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_DM_DBG_BASE_ADDR and
 * `TOP_DARJEELING_RV_DM_DBG_BASE_ADDR + TOP_DARJEELING_RV_DM_DBG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_DM_DBG_SIZE_BYTES 0x200u

/**
 * Peripheral base address for soc device on mbx_jtag in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR 0x1000u

/**
 * Peripheral size for soc device on mbx_jtag in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR + TOP_DARJEELING_MBX_JTAG_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_JTAG_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for jtag device on soc_dbg_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SOC_DBG_CTRL_JTAG_BASE_ADDR 0x2300u

/**
 * Peripheral size for jtag device on soc_dbg_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_DBG_CTRL_JTAG_BASE_ADDR and
 * `TOP_DARJEELING_SOC_DBG_CTRL_JTAG_BASE_ADDR + TOP_DARJEELING_SOC_DBG_CTRL_JTAG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_DBG_CTRL_JTAG_SIZE_BYTES 0x20u



/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_darjeeling_plic_peripheral {
  kTopDarjeelingPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopDarjeelingPlicPeripheralUart0 = 1, /**< uart0 */
  kTopDarjeelingPlicPeripheralGpio = 2, /**< gpio */
  kTopDarjeelingPlicPeripheralSpiDevice = 3, /**< spi_device */
  kTopDarjeelingPlicPeripheralI2c0 = 4, /**< i2c0 */
  kTopDarjeelingPlicPeripheralRvTimer = 5, /**< rv_timer */
  kTopDarjeelingPlicPeripheralOtpCtrl = 6, /**< otp_ctrl */
  kTopDarjeelingPlicPeripheralAlertHandler = 7, /**< alert_handler */
  kTopDarjeelingPlicPeripheralSpiHost0 = 8, /**< spi_host0 */
  kTopDarjeelingPlicPeripheralPwrmgrAon = 9, /**< pwrmgr_aon */
  kTopDarjeelingPlicPeripheralAonTimerAon = 10, /**< aon_timer_aon */
  kTopDarjeelingPlicPeripheralSensorCtrl = 11, /**< sensor_ctrl */
  kTopDarjeelingPlicPeripheralSocProxy = 12, /**< soc_proxy */
  kTopDarjeelingPlicPeripheralHmac = 13, /**< hmac */
  kTopDarjeelingPlicPeripheralKmac = 14, /**< kmac */
  kTopDarjeelingPlicPeripheralOtbn = 15, /**< otbn */
  kTopDarjeelingPlicPeripheralKeymgrDpe = 16, /**< keymgr_dpe */
  kTopDarjeelingPlicPeripheralCsrng = 17, /**< csrng */
  kTopDarjeelingPlicPeripheralEdn0 = 18, /**< edn0 */
  kTopDarjeelingPlicPeripheralEdn1 = 19, /**< edn1 */
  kTopDarjeelingPlicPeripheralDma = 20, /**< dma */
  kTopDarjeelingPlicPeripheralMbx0 = 21, /**< mbx0 */
  kTopDarjeelingPlicPeripheralMbx1 = 22, /**< mbx1 */
  kTopDarjeelingPlicPeripheralMbx2 = 23, /**< mbx2 */
  kTopDarjeelingPlicPeripheralMbx3 = 24, /**< mbx3 */
  kTopDarjeelingPlicPeripheralMbx4 = 25, /**< mbx4 */
  kTopDarjeelingPlicPeripheralMbx5 = 26, /**< mbx5 */
  kTopDarjeelingPlicPeripheralMbx6 = 27, /**< mbx6 */
  kTopDarjeelingPlicPeripheralMbxJtag = 28, /**< mbx_jtag */
  kTopDarjeelingPlicPeripheralMbxPcie0 = 29, /**< mbx_pcie0 */
  kTopDarjeelingPlicPeripheralMbxPcie1 = 30, /**< mbx_pcie1 */
  kTopDarjeelingPlicPeripheralLast = 30, /**< \internal Final PLIC peripheral */
} top_darjeeling_plic_peripheral_t;

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_darjeeling_plic_irq_id {
  kTopDarjeelingPlicIrqIdNone = 0, /**< No Interrupt */
  kTopDarjeelingPlicIrqIdUart0TxWatermark = 1, /**< uart0_tx_watermark */
  kTopDarjeelingPlicIrqIdUart0RxWatermark = 2, /**< uart0_rx_watermark */
  kTopDarjeelingPlicIrqIdUart0TxDone = 3, /**< uart0_tx_done */
  kTopDarjeelingPlicIrqIdUart0RxOverflow = 4, /**< uart0_rx_overflow */
  kTopDarjeelingPlicIrqIdUart0RxFrameErr = 5, /**< uart0_rx_frame_err */
  kTopDarjeelingPlicIrqIdUart0RxBreakErr = 6, /**< uart0_rx_break_err */
  kTopDarjeelingPlicIrqIdUart0RxTimeout = 7, /**< uart0_rx_timeout */
  kTopDarjeelingPlicIrqIdUart0RxParityErr = 8, /**< uart0_rx_parity_err */
  kTopDarjeelingPlicIrqIdUart0TxEmpty = 9, /**< uart0_tx_empty */
  kTopDarjeelingPlicIrqIdGpioGpio0 = 10, /**< gpio_gpio 0 */
  kTopDarjeelingPlicIrqIdGpioGpio1 = 11, /**< gpio_gpio 1 */
  kTopDarjeelingPlicIrqIdGpioGpio2 = 12, /**< gpio_gpio 2 */
  kTopDarjeelingPlicIrqIdGpioGpio3 = 13, /**< gpio_gpio 3 */
  kTopDarjeelingPlicIrqIdGpioGpio4 = 14, /**< gpio_gpio 4 */
  kTopDarjeelingPlicIrqIdGpioGpio5 = 15, /**< gpio_gpio 5 */
  kTopDarjeelingPlicIrqIdGpioGpio6 = 16, /**< gpio_gpio 6 */
  kTopDarjeelingPlicIrqIdGpioGpio7 = 17, /**< gpio_gpio 7 */
  kTopDarjeelingPlicIrqIdGpioGpio8 = 18, /**< gpio_gpio 8 */
  kTopDarjeelingPlicIrqIdGpioGpio9 = 19, /**< gpio_gpio 9 */
  kTopDarjeelingPlicIrqIdGpioGpio10 = 20, /**< gpio_gpio 10 */
  kTopDarjeelingPlicIrqIdGpioGpio11 = 21, /**< gpio_gpio 11 */
  kTopDarjeelingPlicIrqIdGpioGpio12 = 22, /**< gpio_gpio 12 */
  kTopDarjeelingPlicIrqIdGpioGpio13 = 23, /**< gpio_gpio 13 */
  kTopDarjeelingPlicIrqIdGpioGpio14 = 24, /**< gpio_gpio 14 */
  kTopDarjeelingPlicIrqIdGpioGpio15 = 25, /**< gpio_gpio 15 */
  kTopDarjeelingPlicIrqIdGpioGpio16 = 26, /**< gpio_gpio 16 */
  kTopDarjeelingPlicIrqIdGpioGpio17 = 27, /**< gpio_gpio 17 */
  kTopDarjeelingPlicIrqIdGpioGpio18 = 28, /**< gpio_gpio 18 */
  kTopDarjeelingPlicIrqIdGpioGpio19 = 29, /**< gpio_gpio 19 */
  kTopDarjeelingPlicIrqIdGpioGpio20 = 30, /**< gpio_gpio 20 */
  kTopDarjeelingPlicIrqIdGpioGpio21 = 31, /**< gpio_gpio 21 */
  kTopDarjeelingPlicIrqIdGpioGpio22 = 32, /**< gpio_gpio 22 */
  kTopDarjeelingPlicIrqIdGpioGpio23 = 33, /**< gpio_gpio 23 */
  kTopDarjeelingPlicIrqIdGpioGpio24 = 34, /**< gpio_gpio 24 */
  kTopDarjeelingPlicIrqIdGpioGpio25 = 35, /**< gpio_gpio 25 */
  kTopDarjeelingPlicIrqIdGpioGpio26 = 36, /**< gpio_gpio 26 */
  kTopDarjeelingPlicIrqIdGpioGpio27 = 37, /**< gpio_gpio 27 */
  kTopDarjeelingPlicIrqIdGpioGpio28 = 38, /**< gpio_gpio 28 */
  kTopDarjeelingPlicIrqIdGpioGpio29 = 39, /**< gpio_gpio 29 */
  kTopDarjeelingPlicIrqIdGpioGpio30 = 40, /**< gpio_gpio 30 */
  kTopDarjeelingPlicIrqIdGpioGpio31 = 41, /**< gpio_gpio 31 */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 42, /**< spi_device_upload_cmdfifo_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 43, /**< spi_device_upload_payload_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadPayloadOverflow = 44, /**< spi_device_upload_payload_overflow */
  kTopDarjeelingPlicIrqIdSpiDeviceReadbufWatermark = 45, /**< spi_device_readbuf_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceReadbufFlip = 46, /**< spi_device_readbuf_flip */
  kTopDarjeelingPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 47, /**< spi_device_tpm_header_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 48, /**< spi_device_tpm_rdfifo_cmd_end */
  kTopDarjeelingPlicIrqIdSpiDeviceTpmRdfifoDrop = 49, /**< spi_device_tpm_rdfifo_drop */
  kTopDarjeelingPlicIrqIdI2c0FmtThreshold = 50, /**< i2c0_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c0RxThreshold = 51, /**< i2c0_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c0AcqThreshold = 52, /**< i2c0_acq_threshold */
  kTopDarjeelingPlicIrqIdI2c0RxOverflow = 53, /**< i2c0_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c0ControllerHalt = 54, /**< i2c0_controller_halt */
  kTopDarjeelingPlicIrqIdI2c0SclInterference = 55, /**< i2c0_scl_interference */
  kTopDarjeelingPlicIrqIdI2c0SdaInterference = 56, /**< i2c0_sda_interference */
  kTopDarjeelingPlicIrqIdI2c0StretchTimeout = 57, /**< i2c0_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c0SdaUnstable = 58, /**< i2c0_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c0CmdComplete = 59, /**< i2c0_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c0TxStretch = 60, /**< i2c0_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c0TxThreshold = 61, /**< i2c0_tx_threshold */
  kTopDarjeelingPlicIrqIdI2c0AcqStretch = 62, /**< i2c0_acq_stretch */
  kTopDarjeelingPlicIrqIdI2c0UnexpStop = 63, /**< i2c0_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c0HostTimeout = 64, /**< i2c0_host_timeout */
  kTopDarjeelingPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 65, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpOperationDone = 66, /**< otp_ctrl_otp_operation_done */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpError = 67, /**< otp_ctrl_otp_error */
  kTopDarjeelingPlicIrqIdAlertHandlerClassa = 68, /**< alert_handler_classa */
  kTopDarjeelingPlicIrqIdAlertHandlerClassb = 69, /**< alert_handler_classb */
  kTopDarjeelingPlicIrqIdAlertHandlerClassc = 70, /**< alert_handler_classc */
  kTopDarjeelingPlicIrqIdAlertHandlerClassd = 71, /**< alert_handler_classd */
  kTopDarjeelingPlicIrqIdSpiHost0Error = 72, /**< spi_host0_error */
  kTopDarjeelingPlicIrqIdSpiHost0SpiEvent = 73, /**< spi_host0_spi_event */
  kTopDarjeelingPlicIrqIdPwrmgrAonWakeup = 74, /**< pwrmgr_aon_wakeup */
  kTopDarjeelingPlicIrqIdAonTimerAonWkupTimerExpired = 75, /**< aon_timer_aon_wkup_timer_expired */
  kTopDarjeelingPlicIrqIdAonTimerAonWdogTimerBark = 76, /**< aon_timer_aon_wdog_timer_bark */
  kTopDarjeelingPlicIrqIdSensorCtrlIoStatusChange = 77, /**< sensor_ctrl_io_status_change */
  kTopDarjeelingPlicIrqIdSensorCtrlInitStatusChange = 78, /**< sensor_ctrl_init_status_change */
  kTopDarjeelingPlicIrqIdSocProxyExternal0 = 79, /**< soc_proxy_external 0 */
  kTopDarjeelingPlicIrqIdSocProxyExternal1 = 80, /**< soc_proxy_external 1 */
  kTopDarjeelingPlicIrqIdSocProxyExternal2 = 81, /**< soc_proxy_external 2 */
  kTopDarjeelingPlicIrqIdSocProxyExternal3 = 82, /**< soc_proxy_external 3 */
  kTopDarjeelingPlicIrqIdSocProxyExternal4 = 83, /**< soc_proxy_external 4 */
  kTopDarjeelingPlicIrqIdSocProxyExternal5 = 84, /**< soc_proxy_external 5 */
  kTopDarjeelingPlicIrqIdSocProxyExternal6 = 85, /**< soc_proxy_external 6 */
  kTopDarjeelingPlicIrqIdSocProxyExternal7 = 86, /**< soc_proxy_external 7 */
  kTopDarjeelingPlicIrqIdSocProxyExternal8 = 87, /**< soc_proxy_external 8 */
  kTopDarjeelingPlicIrqIdSocProxyExternal9 = 88, /**< soc_proxy_external 9 */
  kTopDarjeelingPlicIrqIdSocProxyExternal10 = 89, /**< soc_proxy_external 10 */
  kTopDarjeelingPlicIrqIdSocProxyExternal11 = 90, /**< soc_proxy_external 11 */
  kTopDarjeelingPlicIrqIdSocProxyExternal12 = 91, /**< soc_proxy_external 12 */
  kTopDarjeelingPlicIrqIdSocProxyExternal13 = 92, /**< soc_proxy_external 13 */
  kTopDarjeelingPlicIrqIdSocProxyExternal14 = 93, /**< soc_proxy_external 14 */
  kTopDarjeelingPlicIrqIdSocProxyExternal15 = 94, /**< soc_proxy_external 15 */
  kTopDarjeelingPlicIrqIdSocProxyExternal16 = 95, /**< soc_proxy_external 16 */
  kTopDarjeelingPlicIrqIdSocProxyExternal17 = 96, /**< soc_proxy_external 17 */
  kTopDarjeelingPlicIrqIdSocProxyExternal18 = 97, /**< soc_proxy_external 18 */
  kTopDarjeelingPlicIrqIdSocProxyExternal19 = 98, /**< soc_proxy_external 19 */
  kTopDarjeelingPlicIrqIdSocProxyExternal20 = 99, /**< soc_proxy_external 20 */
  kTopDarjeelingPlicIrqIdSocProxyExternal21 = 100, /**< soc_proxy_external 21 */
  kTopDarjeelingPlicIrqIdSocProxyExternal22 = 101, /**< soc_proxy_external 22 */
  kTopDarjeelingPlicIrqIdSocProxyExternal23 = 102, /**< soc_proxy_external 23 */
  kTopDarjeelingPlicIrqIdSocProxyExternal24 = 103, /**< soc_proxy_external 24 */
  kTopDarjeelingPlicIrqIdSocProxyExternal25 = 104, /**< soc_proxy_external 25 */
  kTopDarjeelingPlicIrqIdSocProxyExternal26 = 105, /**< soc_proxy_external 26 */
  kTopDarjeelingPlicIrqIdSocProxyExternal27 = 106, /**< soc_proxy_external 27 */
  kTopDarjeelingPlicIrqIdSocProxyExternal28 = 107, /**< soc_proxy_external 28 */
  kTopDarjeelingPlicIrqIdSocProxyExternal29 = 108, /**< soc_proxy_external 29 */
  kTopDarjeelingPlicIrqIdSocProxyExternal30 = 109, /**< soc_proxy_external 30 */
  kTopDarjeelingPlicIrqIdSocProxyExternal31 = 110, /**< soc_proxy_external 31 */
  kTopDarjeelingPlicIrqIdHmacHmacDone = 111, /**< hmac_hmac_done */
  kTopDarjeelingPlicIrqIdHmacFifoEmpty = 112, /**< hmac_fifo_empty */
  kTopDarjeelingPlicIrqIdHmacHmacErr = 113, /**< hmac_hmac_err */
  kTopDarjeelingPlicIrqIdKmacKmacDone = 114, /**< kmac_kmac_done */
  kTopDarjeelingPlicIrqIdKmacFifoEmpty = 115, /**< kmac_fifo_empty */
  kTopDarjeelingPlicIrqIdKmacKmacErr = 116, /**< kmac_kmac_err */
  kTopDarjeelingPlicIrqIdOtbnDone = 117, /**< otbn_done */
  kTopDarjeelingPlicIrqIdKeymgrDpeOpDone = 118, /**< keymgr_dpe_op_done */
  kTopDarjeelingPlicIrqIdCsrngCsCmdReqDone = 119, /**< csrng_cs_cmd_req_done */
  kTopDarjeelingPlicIrqIdCsrngCsEntropyReq = 120, /**< csrng_cs_entropy_req */
  kTopDarjeelingPlicIrqIdCsrngCsHwInstExc = 121, /**< csrng_cs_hw_inst_exc */
  kTopDarjeelingPlicIrqIdCsrngCsFatalErr = 122, /**< csrng_cs_fatal_err */
  kTopDarjeelingPlicIrqIdEdn0EdnCmdReqDone = 123, /**< edn0_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn0EdnFatalErr = 124, /**< edn0_edn_fatal_err */
  kTopDarjeelingPlicIrqIdEdn1EdnCmdReqDone = 125, /**< edn1_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn1EdnFatalErr = 126, /**< edn1_edn_fatal_err */
  kTopDarjeelingPlicIrqIdDmaDmaDone = 127, /**< dma_dma_done */
  kTopDarjeelingPlicIrqIdDmaDmaChunkDone = 128, /**< dma_dma_chunk_done */
  kTopDarjeelingPlicIrqIdDmaDmaError = 129, /**< dma_dma_error */
  kTopDarjeelingPlicIrqIdMbx0MbxReady = 130, /**< mbx0_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx0MbxAbort = 131, /**< mbx0_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx0MbxError = 132, /**< mbx0_mbx_error */
  kTopDarjeelingPlicIrqIdMbx1MbxReady = 133, /**< mbx1_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx1MbxAbort = 134, /**< mbx1_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx1MbxError = 135, /**< mbx1_mbx_error */
  kTopDarjeelingPlicIrqIdMbx2MbxReady = 136, /**< mbx2_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx2MbxAbort = 137, /**< mbx2_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx2MbxError = 138, /**< mbx2_mbx_error */
  kTopDarjeelingPlicIrqIdMbx3MbxReady = 139, /**< mbx3_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx3MbxAbort = 140, /**< mbx3_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx3MbxError = 141, /**< mbx3_mbx_error */
  kTopDarjeelingPlicIrqIdMbx4MbxReady = 142, /**< mbx4_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx4MbxAbort = 143, /**< mbx4_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx4MbxError = 144, /**< mbx4_mbx_error */
  kTopDarjeelingPlicIrqIdMbx5MbxReady = 145, /**< mbx5_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx5MbxAbort = 146, /**< mbx5_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx5MbxError = 147, /**< mbx5_mbx_error */
  kTopDarjeelingPlicIrqIdMbx6MbxReady = 148, /**< mbx6_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx6MbxAbort = 149, /**< mbx6_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx6MbxError = 150, /**< mbx6_mbx_error */
  kTopDarjeelingPlicIrqIdMbxJtagMbxReady = 151, /**< mbx_jtag_mbx_ready */
  kTopDarjeelingPlicIrqIdMbxJtagMbxAbort = 152, /**< mbx_jtag_mbx_abort */
  kTopDarjeelingPlicIrqIdMbxJtagMbxError = 153, /**< mbx_jtag_mbx_error */
  kTopDarjeelingPlicIrqIdMbxPcie0MbxReady = 154, /**< mbx_pcie0_mbx_ready */
  kTopDarjeelingPlicIrqIdMbxPcie0MbxAbort = 155, /**< mbx_pcie0_mbx_abort */
  kTopDarjeelingPlicIrqIdMbxPcie0MbxError = 156, /**< mbx_pcie0_mbx_error */
  kTopDarjeelingPlicIrqIdMbxPcie1MbxReady = 157, /**< mbx_pcie1_mbx_ready */
  kTopDarjeelingPlicIrqIdMbxPcie1MbxAbort = 158, /**< mbx_pcie1_mbx_abort */
  kTopDarjeelingPlicIrqIdMbxPcie1MbxError = 159, /**< mbx_pcie1_mbx_error */
  kTopDarjeelingPlicIrqIdLast = 159, /**< \internal The Last Valid Interrupt ID. */
} top_darjeeling_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_plic_irq_id_t` to
 * `top_darjeeling_plic_peripheral_t`.
 */
extern const top_darjeeling_plic_peripheral_t
    top_darjeeling_plic_interrupt_for_peripheral[160];

/**
 * PLIC Interrupt Target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access for a given interrupt target.
 */
typedef enum top_darjeeling_plic_target {
  kTopDarjeelingPlicTargetIbex0 = 0, /**< Ibex Core 0 */
  kTopDarjeelingPlicTargetLast = 0, /**< \internal Final PLIC target */
} top_darjeeling_plic_target_t;

#define PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO_PADS 12
#define NUM_DIO_PADS 73

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_darjeeling_pinmux_peripheral_in {
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi12 = 0, /**< Peripheral Input 0 */
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi13 = 1, /**< Peripheral Input 1 */
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi14 = 2, /**< Peripheral Input 2 */
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi15 = 3, /**< Peripheral Input 3 */
  kTopDarjeelingPinmuxPeripheralInLast = 3, /**< \internal Last valid peripheral input */
} top_darjeeling_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_darjeeling_pinmux_insel {
  kTopDarjeelingPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopDarjeelingPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopDarjeelingPinmuxInselMio0 = 2, /**< MIO Pad 0 */
  kTopDarjeelingPinmuxInselMio1 = 3, /**< MIO Pad 1 */
  kTopDarjeelingPinmuxInselMio2 = 4, /**< MIO Pad 2 */
  kTopDarjeelingPinmuxInselMio3 = 5, /**< MIO Pad 3 */
  kTopDarjeelingPinmuxInselMio4 = 6, /**< MIO Pad 4 */
  kTopDarjeelingPinmuxInselMio5 = 7, /**< MIO Pad 5 */
  kTopDarjeelingPinmuxInselMio6 = 8, /**< MIO Pad 6 */
  kTopDarjeelingPinmuxInselMio7 = 9, /**< MIO Pad 7 */
  kTopDarjeelingPinmuxInselMio8 = 10, /**< MIO Pad 8 */
  kTopDarjeelingPinmuxInselMio9 = 11, /**< MIO Pad 9 */
  kTopDarjeelingPinmuxInselMio10 = 12, /**< MIO Pad 10 */
  kTopDarjeelingPinmuxInselMio11 = 13, /**< MIO Pad 11 */
  kTopDarjeelingPinmuxInselLast = 13, /**< \internal Last valid insel value */
} top_darjeeling_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_darjeeling_pinmux_mio_out {
  kTopDarjeelingPinmuxMioOutMio0 = 0, /**< MIO Pad 0 */
  kTopDarjeelingPinmuxMioOutMio1 = 1, /**< MIO Pad 1 */
  kTopDarjeelingPinmuxMioOutMio2 = 2, /**< MIO Pad 2 */
  kTopDarjeelingPinmuxMioOutMio3 = 3, /**< MIO Pad 3 */
  kTopDarjeelingPinmuxMioOutMio4 = 4, /**< MIO Pad 4 */
  kTopDarjeelingPinmuxMioOutMio5 = 5, /**< MIO Pad 5 */
  kTopDarjeelingPinmuxMioOutMio6 = 6, /**< MIO Pad 6 */
  kTopDarjeelingPinmuxMioOutMio7 = 7, /**< MIO Pad 7 */
  kTopDarjeelingPinmuxMioOutMio8 = 8, /**< MIO Pad 8 */
  kTopDarjeelingPinmuxMioOutMio9 = 9, /**< MIO Pad 9 */
  kTopDarjeelingPinmuxMioOutMio10 = 10, /**< MIO Pad 10 */
  kTopDarjeelingPinmuxMioOutMio11 = 11, /**< MIO Pad 11 */
  kTopDarjeelingPinmuxMioOutLast = 11, /**< \internal Last valid mio output */
} top_darjeeling_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_darjeeling_pinmux_outsel {
  kTopDarjeelingPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopDarjeelingPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopDarjeelingPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopDarjeelingPinmuxOutselSocProxySocGpo12 = 3, /**< Peripheral Output 0 */
  kTopDarjeelingPinmuxOutselSocProxySocGpo13 = 4, /**< Peripheral Output 1 */
  kTopDarjeelingPinmuxOutselSocProxySocGpo14 = 5, /**< Peripheral Output 2 */
  kTopDarjeelingPinmuxOutselSocProxySocGpo15 = 6, /**< Peripheral Output 3 */
  kTopDarjeelingPinmuxOutselOtpCtrlTest0 = 7, /**< Peripheral Output 4 */
  kTopDarjeelingPinmuxOutselLast = 7, /**< \internal Last valid outsel value */
} top_darjeeling_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_darjeeling_direct_pads {
  kTopDarjeelingDirectPadsSpiHost0Sd0 = 0, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd1 = 1, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd2 = 2, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd3 = 3, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd0 = 4, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd1 = 5, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd2 = 6, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd3 = 7, /**<  */
  kTopDarjeelingDirectPadsI2c0Scl = 8, /**<  */
  kTopDarjeelingDirectPadsI2c0Sda = 9, /**<  */
  kTopDarjeelingDirectPadsGpioGpio0 = 10, /**<  */
  kTopDarjeelingDirectPadsGpioGpio1 = 11, /**<  */
  kTopDarjeelingDirectPadsGpioGpio2 = 12, /**<  */
  kTopDarjeelingDirectPadsGpioGpio3 = 13, /**<  */
  kTopDarjeelingDirectPadsGpioGpio4 = 14, /**<  */
  kTopDarjeelingDirectPadsGpioGpio5 = 15, /**<  */
  kTopDarjeelingDirectPadsGpioGpio6 = 16, /**<  */
  kTopDarjeelingDirectPadsGpioGpio7 = 17, /**<  */
  kTopDarjeelingDirectPadsGpioGpio8 = 18, /**<  */
  kTopDarjeelingDirectPadsGpioGpio9 = 19, /**<  */
  kTopDarjeelingDirectPadsGpioGpio10 = 20, /**<  */
  kTopDarjeelingDirectPadsGpioGpio11 = 21, /**<  */
  kTopDarjeelingDirectPadsGpioGpio12 = 22, /**<  */
  kTopDarjeelingDirectPadsGpioGpio13 = 23, /**<  */
  kTopDarjeelingDirectPadsGpioGpio14 = 24, /**<  */
  kTopDarjeelingDirectPadsGpioGpio15 = 25, /**<  */
  kTopDarjeelingDirectPadsGpioGpio16 = 26, /**<  */
  kTopDarjeelingDirectPadsGpioGpio17 = 27, /**<  */
  kTopDarjeelingDirectPadsGpioGpio18 = 28, /**<  */
  kTopDarjeelingDirectPadsGpioGpio19 = 29, /**<  */
  kTopDarjeelingDirectPadsGpioGpio20 = 30, /**<  */
  kTopDarjeelingDirectPadsGpioGpio21 = 31, /**<  */
  kTopDarjeelingDirectPadsGpioGpio22 = 32, /**<  */
  kTopDarjeelingDirectPadsGpioGpio23 = 33, /**<  */
  kTopDarjeelingDirectPadsGpioGpio24 = 34, /**<  */
  kTopDarjeelingDirectPadsGpioGpio25 = 35, /**<  */
  kTopDarjeelingDirectPadsGpioGpio26 = 36, /**<  */
  kTopDarjeelingDirectPadsGpioGpio27 = 37, /**<  */
  kTopDarjeelingDirectPadsGpioGpio28 = 38, /**<  */
  kTopDarjeelingDirectPadsGpioGpio29 = 39, /**<  */
  kTopDarjeelingDirectPadsGpioGpio30 = 40, /**<  */
  kTopDarjeelingDirectPadsGpioGpio31 = 41, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSck = 42, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceCsb = 43, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceTpmCsb = 44, /**<  */
  kTopDarjeelingDirectPadsUart0Rx = 45, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi0 = 46, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi1 = 47, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi2 = 48, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi3 = 49, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi4 = 50, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi5 = 51, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi6 = 52, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi7 = 53, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi8 = 54, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi9 = 55, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi10 = 56, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi11 = 57, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sck = 58, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Csb = 59, /**<  */
  kTopDarjeelingDirectPadsUart0Tx = 60, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo0 = 61, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo1 = 62, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo2 = 63, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo3 = 64, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo4 = 65, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo5 = 66, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo6 = 67, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo7 = 68, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo8 = 69, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo9 = 70, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo10 = 71, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo11 = 72, /**<  */
  kTopDarjeelingDirectPadsLast = 72, /**< \internal Last valid direct pad */
} top_darjeeling_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_darjeeling_muxed_pads {
  kTopDarjeelingMuxedPadsMio0 = 0, /**<  */
  kTopDarjeelingMuxedPadsMio1 = 1, /**<  */
  kTopDarjeelingMuxedPadsMio2 = 2, /**<  */
  kTopDarjeelingMuxedPadsMio3 = 3, /**<  */
  kTopDarjeelingMuxedPadsMio4 = 4, /**<  */
  kTopDarjeelingMuxedPadsMio5 = 5, /**<  */
  kTopDarjeelingMuxedPadsMio6 = 6, /**<  */
  kTopDarjeelingMuxedPadsMio7 = 7, /**<  */
  kTopDarjeelingMuxedPadsMio8 = 8, /**<  */
  kTopDarjeelingMuxedPadsMio9 = 9, /**<  */
  kTopDarjeelingMuxedPadsMio10 = 10, /**<  */
  kTopDarjeelingMuxedPadsMio11 = 11, /**<  */
  kTopDarjeelingMuxedPadsLast = 11, /**< \internal Last valid muxed pad */
} top_darjeeling_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_darjeeling_power_manager_wake_ups {
  kTopDarjeelingPowerManagerWakeUpsPinmuxAonPinWkupReq = 0, /**<  */
  kTopDarjeelingPowerManagerWakeUpsAonTimerAonWkupReq = 1, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSensorCtrlWkupReq = 2, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSocProxyWkupInternalReq = 3, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSocProxyWkupExternalReq = 4, /**<  */
  kTopDarjeelingPowerManagerWakeUpsLast = 4, /**< \internal Last valid pwrmgr wakeup signal */
} top_darjeeling_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_darjeeling_reset_manager_sw_resets {
  kTopDarjeelingResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopDarjeelingResetManagerSwResetsSpiHost0 = 1, /**<  */
  kTopDarjeelingResetManagerSwResetsI2c0 = 2, /**<  */
  kTopDarjeelingResetManagerSwResetsLast = 2, /**< \internal Last valid rstmgr software reset request */
} top_darjeeling_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_darjeeling_power_manager_reset_requests {
  kTopDarjeelingPowerManagerResetRequestsAonTimerAonAonTimerRstReq = 0, /**<  */
  kTopDarjeelingPowerManagerResetRequestsSocProxyRstReqExternal = 1, /**<  */
  kTopDarjeelingPowerManagerResetRequestsLast = 1, /**< \internal Last valid pwrmgr reset_request signal */
} top_darjeeling_power_manager_reset_requests_t;

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
typedef enum top_darjeeling_gateable_clocks {
  kTopDarjeelingGateableClocksIoDiv4Peri = 0, /**< Clock clk_io_div4_peri in group peri */
  kTopDarjeelingGateableClocksIoDiv2Peri = 1, /**< Clock clk_io_div2_peri in group peri */
  kTopDarjeelingGateableClocksUsbPeri = 2, /**< Clock clk_usb_peri in group peri */
  kTopDarjeelingGateableClocksLast = 2, /**< \internal Last Valid Gateable Clock */
} top_darjeeling_gateable_clocks_t;

/**
 * Clock Manager Software-Hinted Clocks.
 *
 * The Software has partial control over these clocks. It can ask them to stop,
 * but the clock manager is in control of whether the clock actually is stopped.
 */
typedef enum top_darjeeling_hintable_clocks {
  kTopDarjeelingHintableClocksMainAes = 0, /**< Clock clk_main_aes in group trans */
  kTopDarjeelingHintableClocksMainHmac = 1, /**< Clock clk_main_hmac in group trans */
  kTopDarjeelingHintableClocksMainKmac = 2, /**< Clock clk_main_kmac in group trans */
  kTopDarjeelingHintableClocksMainOtbn = 3, /**< Clock clk_main_otbn in group trans */
  kTopDarjeelingHintableClocksLast = 3, /**< \internal Last Valid Hintable Clock */
} top_darjeeling_hintable_clocks_t;

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_
