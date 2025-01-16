// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047

package top_darjeeling_soc_mbx_pkg;
  /**
   * Peripheral base address for soc device on mbx0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX0_SOC_BASE_ADDR = 32'h1465000;

  /**
   * Peripheral size in bytes for soc device on mbx0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX0_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX1_SOC_BASE_ADDR = 32'h1465100;

  /**
   * Peripheral size in bytes for soc device on mbx1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX1_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX2_SOC_BASE_ADDR = 32'h1465200;

  /**
   * Peripheral size in bytes for soc device on mbx2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX2_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx3 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX3_SOC_BASE_ADDR = 32'h1465300;

  /**
   * Peripheral size in bytes for soc device on mbx3 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX3_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx4 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX4_SOC_BASE_ADDR = 32'h1465400;

  /**
   * Peripheral size in bytes for soc device on mbx4 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX4_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx5 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX5_SOC_BASE_ADDR = 32'h1465500;

  /**
   * Peripheral size in bytes for soc device on mbx5 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX5_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx6 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX6_SOC_BASE_ADDR = 32'h1465600;

  /**
   * Peripheral size in bytes for soc device on mbx6 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX6_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx_pcie0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR = 32'h1460100;

  /**
   * Peripheral size in bytes for soc device on mbx_pcie0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE0_SOC_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for soc device on mbx_pcie1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR = 32'h1460200;

  /**
   * Peripheral size in bytes for soc device on mbx_pcie1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_PCIE1_SOC_SIZE_BYTES = 32'h20;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopDarjeelingAlertPeripheralUart0 = 0,
    TopDarjeelingAlertPeripheralGpio = 1,
    TopDarjeelingAlertPeripheralSpiDevice = 2,
    TopDarjeelingAlertPeripheralI2c0 = 3,
    TopDarjeelingAlertPeripheralRvTimer = 4,
    TopDarjeelingAlertPeripheralOtpCtrl = 5,
    TopDarjeelingAlertPeripheralLcCtrl = 6,
    TopDarjeelingAlertPeripheralSpiHost0 = 7,
    TopDarjeelingAlertPeripheralPwrmgrAon = 8,
    TopDarjeelingAlertPeripheralRstmgrAon = 9,
    TopDarjeelingAlertPeripheralClkmgrAon = 10,
    TopDarjeelingAlertPeripheralPinmuxAon = 11,
    TopDarjeelingAlertPeripheralAonTimerAon = 12,
    TopDarjeelingAlertPeripheralSensorCtrl = 13,
    TopDarjeelingAlertPeripheralSocProxy = 14,
    TopDarjeelingAlertPeripheralSramCtrlRetAon = 15,
    TopDarjeelingAlertPeripheralRvDm = 16,
    TopDarjeelingAlertPeripheralRvPlic = 17,
    TopDarjeelingAlertPeripheralAes = 18,
    TopDarjeelingAlertPeripheralHmac = 19,
    TopDarjeelingAlertPeripheralKmac = 20,
    TopDarjeelingAlertPeripheralOtbn = 21,
    TopDarjeelingAlertPeripheralKeymgrDpe = 22,
    TopDarjeelingAlertPeripheralCsrng = 23,
    TopDarjeelingAlertPeripheralEdn0 = 24,
    TopDarjeelingAlertPeripheralEdn1 = 25,
    TopDarjeelingAlertPeripheralSramCtrlMain = 26,
    TopDarjeelingAlertPeripheralSramCtrlMbox = 27,
    TopDarjeelingAlertPeripheralRomCtrl0 = 28,
    TopDarjeelingAlertPeripheralRomCtrl1 = 29,
    TopDarjeelingAlertPeripheralDma = 30,
    TopDarjeelingAlertPeripheralMbx0 = 31,
    TopDarjeelingAlertPeripheralMbx1 = 32,
    TopDarjeelingAlertPeripheralMbx2 = 33,
    TopDarjeelingAlertPeripheralMbx3 = 34,
    TopDarjeelingAlertPeripheralMbx4 = 35,
    TopDarjeelingAlertPeripheralMbx5 = 36,
    TopDarjeelingAlertPeripheralMbx6 = 37,
    TopDarjeelingAlertPeripheralMbxJtag = 38,
    TopDarjeelingAlertPeripheralMbxPcie0 = 39,
    TopDarjeelingAlertPeripheralMbxPcie1 = 40,
    TopDarjeelingAlertPeripheralSocDbgCtrl = 41,
    TopDarjeelingAlertPeripheralRvCoreIbex = 42,
    TopDarjeelingAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopDarjeelingAlertIdUart0FatalFault = 0,
    TopDarjeelingAlertIdGpioFatalFault = 1,
    TopDarjeelingAlertIdSpiDeviceFatalFault = 2,
    TopDarjeelingAlertIdI2c0FatalFault = 3,
    TopDarjeelingAlertIdRvTimerFatalFault = 4,
    TopDarjeelingAlertIdOtpCtrlFatalMacroError = 5,
    TopDarjeelingAlertIdOtpCtrlFatalCheckError = 6,
    TopDarjeelingAlertIdOtpCtrlFatalBusIntegError = 7,
    TopDarjeelingAlertIdOtpCtrlFatalPrimOtpAlert = 8,
    TopDarjeelingAlertIdOtpCtrlRecovPrimOtpAlert = 9,
    TopDarjeelingAlertIdLcCtrlFatalProgError = 10,
    TopDarjeelingAlertIdLcCtrlFatalStateError = 11,
    TopDarjeelingAlertIdLcCtrlFatalBusIntegError = 12,
    TopDarjeelingAlertIdSpiHost0FatalFault = 13,
    TopDarjeelingAlertIdPwrmgrAonFatalFault = 14,
    TopDarjeelingAlertIdRstmgrAonFatalFault = 15,
    TopDarjeelingAlertIdRstmgrAonFatalCnstyFault = 16,
    TopDarjeelingAlertIdClkmgrAonRecovFault = 17,
    TopDarjeelingAlertIdClkmgrAonFatalFault = 18,
    TopDarjeelingAlertIdPinmuxAonFatalFault = 19,
    TopDarjeelingAlertIdAonTimerAonFatalFault = 20,
    TopDarjeelingAlertIdSensorCtrlRecovAlert = 21,
    TopDarjeelingAlertIdSensorCtrlFatalAlert = 22,
    TopDarjeelingAlertIdSocProxyFatalAlertIntg = 23,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal0 = 24,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal1 = 25,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal2 = 26,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal3 = 27,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal4 = 28,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal5 = 29,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal6 = 30,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal7 = 31,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal8 = 32,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal9 = 33,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal10 = 34,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal11 = 35,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal12 = 36,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal13 = 37,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal14 = 38,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal15 = 39,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal16 = 40,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal17 = 41,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal18 = 42,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal19 = 43,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal20 = 44,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal21 = 45,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal22 = 46,
    TopDarjeelingAlertIdSocProxyFatalAlertExternal23 = 47,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal0 = 48,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal1 = 49,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal2 = 50,
    TopDarjeelingAlertIdSocProxyRecovAlertExternal3 = 51,
    TopDarjeelingAlertIdSramCtrlRetAonFatalError = 52,
    TopDarjeelingAlertIdRvDmFatalFault = 53,
    TopDarjeelingAlertIdRvPlicFatalFault = 54,
    TopDarjeelingAlertIdAesRecovCtrlUpdateErr = 55,
    TopDarjeelingAlertIdAesFatalFault = 56,
    TopDarjeelingAlertIdHmacFatalFault = 57,
    TopDarjeelingAlertIdKmacRecovOperationErr = 58,
    TopDarjeelingAlertIdKmacFatalFaultErr = 59,
    TopDarjeelingAlertIdOtbnFatal = 60,
    TopDarjeelingAlertIdOtbnRecov = 61,
    TopDarjeelingAlertIdKeymgrDpeRecovOperationErr = 62,
    TopDarjeelingAlertIdKeymgrDpeFatalFaultErr = 63,
    TopDarjeelingAlertIdCsrngRecovAlert = 64,
    TopDarjeelingAlertIdCsrngFatalAlert = 65,
    TopDarjeelingAlertIdEdn0RecovAlert = 66,
    TopDarjeelingAlertIdEdn0FatalAlert = 67,
    TopDarjeelingAlertIdEdn1RecovAlert = 68,
    TopDarjeelingAlertIdEdn1FatalAlert = 69,
    TopDarjeelingAlertIdSramCtrlMainFatalError = 70,
    TopDarjeelingAlertIdSramCtrlMboxFatalError = 71,
    TopDarjeelingAlertIdRomCtrl0Fatal = 72,
    TopDarjeelingAlertIdRomCtrl1Fatal = 73,
    TopDarjeelingAlertIdDmaFatalFault = 74,
    TopDarjeelingAlertIdMbx0FatalFault = 75,
    TopDarjeelingAlertIdMbx0RecovFault = 76,
    TopDarjeelingAlertIdMbx1FatalFault = 77,
    TopDarjeelingAlertIdMbx1RecovFault = 78,
    TopDarjeelingAlertIdMbx2FatalFault = 79,
    TopDarjeelingAlertIdMbx2RecovFault = 80,
    TopDarjeelingAlertIdMbx3FatalFault = 81,
    TopDarjeelingAlertIdMbx3RecovFault = 82,
    TopDarjeelingAlertIdMbx4FatalFault = 83,
    TopDarjeelingAlertIdMbx4RecovFault = 84,
    TopDarjeelingAlertIdMbx5FatalFault = 85,
    TopDarjeelingAlertIdMbx5RecovFault = 86,
    TopDarjeelingAlertIdMbx6FatalFault = 87,
    TopDarjeelingAlertIdMbx6RecovFault = 88,
    TopDarjeelingAlertIdMbxJtagFatalFault = 89,
    TopDarjeelingAlertIdMbxJtagRecovFault = 90,
    TopDarjeelingAlertIdMbxPcie0FatalFault = 91,
    TopDarjeelingAlertIdMbxPcie0RecovFault = 92,
    TopDarjeelingAlertIdMbxPcie1FatalFault = 93,
    TopDarjeelingAlertIdMbxPcie1RecovFault = 94,
    TopDarjeelingAlertIdSocDbgCtrlFatalFault = 95,
    TopDarjeelingAlertIdSocDbgCtrlRecovCtrlUpdateErr = 96,
    TopDarjeelingAlertIdRvCoreIbexFatalSwErr = 97,
    TopDarjeelingAlertIdRvCoreIbexRecovSwErr = 98,
    TopDarjeelingAlertIdRvCoreIbexFatalHwErr = 99,
    TopDarjeelingAlertIdRvCoreIbexRecovHwErr = 100,
    TopDarjeelingAlertIdCount
  } alert_id_e;

  // Enumeration of IO power domains.
  // Only used in ASIC target.
  typedef enum logic [0:0] {
    IoBankVio = 0,
    IoBankCount = 1
  } pwr_dom_e;

  // Enumeration for MIO signals on the top-level.
  typedef enum int unsigned {
    MioInSocProxySocGpi12 = 0,
    MioInSocProxySocGpi13 = 1,
    MioInSocProxySocGpi14 = 2,
    MioInSocProxySocGpi15 = 3,
    MioInCount = 4
  } mio_in_e;

  typedef enum {
    MioOutSocProxySocGpo12 = 0,
    MioOutSocProxySocGpo13 = 1,
    MioOutSocProxySocGpo14 = 2,
    MioOutSocProxySocGpo15 = 3,
    MioOutOtpCtrlTest0 = 4,
    MioOutCount = 5
  } mio_out_e;

  // Enumeration for DIO signals, used on both the top and chip-levels.
  typedef enum int unsigned {
    DioSpiHost0Sd0 = 0,
    DioSpiHost0Sd1 = 1,
    DioSpiHost0Sd2 = 2,
    DioSpiHost0Sd3 = 3,
    DioSpiDeviceSd0 = 4,
    DioSpiDeviceSd1 = 5,
    DioSpiDeviceSd2 = 6,
    DioSpiDeviceSd3 = 7,
    DioI2c0Scl = 8,
    DioI2c0Sda = 9,
    DioGpioGpio0 = 10,
    DioGpioGpio1 = 11,
    DioGpioGpio2 = 12,
    DioGpioGpio3 = 13,
    DioGpioGpio4 = 14,
    DioGpioGpio5 = 15,
    DioGpioGpio6 = 16,
    DioGpioGpio7 = 17,
    DioGpioGpio8 = 18,
    DioGpioGpio9 = 19,
    DioGpioGpio10 = 20,
    DioGpioGpio11 = 21,
    DioGpioGpio12 = 22,
    DioGpioGpio13 = 23,
    DioGpioGpio14 = 24,
    DioGpioGpio15 = 25,
    DioGpioGpio16 = 26,
    DioGpioGpio17 = 27,
    DioGpioGpio18 = 28,
    DioGpioGpio19 = 29,
    DioGpioGpio20 = 30,
    DioGpioGpio21 = 31,
    DioGpioGpio22 = 32,
    DioGpioGpio23 = 33,
    DioGpioGpio24 = 34,
    DioGpioGpio25 = 35,
    DioGpioGpio26 = 36,
    DioGpioGpio27 = 37,
    DioGpioGpio28 = 38,
    DioGpioGpio29 = 39,
    DioGpioGpio30 = 40,
    DioGpioGpio31 = 41,
    DioSpiDeviceSck = 42,
    DioSpiDeviceCsb = 43,
    DioSpiDeviceTpmCsb = 44,
    DioUart0Rx = 45,
    DioSocProxySocGpi0 = 46,
    DioSocProxySocGpi1 = 47,
    DioSocProxySocGpi2 = 48,
    DioSocProxySocGpi3 = 49,
    DioSocProxySocGpi4 = 50,
    DioSocProxySocGpi5 = 51,
    DioSocProxySocGpi6 = 52,
    DioSocProxySocGpi7 = 53,
    DioSocProxySocGpi8 = 54,
    DioSocProxySocGpi9 = 55,
    DioSocProxySocGpi10 = 56,
    DioSocProxySocGpi11 = 57,
    DioSpiHost0Sck = 58,
    DioSpiHost0Csb = 59,
    DioUart0Tx = 60,
    DioSocProxySocGpo0 = 61,
    DioSocProxySocGpo1 = 62,
    DioSocProxySocGpo2 = 63,
    DioSocProxySocGpo3 = 64,
    DioSocProxySocGpo4 = 65,
    DioSocProxySocGpo5 = 66,
    DioSocProxySocGpo6 = 67,
    DioSocProxySocGpo7 = 68,
    DioSocProxySocGpo8 = 69,
    DioSocProxySocGpo9 = 70,
    DioSocProxySocGpo10 = 71,
    DioSocProxySocGpo11 = 72,
    DioCount = 73
  } dio_e;

  // Enumeration for the types of pads.
  typedef enum {
    MioPad,
    DioPad
  } pad_type_e;

  // Raw MIO/DIO input array indices on chip-level.
  // TODO: Does not account for target specific stubbed/added pads.
  // Need to make a target-specific package for those.
  typedef enum int unsigned {
    MioPadMio0 = 0,
    MioPadMio1 = 1,
    MioPadMio2 = 2,
    MioPadMio3 = 3,
    MioPadMio4 = 4,
    MioPadMio5 = 5,
    MioPadMio6 = 6,
    MioPadMio7 = 7,
    MioPadMio8 = 8,
    MioPadMio9 = 9,
    MioPadMio10 = 10,
    MioPadMio11 = 11,
    MioPadCount
  } mio_pad_e;

  typedef enum int unsigned {
    DioPadPorN = 0,
    DioPadJtagTck = 1,
    DioPadJtagTms = 2,
    DioPadJtagTdi = 3,
    DioPadJtagTdo = 4,
    DioPadJtagTrstN = 5,
    DioPadOtpExtVolt = 6,
    DioPadSpiHostD0 = 7,
    DioPadSpiHostD1 = 8,
    DioPadSpiHostD2 = 9,
    DioPadSpiHostD3 = 10,
    DioPadSpiHostClk = 11,
    DioPadSpiHostCsL = 12,
    DioPadSpiDevD0 = 13,
    DioPadSpiDevD1 = 14,
    DioPadSpiDevD2 = 15,
    DioPadSpiDevD3 = 16,
    DioPadSpiDevClk = 17,
    DioPadSpiDevCsL = 18,
    DioPadSpiDevTpmCsL = 19,
    DioPadUartRx = 20,
    DioPadUartTx = 21,
    DioPadI2cScl = 22,
    DioPadI2cSda = 23,
    DioPadGpio0 = 24,
    DioPadGpio1 = 25,
    DioPadGpio2 = 26,
    DioPadGpio3 = 27,
    DioPadGpio4 = 28,
    DioPadGpio5 = 29,
    DioPadGpio6 = 30,
    DioPadGpio7 = 31,
    DioPadGpio8 = 32,
    DioPadGpio9 = 33,
    DioPadGpio10 = 34,
    DioPadGpio11 = 35,
    DioPadGpio12 = 36,
    DioPadGpio13 = 37,
    DioPadGpio14 = 38,
    DioPadGpio15 = 39,
    DioPadGpio16 = 40,
    DioPadGpio17 = 41,
    DioPadGpio18 = 42,
    DioPadGpio19 = 43,
    DioPadGpio20 = 44,
    DioPadGpio21 = 45,
    DioPadGpio22 = 46,
    DioPadGpio23 = 47,
    DioPadGpio24 = 48,
    DioPadGpio25 = 49,
    DioPadGpio26 = 50,
    DioPadGpio27 = 51,
    DioPadGpio28 = 52,
    DioPadGpio29 = 53,
    DioPadGpio30 = 54,
    DioPadGpio31 = 55,
    DioPadSocGpi0 = 56,
    DioPadSocGpi1 = 57,
    DioPadSocGpi2 = 58,
    DioPadSocGpi3 = 59,
    DioPadSocGpi4 = 60,
    DioPadSocGpi5 = 61,
    DioPadSocGpi6 = 62,
    DioPadSocGpi7 = 63,
    DioPadSocGpi8 = 64,
    DioPadSocGpi9 = 65,
    DioPadSocGpi10 = 66,
    DioPadSocGpi11 = 67,
    DioPadSocGpo0 = 68,
    DioPadSocGpo1 = 69,
    DioPadSocGpo2 = 70,
    DioPadSocGpo3 = 71,
    DioPadSocGpo4 = 72,
    DioPadSocGpo5 = 73,
    DioPadSocGpo6 = 74,
    DioPadSocGpo7 = 75,
    DioPadSocGpo8 = 76,
    DioPadSocGpo9 = 77,
    DioPadSocGpo10 = 78,
    DioPadSocGpo11 = 79,
    DioPadCount
  } dio_pad_e;

  // List of peripheral instantiated in this chip.
  typedef enum {
    PeripheralMbx0,
    PeripheralMbx1,
    PeripheralMbx2,
    PeripheralMbx3,
    PeripheralMbx4,
    PeripheralMbx5,
    PeripheralMbx6,
    PeripheralMbxPcie0,
    PeripheralMbxPcie1,
    PeripheralCount
  } peripheral_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

// MACROs for AST analog simulation support
`ifdef ANALOGSIM
  `define INOUT_AI input ast_pkg::awire_t
  `define INOUT_AO output ast_pkg::awire_t
`else
  `define INOUT_AI inout
  `define INOUT_AO inout
`endif

endpackage
