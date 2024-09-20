// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
// -o hw/top_englishbreakfast

#include "hw/top_englishbreakfast/sw/autogen/top_englishbreakfast.h"

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_englishbreakfast_plic_irq_id_t` to
 * `top_englishbreakfast_plic_peripheral_t`.
 */
const top_englishbreakfast_plic_peripheral_t
    top_englishbreakfast_plic_interrupt_for_peripheral[88] = {
  [kTopEnglishbreakfastPlicIrqIdNone] = kTopEnglishbreakfastPlicPeripheralUnknown,
  [kTopEnglishbreakfastPlicIrqIdUart0TxWatermark] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0RxWatermark] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0TxDone] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0RxOverflow] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0RxFrameErr] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0RxBreakErr] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0RxTimeout] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0RxParityErr] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart0TxEmpty] = kTopEnglishbreakfastPlicPeripheralUart0,
  [kTopEnglishbreakfastPlicIrqIdUart1TxWatermark] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1RxWatermark] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1TxDone] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1RxOverflow] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1RxFrameErr] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1RxBreakErr] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1RxTimeout] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1RxParityErr] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdUart1TxEmpty] = kTopEnglishbreakfastPlicPeripheralUart1,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio0] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio1] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio2] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio3] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio4] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio5] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio6] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio7] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio8] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio9] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio10] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio11] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio12] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio13] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio14] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio15] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio16] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio17] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio18] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio19] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio20] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio21] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio22] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio23] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio24] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio25] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio26] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio27] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio28] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio29] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio30] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdGpioGpio31] = kTopEnglishbreakfastPlicPeripheralGpio,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceUploadPayloadNotEmpty] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceUploadPayloadOverflow] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceReadbufWatermark] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceReadbufFlip] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceTpmHeaderNotEmpty] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceTpmRdfifoCmdEnd] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiDeviceTpmRdfifoDrop] = kTopEnglishbreakfastPlicPeripheralSpiDevice,
  [kTopEnglishbreakfastPlicIrqIdSpiHost0Error] = kTopEnglishbreakfastPlicPeripheralSpiHost0,
  [kTopEnglishbreakfastPlicIrqIdSpiHost0SpiEvent] = kTopEnglishbreakfastPlicPeripheralSpiHost0,
  [kTopEnglishbreakfastPlicIrqIdUsbdevPktReceived] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevPktSent] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevDisconnected] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevHostLost] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevLinkReset] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevLinkSuspend] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevLinkResume] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevAvOutEmpty] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevRxFull] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevAvOverflow] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevLinkInErr] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevRxCrcErr] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevRxPidErr] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevRxBitstuffErr] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevFrame] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevPowered] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevLinkOutErr] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdUsbdevAvSetupEmpty] = kTopEnglishbreakfastPlicPeripheralUsbdev,
  [kTopEnglishbreakfastPlicIrqIdPwrmgrAonWakeup] = kTopEnglishbreakfastPlicPeripheralPwrmgrAon,
  [kTopEnglishbreakfastPlicIrqIdAonTimerAonWkupTimerExpired] = kTopEnglishbreakfastPlicPeripheralAonTimerAon,
  [kTopEnglishbreakfastPlicIrqIdAonTimerAonWdogTimerBark] = kTopEnglishbreakfastPlicPeripheralAonTimerAon,
  [kTopEnglishbreakfastPlicIrqIdFlashCtrlProgEmpty] = kTopEnglishbreakfastPlicPeripheralFlashCtrl,
  [kTopEnglishbreakfastPlicIrqIdFlashCtrlProgLvl] = kTopEnglishbreakfastPlicPeripheralFlashCtrl,
  [kTopEnglishbreakfastPlicIrqIdFlashCtrlRdFull] = kTopEnglishbreakfastPlicPeripheralFlashCtrl,
  [kTopEnglishbreakfastPlicIrqIdFlashCtrlRdLvl] = kTopEnglishbreakfastPlicPeripheralFlashCtrl,
  [kTopEnglishbreakfastPlicIrqIdFlashCtrlOpDone] = kTopEnglishbreakfastPlicPeripheralFlashCtrl,
  [kTopEnglishbreakfastPlicIrqIdFlashCtrlCorrErr] = kTopEnglishbreakfastPlicPeripheralFlashCtrl,
};


/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_englishbreakfast_alert_id_t` to
 * `top_englishbreakfast_alert_peripheral_t`.
 */
const top_englishbreakfast_alert_peripheral_t
    top_englishbreakfast_alert_for_peripheral[28] = {
  [kTopEnglishbreakfastAlertIdUart0FatalFault] = kTopEnglishbreakfastAlertPeripheralUart0,
  [kTopEnglishbreakfastAlertIdUart1FatalFault] = kTopEnglishbreakfastAlertPeripheralUart1,
  [kTopEnglishbreakfastAlertIdGpioFatalFault] = kTopEnglishbreakfastAlertPeripheralGpio,
  [kTopEnglishbreakfastAlertIdSpiDeviceFatalFault] = kTopEnglishbreakfastAlertPeripheralSpiDevice,
  [kTopEnglishbreakfastAlertIdSpiHost0FatalFault] = kTopEnglishbreakfastAlertPeripheralSpiHost0,
  [kTopEnglishbreakfastAlertIdRvTimerFatalFault] = kTopEnglishbreakfastAlertPeripheralRvTimer,
  [kTopEnglishbreakfastAlertIdUsbdevFatalFault] = kTopEnglishbreakfastAlertPeripheralUsbdev,
  [kTopEnglishbreakfastAlertIdPwrmgrAonFatalFault] = kTopEnglishbreakfastAlertPeripheralPwrmgrAon,
  [kTopEnglishbreakfastAlertIdRstmgrAonFatalFault] = kTopEnglishbreakfastAlertPeripheralRstmgrAon,
  [kTopEnglishbreakfastAlertIdRstmgrAonFatalCnstyFault] = kTopEnglishbreakfastAlertPeripheralRstmgrAon,
  [kTopEnglishbreakfastAlertIdClkmgrAonRecovFault] = kTopEnglishbreakfastAlertPeripheralClkmgrAon,
  [kTopEnglishbreakfastAlertIdClkmgrAonFatalFault] = kTopEnglishbreakfastAlertPeripheralClkmgrAon,
  [kTopEnglishbreakfastAlertIdPinmuxAonFatalFault] = kTopEnglishbreakfastAlertPeripheralPinmuxAon,
  [kTopEnglishbreakfastAlertIdAonTimerAonFatalFault] = kTopEnglishbreakfastAlertPeripheralAonTimerAon,
  [kTopEnglishbreakfastAlertIdFlashCtrlRecovErr] = kTopEnglishbreakfastAlertPeripheralFlashCtrl,
  [kTopEnglishbreakfastAlertIdFlashCtrlFatalStdErr] = kTopEnglishbreakfastAlertPeripheralFlashCtrl,
  [kTopEnglishbreakfastAlertIdFlashCtrlFatalErr] = kTopEnglishbreakfastAlertPeripheralFlashCtrl,
  [kTopEnglishbreakfastAlertIdFlashCtrlFatalPrimFlashAlert] = kTopEnglishbreakfastAlertPeripheralFlashCtrl,
  [kTopEnglishbreakfastAlertIdFlashCtrlRecovPrimFlashAlert] = kTopEnglishbreakfastAlertPeripheralFlashCtrl,
  [kTopEnglishbreakfastAlertIdRvPlicFatalFault] = kTopEnglishbreakfastAlertPeripheralRvPlic,
  [kTopEnglishbreakfastAlertIdAesRecovCtrlUpdateErr] = kTopEnglishbreakfastAlertPeripheralAes,
  [kTopEnglishbreakfastAlertIdAesFatalFault] = kTopEnglishbreakfastAlertPeripheralAes,
  [kTopEnglishbreakfastAlertIdSramCtrlMainFatalError] = kTopEnglishbreakfastAlertPeripheralSramCtrlMain,
  [kTopEnglishbreakfastAlertIdRomCtrlFatal] = kTopEnglishbreakfastAlertPeripheralRomCtrl,
  [kTopEnglishbreakfastAlertIdRvCoreIbexFatalSwErr] = kTopEnglishbreakfastAlertPeripheralRvCoreIbex,
  [kTopEnglishbreakfastAlertIdRvCoreIbexRecovSwErr] = kTopEnglishbreakfastAlertPeripheralRvCoreIbex,
  [kTopEnglishbreakfastAlertIdRvCoreIbexFatalHwErr] = kTopEnglishbreakfastAlertPeripheralRvCoreIbex,
  [kTopEnglishbreakfastAlertIdRvCoreIbexRecovHwErr] = kTopEnglishbreakfastAlertPeripheralRvCoreIbex,
};
