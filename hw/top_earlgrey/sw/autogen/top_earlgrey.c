// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
const top_earlgrey_plic_peripheral_t
    top_earlgrey_plic_interrupt_for_peripheral[84] = {
  [kTopEarlgreyPlicIrqIdNone] = kTopEarlgreyPlicPeripheralUnknown,
  [kTopEarlgreyPlicIrqIdGpioGpio0] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio1] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio2] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio3] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio4] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio5] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio6] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio7] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio8] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio9] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio10] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio11] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio12] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio13] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio14] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio15] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio16] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio17] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio18] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio19] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio20] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio21] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio22] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio23] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio24] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio25] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio26] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio27] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio28] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio29] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio30] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdGpioGpio31] = kTopEarlgreyPlicPeripheralGpio,
  [kTopEarlgreyPlicIrqIdUartTxWatermark] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartRxWatermark] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartTxEmpty] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartRxOverflow] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartRxFrameErr] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartRxBreakErr] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartRxTimeout] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdUartRxParityErr] = kTopEarlgreyPlicPeripheralUart,
  [kTopEarlgreyPlicIrqIdSpiDeviceRxf] = kTopEarlgreyPlicPeripheralSpiDevice,
  [kTopEarlgreyPlicIrqIdSpiDeviceRxlvl] = kTopEarlgreyPlicPeripheralSpiDevice,
  [kTopEarlgreyPlicIrqIdSpiDeviceTxlvl] = kTopEarlgreyPlicPeripheralSpiDevice,
  [kTopEarlgreyPlicIrqIdSpiDeviceRxerr] = kTopEarlgreyPlicPeripheralSpiDevice,
  [kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow] = kTopEarlgreyPlicPeripheralSpiDevice,
  [kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow] = kTopEarlgreyPlicPeripheralSpiDevice,
  [kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty] = kTopEarlgreyPlicPeripheralFlashCtrl,
  [kTopEarlgreyPlicIrqIdFlashCtrlProgLvl] = kTopEarlgreyPlicPeripheralFlashCtrl,
  [kTopEarlgreyPlicIrqIdFlashCtrlRdFull] = kTopEarlgreyPlicPeripheralFlashCtrl,
  [kTopEarlgreyPlicIrqIdFlashCtrlRdLvl] = kTopEarlgreyPlicPeripheralFlashCtrl,
  [kTopEarlgreyPlicIrqIdFlashCtrlOpDone] = kTopEarlgreyPlicPeripheralFlashCtrl,
  [kTopEarlgreyPlicIrqIdFlashCtrlOpError] = kTopEarlgreyPlicPeripheralFlashCtrl,
  [kTopEarlgreyPlicIrqIdHmacHmacDone] = kTopEarlgreyPlicPeripheralHmac,
  [kTopEarlgreyPlicIrqIdHmacFifoEmpty] = kTopEarlgreyPlicPeripheralHmac,
  [kTopEarlgreyPlicIrqIdHmacHmacErr] = kTopEarlgreyPlicPeripheralHmac,
  [kTopEarlgreyPlicIrqIdAlertHandlerClassa] = kTopEarlgreyPlicPeripheralAlertHandler,
  [kTopEarlgreyPlicIrqIdAlertHandlerClassb] = kTopEarlgreyPlicPeripheralAlertHandler,
  [kTopEarlgreyPlicIrqIdAlertHandlerClassc] = kTopEarlgreyPlicPeripheralAlertHandler,
  [kTopEarlgreyPlicIrqIdAlertHandlerClassd] = kTopEarlgreyPlicPeripheralAlertHandler,
  [kTopEarlgreyPlicIrqIdNmiGenEsc0] = kTopEarlgreyPlicPeripheralNmiGen,
  [kTopEarlgreyPlicIrqIdNmiGenEsc1] = kTopEarlgreyPlicPeripheralNmiGen,
  [kTopEarlgreyPlicIrqIdNmiGenEsc2] = kTopEarlgreyPlicPeripheralNmiGen,
  [kTopEarlgreyPlicIrqIdUsbdevPktReceived] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevPktSent] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevDisconnected] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevHostLost] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevLinkReset] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevLinkSuspend] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevLinkResume] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevAvEmpty] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevRxFull] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevAvOverflow] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevLinkInErr] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevRxCrcErr] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevRxPidErr] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevRxBitstuffErr] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevFrame] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdUsbdevConnected] = kTopEarlgreyPlicPeripheralUsbdev,
  [kTopEarlgreyPlicIrqIdPwrmgrWakeup] = kTopEarlgreyPlicPeripheralPwrmgr,
  [kTopEarlgreyPlicIrqIdOtbnDone] = kTopEarlgreyPlicPeripheralOtbn,
  [kTopEarlgreyPlicIrqIdOtbnErr] = kTopEarlgreyPlicPeripheralOtbn,
  [kTopEarlgreyPlicIrqIdKeymgrOpDone] = kTopEarlgreyPlicPeripheralKeymgr,
  [kTopEarlgreyPlicIrqIdKeymgrErr] = kTopEarlgreyPlicPeripheralKeymgr,
};


/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_alert_id_t` to
 * `top_earlgrey_alert_peripheral_t`.
 */
const top_earlgrey_alert_peripheral_t
    top_earlgrey_alert_for_peripheral[15] = {
  [kTopEarlgreyAlertIdAesCtrlErrUpdate] = kTopEarlgreyAlertPeripheralAes,
  [kTopEarlgreyAlertIdAesCtrlErrStorage] = kTopEarlgreyAlertPeripheralAes,
  [kTopEarlgreyAlertIdOtbnImemUncorrectable] = kTopEarlgreyAlertPeripheralOtbn,
  [kTopEarlgreyAlertIdOtbnDmemUncorrectable] = kTopEarlgreyAlertPeripheralOtbn,
  [kTopEarlgreyAlertIdOtbnRegUncorrectable] = kTopEarlgreyAlertPeripheralOtbn,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts0] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts1] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts2] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts3] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts4] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts5] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdSensorCtrlAstAlerts6] = kTopEarlgreyAlertPeripheralSensorCtrl,
  [kTopEarlgreyAlertIdKeymgrErr] = kTopEarlgreyAlertPeripheralKeymgr,
  [kTopEarlgreyAlertIdOtpCtrlOtpMacroFailure] = kTopEarlgreyAlertPeripheralOtpCtrl,
  [kTopEarlgreyAlertIdOtpCtrlOtpCheckFailure] = kTopEarlgreyAlertPeripheralOtpCtrl,
};

