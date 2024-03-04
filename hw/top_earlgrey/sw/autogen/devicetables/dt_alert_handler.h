// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_ALERT_HANDLER_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_ALERT_HANDLER_H_

#include "sw/device/lib/devicetables/dt.h"
#include <stdint.h>

typedef enum {
  kDtAlertHandlerRegBlockCore = 0,
  kDtAlertHandlerRegBlockCount = 1,
} dt_alert_handler_reg_block_t;

typedef enum {
  kDtAlertHandlerIrqTypeClassa = 0,
  kDtAlertHandlerIrqTypeClassb = 1,
  kDtAlertHandlerIrqTypeClassc = 2,
  kDtAlertHandlerIrqTypeClassd = 3,
  kDtAlertHandlerIrqTypeCount = 4,
} dt_alert_handler_irq_type_t;

typedef enum {
  kDtAlertHandlerClockClk = 0,
  kDtAlertHandlerClockEdn = 1,
  kDtAlertHandlerClockCount = 2,
} dt_alert_handler_clock_t;

typedef enum {
  kDtAlertHandlerPinctrlInputCount = 0,
  kDtAlertHandlerPinctrlOutputCount = 0,
} dt_alert_handler_pinctrl_t;

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_DEVICETABLES_DT_ALERT_HANDLER_H_
