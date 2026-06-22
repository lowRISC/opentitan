// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_ALERT_FI_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_ALERT_FI_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

/**
 * Alert Trigger FI test.
 *
 * Trigger a specified alert test from a hardware and get the reaction from the
 * chip.
 *
 * AES: recoverable and fatal alerts related to control updates and general
 * faults.
 *  - RecovCtrlUpdateErr [Case 0]
 *  - FatalFault [Case 1]
 * AON_TIMER: a fatal fault alert.
 *  - FatalFault [Case 2]
 * CLKMGR: recoverable and fatal clock manager faults.
 *  - RecovFault [Case 3]
 *  - FatalFault [Case 4]
 * CSRNG: recoverable and fatal alerts for the Continuous Self-Test Random
 * Number Generator.
 *  - RecovAlert [Case 5]
 *  - FatalAlert [Case 6]
 * EDN: recoverable and fatal alerts for the Entropy Distribution Network (EDN0
 * and EDN1).
 *  - EDN0 RecovAlert [Case 7]
 *  - EDN0 FatalAlert [Case 8]
 *  - EDN1 RecovAlert [Case 9]
 *  - EDN1 FatalAlert [Case 10]
 * ENTROPY_SRC: recoverable and fatal alerts for the Entropy Source.
 *  - RecovAlert [Case 11]
 *  - FatalAlert [Case 12]
 * FLASH_CTRL: various recoverable and fatal errors and alerts related to flash
 * control.
 *  - RecovErr [Case 13]
 *  - FatalStdErr [Case 14]
 *  - FatalErr [Case 15]
 *  - FatalPrimFlashAlert [Case 16]
 *  - RecovPrimFlashAlert [Case 17]
 * GPIO: a fatal fault alert.
 *  - FatalFault [Case 18]
 * HMAC: a fatal fault alert.
 *  - FatalFault [Case 19]
 * I2C: a fatal fault alert (I2C0, I2C1, and I2C2).
 *  - I2C0 FatalFault [Case 20]
 *  - I2C1 FatalFault [Case 21]
 *  - I2C2 FatalFault [Case 22]
 * KEYMGR: recoverable and fatal key manager errors.
 *  - RecovOperationErr [Case 23]
 *  - FatalFaultErr [Case 24]
 * KMAC: recoverable and fatal KMAC errors.
 *  - RecovOperationErr [Case 25]
 *  - FatalFaultErr [Case 26]
 * LC_CTRL: fatal programming, state, and bus integrity errors for the lifecycle
 * controller.
 *  - FatalProgError [Case 27]
 *  - FatalStateError [Case 28]
 *  - FatalBusIntegError [Case 29]
 * OTBN: recoverable and fatal alerts for the OpenTitan Big Number accelerator.
 *  - FatalAlert [Case 30]
 *  - RecovAlert [Case 30]
 * OTP_CTRL: fatal macro, check, bus integrity errors, and primary OTP alerts
 * (both fatal and recoverable).
 *  - FatalMacroError [Case 31]
 *  - FatalCheckError [Case 32]
 *  - FatalBusIntegError [Case 33]
 *  - FatalPrimOtpAlert [Case 34]
 *  - RecovPrimOtpAlert [Case 35]
 * PINMUX: a fatal fault alert.
 *  - FatalFault [Case 36]
 * PWRMGR: a fatal fault alert.
 *  - FatalFault [Case 37]
 * ROM_CTRL: a fatal alert.
 *  - Fatal [Case 38]
 * RSTMGR: fatal faults and consistency faults for the reset manager.
 *  - FatalFault [Case 39]
 *  - FatalCnstyFault [Case 40]
 * RV_CORE_IBEX: recoverable and fatal software and hardware errors for the Ibex
 * core.
 *  - FatalSwErr [Case 41]
 *  - RecovSwErr [Case 42]
 *  - FatalHwErr [Case 43]
 *  - RecovHwErr [Case 44]
 * RV_PLIC: a fatal fault for the Platform-Level Interrupt Controller.
 *  - FatalFault [Case 45]
 * RV_TIMER: a fatal fault.
 *  - FatalFault [Case 46]
 * SENSOR_CTRL: recoverable and fatal sensor controller alerts.
 *  - RecovAlert [Case 47]
 *  - FatalAlert [Case 48]
 * SPI_DEVICE: a fatal fault for the SPI device.
 *  - FatalFault [Case 49]
 * SPI_HOST: a fatal fault for the SPI host (SPI_HOST0 and SPI_HOST1).
 *  - SPI_HOST0 FatalFault [Case 50]
 *  - SPI_HOST1 FatalFault [Case 51]
 * SRAM_CTRL: a fatal error for both main and retention SRAM controllers.
 *  - Main SRAM FatalError [Case 52]
 *  - Retention SRAM FatalError [Case 53]
 * SYSRST_CTRL: a fatal fault for the system reset controller.
 *  - FatalFault [Case 54]
 * UART: a fatal fault (UART0, UART1, UART2, and UART3).
 *  - UART0 FatalFault [Case 55]
 *  - UART1 FatalFault [Case 56]
 *  - UART2 FatalFault [Case 57]
 *  - UART3 FatalFault [Case 58]
 * USBDEV: a fatal fault for the USB device controller.
 *  - FatalFault [Case 59]
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_alert_fi_trigger(ujson_t *uj);

/**
 * Alert FI sensor control trigger test.
 *
 * Writes to the ALERT_TRIG register in the sensor control.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_alert_fi_sensor_ctrl_trigger(ujson_t *uj);

/**
 * Alert FI ibex sw fatal write.
 *
 * Writes to the sw fatal fault register.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_alert_fi_ibex_sw_fatal(ujson_t *uj);

/**
 * Alert FI command handler.
 *
 * Command handler for the Alert FI command.
 *
 * @param uj An initialized uJSON context.
 * @return OK or error.
 */
status_t handle_alert_fi(ujson_t *uj);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_FI_ALERT_FI_H_
