// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/shutdown.h"

#include <assert.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/log.h"

#include "alert_handler_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"
#include "lc_ctrl_regs.h"
#include "otp_ctrl_regs.h"
#include "rv_core_ibex_regs.h"
#include "sram_ctrl_regs.h"

static_assert(ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT <=
                  OTP_CTRL_PARAM_ROM_ALERT_CLASSIFICATION_SIZE / 4,
              "More alerts than alert classification OTP words!");
static_assert(ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT <=
                  OTP_CTRL_PARAM_ROM_LOCAL_ALERT_CLASSIFICATION_SIZE / 4,
              "More local alerts than local alert classification OTP words!");

#define NO_MODIFIERS

#ifdef OT_OFF_TARGET_TEST
// If we're building as a unit test, rename the shutdown functions so they
// can be mocked and/or tested individually.
// The unmodified function name will be declared as `extern` so the test
// program can supply its own implementation.  The implementation present
// in this file will be named `unmocked_${name}` so the test program can
// invoke it for testing.
#define SHUTDOWN_FUNC(modifiers_, name_) \
  extern void name_;                     \
  void unmocked_##name_
#else
#define SHUTDOWN_FUNC(modifiers_, name_) \
  static ALWAYS_INLINE modifiers_ void name_
#endif

// Convert the alert class to an index.
// This is required because I expect to change the constant definitions in
// alert_class_t to have reasonable hamming distances.
static size_t clsindex(alert_class_t cls) {
  switch (cls) {
    case kAlertClassA:
      return 0;
    case kAlertClassB:
      return 1;
    case kAlertClassC:
      return 2;
    case kAlertClassD:
      return 3;
    default:
      return 0;
  }
}

rom_error_t shutdown_init(lifecycle_state_t lc_state) {
  // Are we in a lifecycle state which needs alert configuration?
  uint32_t lc_shift;
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      // Don't configure alerts during manufacturing as OTP may not have been
      // programmed yet.
      return kErrorOk;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      lc_shift = 0;
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      lc_shift = 8;
      break;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      lc_shift = 16;
      break;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      lc_shift = 24;
      break;
    default:
      HARDENED_UNREACHABLE();
  }

  // Get the enable and escalation settings for all four alert classes.
  // Each of these OTP words is composed of 4 byte enums with the enable and
  // escalate configs per alert class (a/b/c/d).
  uint32_t class_enable = otp_read32(OTP_CTRL_PARAM_ROM_ALERT_CLASS_EN_OFFSET);
  uint32_t class_escalate =
      otp_read32(OTP_CTRL_PARAM_ROM_ALERT_ESCALATION_OFFSET);
  alert_enable_t enable[ALERT_CLASSES];
  alert_escalate_t escalate[ALERT_CLASSES];
  for (size_t i = 0; i < ALERT_CLASSES; ++i) {
    enable[i] = (alert_enable_t)bitfield_field32_read(
        class_enable, (bitfield_field32_t){.mask = 0xff, .index = i * 8});
    escalate[i] = (alert_escalate_t)bitfield_field32_read(
        class_escalate, (bitfield_field32_t){.mask = 0xff, .index = i * 8});
  }

  // For each alert, read its corresponding OTP word and extract the class
  // configuration for the current lifecycle state.
  rom_error_t error = kErrorOk;
  for (size_t i = 0; i < ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    uint32_t value = otp_read32(OTP_CTRL_PARAM_ROM_ALERT_CLASSIFICATION_OFFSET +
                                i * sizeof(uint32_t));
    alert_class_t cls = (alert_class_t)bitfield_field32_read(
        value, (bitfield_field32_t){.mask = 0xff, .index = lc_shift});
    rom_error_t e = alert_configure(i, cls, enable[clsindex(cls)]);
    if (e != kErrorOk) {
      // Keep going if there is an error programming one alert.  We want to
      // program them all.
      error = e;
    }
  }

  // For each local alert, read its corresponding OTP word and extract the class
  // configuration for the current lifecycle state.
  for (size_t i = 0; i < ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT;
       ++i) {
    uint32_t value =
        otp_read32(OTP_CTRL_PARAM_ROM_LOCAL_ALERT_CLASSIFICATION_OFFSET +
                   i * sizeof(uint32_t));
    alert_class_t cls = (alert_class_t)bitfield_field32_read(
        value, (bitfield_field32_t){.mask = 0xff, .index = lc_shift});
    rom_error_t e = alert_local_configure(i, cls, enable[clsindex(cls)]);
    if (e != kErrorOk) {
      // Keep going if there is an error programming one alert.  We want to
      // program them all.
      error = e;
    }
  }

  // For each alert class, configure the various escalation parameters.
  const alert_class_t kClasses[] = {
      kAlertClassA,
      kAlertClassB,
      kAlertClassC,
      kAlertClassD,
  };
  alert_class_config_t config;
  for (size_t i = 0; i < ALERT_CLASSES; ++i) {
    config.enabled = enable[i];
    config.escalation = escalate[i];
    config.accum_threshold = otp_read32(
        OTP_CTRL_PARAM_ROM_ALERT_ACCUM_THRESH_OFFSET + i * sizeof(uint32_t));
    config.timeout_cycles = otp_read32(
        OTP_CTRL_PARAM_ROM_ALERT_TIMEOUT_CYCLES_OFFSET + i * sizeof(uint32_t));
    for (size_t phase = 0; phase < ARRAYSIZE(config.phase_cycles); ++phase) {
      config.phase_cycles[phase] = otp_read32(
          OTP_CTRL_PARAM_ROM_ALERT_PHASE_CYCLES_OFFSET +
          (i * ARRAYSIZE(config.phase_cycles) + phase) * sizeof(uint32_t));
    }

    rom_error_t e = alert_class_configure(kClasses[i], &config);
    if (e != kErrorOk) {
      // Keep going if there is an error programming an alert class. We want to
      // program them all.
      error = e;
    }
  }
  return error;
}

/**
 * Implementation of `shutdown_redact` that is guaranteed to be inlined.
 *
 * This function must be inlined because it is called from `shutdown_finalize`.
 */
static ALWAYS_INLINE uint32_t
shutdown_redact_inline(rom_error_t reason, shutdown_error_redact_t severity) {
  uint32_t redacted = (uint32_t)reason;
  if (reason == kErrorOk) {
    return 0;
  }
  switch (severity) {
    case kShutdownErrorRedactModule:
      redacted = bitfield_field32_write(redacted, ROM_ERROR_FIELD_MODULE, 0);
      FALLTHROUGH_INTENDED;
    case kShutdownErrorRedactError:
      redacted = bitfield_field32_write(redacted, ROM_ERROR_FIELD_ERROR, 0);
      FALLTHROUGH_INTENDED;
    case kShutdownErrorRedactNone:
      break;
    case kShutdownErrorRedactAll:
      FALLTHROUGH_INTENDED;
    default:
      redacted = kErrorUnknown;
  }
  return redacted;
}

uint32_t shutdown_redact(rom_error_t reason, shutdown_error_redact_t severity) {
  return shutdown_redact_inline(reason, severity);
}

/**
 * Implementation of `shutdown_redact_policy` that is guaranteed to be inlined.
 *
 * This function must be inlined because it is called from `shutdown_finalize`.
 */
static ALWAYS_INLINE shutdown_error_redact_t
shutdown_redact_policy_inline(uint32_t raw_state) {
  switch (raw_state) {
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6:
    case LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7:
    case LC_CTRL_LC_STATE_STATE_VALUE_RMA:
      // No error redaction in TEST_UNLOCKED and RMA states.
      return kShutdownErrorRedactNone;
    case LC_CTRL_LC_STATE_STATE_VALUE_DEV:
    case LC_CTRL_LC_STATE_STATE_VALUE_PROD:
    case LC_CTRL_LC_STATE_STATE_VALUE_PROD_END:
      // In production states use the redaction level specified in OTP.
      return (shutdown_error_redact_t)abs_mmio_read32(
          TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
          OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
          OTP_CTRL_PARAM_ROM_ERROR_REPORTING_OFFSET);
    default:
      // Redact everything if in an unexpected lifecycle state.
      return kShutdownErrorRedactAll;
  }
}

shutdown_error_redact_t shutdown_redact_policy(void) {
  // Determine the error code redaction policy to apply according to the
  // lifecycle state and OTP configuration.
  //
  // Note that we cannot use the lifecycle or OTP libraries since an error
  // may trigger a call to `shutdown_finalize`.
  uint32_t raw_state =
      bitfield_field32_read(abs_mmio_read32(TOP_EARLGREY_LC_CTRL_BASE_ADDR +
                                            LC_CTRL_LC_STATE_REG_OFFSET),
                            LC_CTRL_LC_STATE_STATE_FIELD);
  return shutdown_redact_policy_inline(raw_state);
}

SHUTDOWN_FUNC(NO_MODIFIERS, shutdown_report_error(rom_error_t reason)) {
  uint32_t raw_state =
      bitfield_field32_read(abs_mmio_read32(TOP_EARLGREY_LC_CTRL_BASE_ADDR +
                                            LC_CTRL_LC_STATE_REG_OFFSET),
                            LC_CTRL_LC_STATE_STATE_FIELD);

  // Call the inline variant of `shutdown_redact_policy` because we want to
  // guarantee that we won't jump to a different function.
  shutdown_error_redact_t policy = shutdown_redact_policy_inline(raw_state);

  // Call the inline variant of `shutdown_redact` because we want to guarantee
  // that we won't jump to a different function.
  uint32_t redacted_error = shutdown_redact_inline(reason, policy);

  // TODO(lowrisc/opentitan#7894): What (if anything) should we print at
  // startup?
  log_printf("lc_state: 0x%x\n\r", (unsigned int)raw_state);

  // TODO(lowRISC/opentitan#8236): log_printf is in the .text section.
  log_printf("boot_fault: 0x%x\n", (unsigned int)redacted_error);
}

SHUTDOWN_FUNC(NO_MODIFIERS, shutdown_software_escalate(void)) {
  enum { kBase = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR };
  //  Setting rv_core_ibex.SW_FATAL_ERR (rw0c) to any value other than
  // `kMultiBitBool4False` will continuously cause alert events.
  abs_mmio_write32(kBase + RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET, 0);
}

SHUTDOWN_FUNC(NO_MODIFIERS, shutdown_keymgr_kill(void)) {
  enum {
    kBase = TOP_EARLGREY_KEYMGR_BASE_ADDR,
  };
  uint32_t reg =
      bitfield_field32_write(0, KEYMGR_CONTROL_SHADOWED_DEST_SEL_FIELD,
                             KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE);
  reg = bitfield_field32_write(reg, KEYMGR_CONTROL_SHADOWED_OPERATION_FIELD,
                               KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_DISABLE);
  abs_mmio_write32_shadowed(kBase + KEYMGR_CONTROL_SHADOWED_REG_OFFSET, reg);

  abs_mmio_write32(kBase + KEYMGR_START_REG_OFFSET, 1);
  abs_mmio_write32(kBase + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET, 1);
}

SHUTDOWN_FUNC(NO_MODIFIERS, shutdown_flash_kill(void)) {
  enum { kBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR };
  // Setting DIS (rw0c) to a value other than 5 will disable flash permanently.
  abs_mmio_write32(kBase + FLASH_CTRL_DIS_REG_OFFSET, 0);
}

SHUTDOWN_FUNC(noreturn, shutdown_hang(void)) {
  enum { kSramCtrlBase = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR };

  // Disable SRAM execution and lock the register.
  abs_mmio_write32(kSramCtrlBase + SRAM_CTRL_EXEC_EN_OFFSET, 0);
  abs_mmio_write32(kSramCtrlBase + SRAM_CTRL_EXEC_REGWEN_REG_OFFSET, 0);

  // Switch to assembly as RAM (incl. stack) is about to get scrambled.
#ifdef OT_PLATFORM_RV32
  while (true) {
    asm volatile(
        // Request a new scrambling key, then lock the SRAM control register.
        "sw %[kRenewKey], %[kCtrlOffset](%[kMainRamCtrlBase]);"
        "sw zero, %[kRegWriteEn](%[kMainRamCtrlBase]);"

        // TODO(lowRISC/opentitan#7148): restrict the ePMP such that only
        // ROM may execute.  mundaym's suggestion: set entry 2 as a NAPOT
        // region covering the entire address space, clear all its permission
        // bits and set the lock bit, and then finally disable RLB to prevent
        // any further modifications.

        // Generate a halt-maze.
        "1:"
        "wfi; wfi; wfi; wfi; j 1b;"
        "wfi; wfi; j 1b;"
        "wfi; j 1b;"
        "wfi;"
        :
        : [kRenewKey] "r"(1 << SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT),
          [kCtrlOffset] "I"(SRAM_CTRL_CTRL_REG_OFFSET),
          [kMainRamCtrlBase] "r"(kSramCtrlBase),
          [kRegWriteEn] "I"(SRAM_CTRL_CTRL_REGWEN_REG_OFFSET));
  }
#endif
}

#ifndef OT_OFF_TARGET_TEST
/**
 * The shutdown_finalize function goes into the .shutdown section which is
 * placed by the linker script after all other executable code.
 */
__attribute__((section(".shutdown")))
#endif
void shutdown_finalize(rom_error_t reason) {
  shutdown_report_error(reason);
  shutdown_software_escalate();
  shutdown_keymgr_kill();
  shutdown_flash_kill();
  // If we get here, we'll wait for the watchdog to reset the chip.
  shutdown_hang();
}
