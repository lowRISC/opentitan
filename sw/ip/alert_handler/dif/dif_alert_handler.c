// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include <assert.h>
#include <limits.h>

#include "sw/device/lib/base/bitfield.h"

#include "alert_handler_regs.h"  // Generated.

static_assert(ALERT_HANDLER_PARAM_N_CLASSES == 4,
              "Expected four alert classes!");
static_assert(ALERT_HANDLER_PARAM_N_ESC_SEV == 4,
              "Expected four escalation signals!");
static_assert(ALERT_HANDLER_PARAM_N_PHASES == 4,
              "Expected four escalation phases!");
static_assert(ALERT_HANDLER_PARAM_N_LOC_ALERT == 7,
              "Expected seven local alerts!");

// Enable, class, lock, and cause multiregs for alerts.
static_assert(ALERT_HANDLER_ALERT_EN_SHADOWED_MULTIREG_COUNT &&
                  ALERT_HANDLER_ALERT_EN_SHADOWED_EN_A_FIELD_WIDTH == 1 &&
                  ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT == 0,
              "Expected alert enables to be multiregs with LSB at index 0!");
static_assert(ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT &&
                  ALERT_HANDLER_ALERT_CLASS_SHADOWED_CLASS_A_FIELD_WIDTH == 2 &&
                  ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_OFFSET == 0,
              "Expected alert class CSRs to be multiregs with LSB at index 0!");
static_assert(ALERT_HANDLER_ALERT_REGWEN_MULTIREG_COUNT &&
                  ALERT_HANDLER_ALERT_REGWEN_EN_FIELD_WIDTH == 1 &&
                  ALERT_HANDLER_ALERT_REGWEN_0_EN_0_BIT == 0,
              "Expected alert locks to be multiregs with LSB at index 0!");
static_assert(ALERT_HANDLER_ALERT_CAUSE_MULTIREG_COUNT &&
                  ALERT_HANDLER_ALERT_CAUSE_A_FIELD_WIDTH == 1 &&
                  ALERT_HANDLER_ALERT_CAUSE_0_A_0_BIT == 0,
              "Expected alert causes to be multiregs with LSB at index 0!");

// Enable, class, lock, and cause multiregs for local alerts.
static_assert(
    ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_MULTIREG_COUNT &&
        ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_EN_LA_FIELD_WIDTH == 1 &&
        ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT == 0,
    "Expected local alert enables to be multiregs with LSB at index 0!");
static_assert(
    ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT &&
        ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_CLASS_LA_FIELD_WIDTH == 2 &&
        ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_OFFSET == 0,
    "Expected local alert class CSRs to be multiregs with LSB at index 0!");
static_assert(
    ALERT_HANDLER_LOC_ALERT_REGWEN_MULTIREG_COUNT &&
        ALERT_HANDLER_LOC_ALERT_REGWEN_EN_FIELD_WIDTH == 1 &&
        ALERT_HANDLER_LOC_ALERT_REGWEN_0_EN_0_BIT == 0,
    "Expected local alert locks to be multiregs with LSB at index 0!");
static_assert(
    ALERT_HANDLER_LOC_ALERT_CAUSE_MULTIREG_COUNT &&
        ALERT_HANDLER_LOC_ALERT_CAUSE_LA_FIELD_WIDTH == 1 &&
        ALERT_HANDLER_LOC_ALERT_CAUSE_0_LA_0_BIT == 0,
    "Expected local alert causes to be multiregs with LSB at index 0!");

// Accumulator threshold field sizes.
static_assert(
    ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_CLASSA_ACCUM_THRESH_SHADOWED_MASK <=
        USHRT_MAX,
    "Expected class A accumulator threshold field to be 16 bits.");
static_assert(
    ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_CLASSB_ACCUM_THRESH_SHADOWED_MASK <=
        USHRT_MAX,
    "Expected class B accumulator threshold field to be 16 bits.");
static_assert(
    ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_CLASSC_ACCUM_THRESH_SHADOWED_MASK <=
        USHRT_MAX,
    "Expected class C accumulator threshold field to be 16 bits.");
static_assert(
    ALERT_HANDLER_CLASSD_ACCUM_THRESH_SHADOWED_CLASSD_ACCUM_THRESH_SHADOWED_MASK <=
        USHRT_MAX,
    "Expected class D accumulator threshold field to be 16 bits.");

/**
 * Macro for generating the case statements for local alert cause CSRs.
 */
#define LOC_ALERT_CAUSE_REGS_CASE_(loc_alert_, value_)                      \
  case loc_alert_:                                                          \
    cause_reg_offset = ALERT_HANDLER_LOC_ALERT_CAUSE_##value_##_REG_OFFSET; \
    break;

/**
 * Macro for generating the case statements for local alert lock CSRs.
 */
#define LOC_ALERT_REGWENS_CASE_(loc_alert_, value_)                       \
  case loc_alert_:                                                        \
    regwen_offset = ALERT_HANDLER_LOC_ALERT_REGWEN_##value_##_REG_OFFSET; \
    break;

/**
 * Macro for generating the case statements for class lock CSRs.
 */
#define ALERT_CLASS_REGWENS_CASE_(class_, value_)                    \
  case kDifAlertHandlerClass##class_:                                \
    regwen_offset = ALERT_HANDLER_CLASS##class_##_REGWEN_REG_OFFSET; \
    break;

/**
 * Macro for generating the case statements for class clear lock CSRs.
 */
#define ALERT_CLASS_CLEAR_REGWENS_CASE_(class_, value_)                  \
  case kDifAlertHandlerClass##class_:                                    \
    regwen_offset = ALERT_HANDLER_CLASS##class_##_CLR_REGWEN_REG_OFFSET; \
    break;

/**
 * We use this to convert the class enum to the integer value that is
 * assigned to each class in auto-generated register header file. We do this
 * to make this code robust against changes to the class values in the
 * auto-generated register header file.
 */
OT_WARN_UNUSED_RESULT
static bool class_to_uint32(dif_alert_handler_class_t alert_class,
                            uint32_t *classification) {
#define ALERT_CLASS_REGS_CASE_(class_, value_)                              \
  case kDifAlertHandlerClass##class_:                                       \
    *classification =                                                       \
        ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASS##class_; \
    break;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_REGS_CASE_)
    default:
      return false;
  }

#undef ALERT_CLASS_REGS_CASE_

  return true;
}

OT_WARN_UNUSED_RESULT
static bool is_valid_escalation_phase(dif_alert_handler_class_state_t phase) {
  if (phase < kDifAlertHandlerClassStatePhase0 ||
      phase > kDifAlertHandlerClassStatePhase3) {
    return false;
  }
  return true;
}

/**
 * NOTE: the alert ID corresponds directly to the multireg index for each CSR.
 * (I.e., alert N has enable multireg N).
 */
dif_result_t dif_alert_handler_configure_alert(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    dif_alert_handler_class_t alert_class, dif_toggle_t enabled,
    dif_toggle_t locked) {
  if (alert_handler == NULL || alert >= ALERT_HANDLER_PARAM_N_ALERTS ||
      !dif_is_valid_toggle(enabled) || !dif_is_valid_toggle(locked)) {
    return kDifBadArg;
  }
  uint32_t classification;
  if (!class_to_uint32(alert_class, &classification)) {
    return kDifBadArg;
  }

  // Check if configuration is locked.
  ptrdiff_t regwen_offset = ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET +
                            (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  if (!mmio_region_read32(alert_handler->base_addr, regwen_offset)) {
    return kDifLocked;
  }

  // Classify the alert.
  ptrdiff_t class_reg_offset = ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
                               (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  mmio_region_write32_shadowed(alert_handler->base_addr, class_reg_offset,
                               classification);

  // Enable the alert.
  ptrdiff_t enable_reg_offset = ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET +
                                (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  mmio_region_write32_shadowed(alert_handler->base_addr, enable_reg_offset,
                               0x1);

  // Lock the configuration.
  if (locked == kDifToggleEnabled) {
    mmio_region_write32(alert_handler->base_addr, regwen_offset, 0);
  }

  return kDifOk;
}

dif_result_t dif_alert_handler_configure_local_alert(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert,
    dif_alert_handler_class_t alert_class, dif_toggle_t enabled,
    dif_toggle_t locked) {
  if (alert_handler == NULL || !dif_is_valid_toggle(enabled) ||
      !dif_is_valid_toggle(locked)) {
    return kDifBadArg;
  }
  uint32_t classification;
  if (!class_to_uint32(alert_class, &classification)) {
    return kDifBadArg;
  }

#define LOC_ALERT_REGS_CASE_(loc_alert_, value_)                          \
  case loc_alert_:                                                        \
    enable_reg_offset =                                                   \
        ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_##value_##_REG_OFFSET;        \
    class_reg_offset =                                                    \
        ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_##value_##_REG_OFFSET;     \
    regwen_offset = ALERT_HANDLER_LOC_ALERT_REGWEN_##value_##_REG_OFFSET; \
    break;

  // Get register/field offsets for local alert type.
  ptrdiff_t enable_reg_offset;
  ptrdiff_t class_reg_offset;
  ptrdiff_t regwen_offset;
  switch (local_alert) {
    LIST_OF_LOC_ALERTS(LOC_ALERT_REGS_CASE_)
    default:
      return kDifBadArg;
  }

#undef LOC_ALERT_REGS_CASE_

  // Check if configuration is locked.
  if (!mmio_region_read32(alert_handler->base_addr, regwen_offset)) {
    return kDifLocked;
  }

  // Classify the alert.
  mmio_region_write32_shadowed(alert_handler->base_addr, class_reg_offset,
                               classification);

  // Enable the alert.
  // NOTE: the alert ID corresponds directly to the multireg index.
  // (I.e., alert N has enable multireg N).
  mmio_region_write32_shadowed(alert_handler->base_addr, enable_reg_offset,
                               0x1);

  // Lock the configuration.
  if (locked == kDifToggleEnabled) {
    mmio_region_write32(alert_handler->base_addr, regwen_offset, 0);
  }

  return kDifOk;
}

dif_result_t dif_alert_handler_configure_class(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class,
    dif_alert_handler_class_config_t config, dif_toggle_t enabled,
    dif_toggle_t locked) {
  if (alert_handler == NULL ||
      !dif_is_valid_toggle(config.auto_lock_accumulation_counter) ||
      (config.escalation_phases == NULL && config.escalation_phases_len != 0) ||
      (config.escalation_phases != NULL && config.escalation_phases_len == 0) ||
      !is_valid_escalation_phase(config.crashdump_escalation_phase) ||
      !dif_is_valid_toggle(enabled) || !dif_is_valid_toggle(locked)) {
    return kDifBadArg;
  }
  for (int i = 0; i < config.escalation_phases_len; ++i) {
    switch (config.escalation_phases[i].phase) {
      case kDifAlertHandlerClassStatePhase0:
      case kDifAlertHandlerClassStatePhase1:
      case kDifAlertHandlerClassStatePhase2:
      case kDifAlertHandlerClassStatePhase3:
        continue;
        break;
      default:
        return kDifBadArg;
    }
  }

#define ALERT_CLASS_CONFIG_REGS_CASE_(class_, value_)                         \
  case kDifAlertHandlerClass##class_:                                         \
    class_regwen_offset = ALERT_HANDLER_CLASS##class_##_REGWEN_REG_OFFSET;    \
    ctrl_reg_offset = ALERT_HANDLER_CLASS##class_##_CTRL_SHADOWED_REG_OFFSET; \
    accum_thresh_reg_offset =                                                 \
        ALERT_HANDLER_CLASS##class_##_ACCUM_THRESH_SHADOWED_REG_OFFSET;       \
    irq_deadline_reg_offset =                                                 \
        ALERT_HANDLER_CLASS##class_##_TIMEOUT_CYC_SHADOWED_REG_OFFSET;        \
    phase0_cycles_reg_offset =                                                \
        ALERT_HANDLER_CLASS##class_##_PHASE0_CYC_SHADOWED_REG_OFFSET;         \
    phase1_cycles_reg_offset =                                                \
        ALERT_HANDLER_CLASS##class_##_PHASE1_CYC_SHADOWED_REG_OFFSET;         \
    phase2_cycles_reg_offset =                                                \
        ALERT_HANDLER_CLASS##class_##_PHASE2_CYC_SHADOWED_REG_OFFSET;         \
    phase3_cycles_reg_offset =                                                \
        ALERT_HANDLER_CLASS##class_##_PHASE3_CYC_SHADOWED_REG_OFFSET;         \
    crashdump_phase_reg_offset =                                              \
        ALERT_HANDLER_CLASS##class_##_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET;  \
    break;

  ptrdiff_t class_regwen_offset;
  ptrdiff_t ctrl_reg_offset;
  ptrdiff_t accum_thresh_reg_offset;
  ptrdiff_t irq_deadline_reg_offset;
  ptrdiff_t phase0_cycles_reg_offset;
  ptrdiff_t phase1_cycles_reg_offset;
  ptrdiff_t phase2_cycles_reg_offset;
  ptrdiff_t phase3_cycles_reg_offset;
  ptrdiff_t crashdump_phase_reg_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_CONFIG_REGS_CASE_)
    default:
      return kDifBadArg;
  }

#undef ALERT_CLASS_CONFIG_REGS_CASE_

  // Check if class configuration is locked.
  if (!mmio_region_read32(alert_handler->base_addr, class_regwen_offset)) {
    return kDifLocked;
  }

  // NOTE: from this point on, we assume that Class A's constants are
  // representative of all alert class control register layouts.

  // Configure the class control register and escalation phases / cycle times.
  // Note, if an escalation phase is configured, it is also enabled.
  uint32_t ctrl_reg = 0;
  ctrl_reg =
      bitfield_bit32_write(ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT,
                           dif_toggle_to_bool(enabled));
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT,
      dif_toggle_to_bool(config.auto_lock_accumulation_counter));

  for (int i = 0; i < config.escalation_phases_len; ++i) {
    dif_alert_handler_class_state_t phase = config.escalation_phases[i].phase;
    dif_alert_handler_escalation_signal_t signal =
        config.escalation_phases[i].signal;

    // Check the escalation phase is valid. The signal is checked in the case
    // statement below, which will return kDifBadArg if it does not
    // correspond to any of the specified cases.
    if (!is_valid_escalation_phase(phase)) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t signal_enable_bit;
    bitfield_field32_t signal_map_field;
    switch (signal) {
      // TODO: this should be rewritten to allow combinations of all signals.
      // The alert handler supports the full phase -> signal mapping matrix.
      // I.e., it is possible to enable signal 0 and 3 in phase 1 for
      // instance. For Top Earl Grey it is for instance also recommended to
      // trigger signals 1 and 2 at the same time since both trigger the same
      // action in the life cycle controller and serve as redundant
      // channels.
      case 0:
        signal_enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT;
        signal_map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_FIELD;
        break;
      case 1:
        signal_enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT;
        signal_map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_FIELD;
        break;
      case 2:
        signal_enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT;
        signal_map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_FIELD;
        break;
      case 3:
        signal_enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT;
        signal_map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_FIELD;
        break;
      // Does not trigger any of the signals. Can be useful in cases where an
      // escalation phase is just used to wait a specific amount of time.
      case 0xFFFFFFFF:
        break;
      default:
        return kDifBadArg;
    }

    // Clear all settings.
    if (signal == 0xFFFFFFFF) {
      ctrl_reg = bitfield_bit32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT, false);
      ctrl_reg = bitfield_field32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_FIELD,
          (uint32_t)(phase - kDifAlertHandlerClassStatePhase0));
      ctrl_reg = bitfield_bit32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT, false);
      ctrl_reg = bitfield_field32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_FIELD,
          (uint32_t)(phase - kDifAlertHandlerClassStatePhase0));
      ctrl_reg = bitfield_bit32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT, false);
      ctrl_reg = bitfield_field32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_FIELD,
          (uint32_t)(phase - kDifAlertHandlerClassStatePhase0));
      ctrl_reg = bitfield_bit32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT, false);
      ctrl_reg = bitfield_field32_write(
          ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_FIELD,
          (uint32_t)(phase - kDifAlertHandlerClassStatePhase0));
    } else {
      ctrl_reg = bitfield_bit32_write(ctrl_reg, signal_enable_bit, true);
      ctrl_reg = bitfield_field32_write(
          ctrl_reg, signal_map_field,
          (uint32_t)(phase - kDifAlertHandlerClassStatePhase0));
    }

    switch (phase) {
      case kDifAlertHandlerClassStatePhase0:
        mmio_region_write32_shadowed(
            alert_handler->base_addr, phase0_cycles_reg_offset,
            config.escalation_phases[i].duration_cycles);
        break;
      case kDifAlertHandlerClassStatePhase1:
        mmio_region_write32_shadowed(
            alert_handler->base_addr, phase1_cycles_reg_offset,
            config.escalation_phases[i].duration_cycles);
        break;
      case kDifAlertHandlerClassStatePhase2:
        mmio_region_write32_shadowed(
            alert_handler->base_addr, phase2_cycles_reg_offset,
            config.escalation_phases[i].duration_cycles);
        break;
      case kDifAlertHandlerClassStatePhase3:
        mmio_region_write32_shadowed(
            alert_handler->base_addr, phase3_cycles_reg_offset,
            config.escalation_phases[i].duration_cycles);
        break;
      default:
        return kDifBadArg;
    }
  }

  // Configure the class accumulator threshold.
  mmio_region_write32_shadowed(alert_handler->base_addr,
                               accum_thresh_reg_offset,
                               config.accumulator_threshold);

  // Configure the class IRQ deadline.
  mmio_region_write32_shadowed(alert_handler->base_addr,
                               irq_deadline_reg_offset,
                               config.irq_deadline_cycles);

  // Configure the crashdump phase.
  mmio_region_write32_shadowed(alert_handler->base_addr,
                               crashdump_phase_reg_offset,
                               (uint32_t)(config.crashdump_escalation_phase -
                                          kDifAlertHandlerClassStatePhase0));

  // Configure the class control register last, since this holds the enable bit.
  mmio_region_write32_shadowed(alert_handler->base_addr, ctrl_reg_offset,
                               ctrl_reg);

  // Lock the configuration.
  if (locked == kDifToggleEnabled) {
    mmio_region_write32(alert_handler->base_addr, class_regwen_offset, 0);
  }

  return kDifOk;
}

dif_result_t dif_alert_handler_configure_ping_timer(
    const dif_alert_handler_t *alert_handler, uint32_t ping_timeout,
    dif_toggle_t enabled, dif_toggle_t locked) {
  if (alert_handler == NULL ||
      ping_timeout >
          ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK ||
      !dif_is_valid_toggle(enabled) || !dif_is_valid_toggle(locked)) {
    return kDifBadArg;
  }

  // Check if the ping timer is locked.
  if (!mmio_region_read32(alert_handler->base_addr,
                          ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // Set the ping timeout.
  mmio_region_write32_shadowed(
      alert_handler->base_addr,
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET, ping_timeout);

  // Enable the ping timer.
  // Note, this must be done after the timeout has been configured above, since
  // pinging will start immediately.
  if (enabled == kDifToggleEnabled) {
    mmio_region_write32_shadowed(
        alert_handler->base_addr,
        ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET, 1);
  }

  // Lock the configuration.
  if (locked == kDifToggleEnabled) {
    mmio_region_write32(alert_handler->base_addr,
                        ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);
  }

  return kDifOk;
}

dif_result_t dif_alert_handler_ping_timer_set_enabled(
    const dif_alert_handler_t *alert_handler, dif_toggle_t locked) {
  if (alert_handler == NULL || !dif_is_valid_toggle(locked)) {
    return kDifBadArg;
  }

  // Check if the ping timer is locked.
  if (!mmio_region_read32(alert_handler->base_addr,
                          ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // Enable the ping timer.
  mmio_region_write32_shadowed(alert_handler->base_addr,
                               ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
                               1);

  // Lock the configuration.
  if (locked == kDifToggleEnabled) {
    mmio_region_write32(alert_handler->base_addr,
                        ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);
  }

  return kDifOk;
}

dif_result_t dif_alert_handler_lock_alert(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert) {
  if (alert_handler == NULL || alert >= ALERT_HANDLER_PARAM_N_ALERTS) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset = ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET +
                            (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  mmio_region_write32(alert_handler->base_addr, regwen_offset, 0);

  return kDifOk;
}

dif_result_t dif_alert_handler_is_alert_locked(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    bool *is_locked) {
  if (alert_handler == NULL || alert >= ALERT_HANDLER_PARAM_N_ALERTS ||
      is_locked == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset = ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET +
                            (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  *is_locked = !mmio_region_read32(alert_handler->base_addr, regwen_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_lock_local_alert(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset;
  switch (local_alert) {
    LIST_OF_LOC_ALERTS(LOC_ALERT_REGWENS_CASE_)
    default:
      return kDifBadArg;
  }

  mmio_region_write32(alert_handler->base_addr, regwen_offset, 0);

  return kDifOk;
}

dif_result_t dif_alert_handler_is_local_alert_locked(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert, bool *is_locked) {
  if (alert_handler == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset;
  switch (local_alert) {
    LIST_OF_LOC_ALERTS(LOC_ALERT_REGWENS_CASE_)
    default:
      return kDifBadArg;
  }

  *is_locked = !mmio_region_read32(alert_handler->base_addr, regwen_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_lock_class(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_REGWENS_CASE_)
    default:
      return kDifBadArg;
  }

  mmio_region_write32(alert_handler->base_addr, regwen_offset, 0);

  return kDifOk;
}

dif_result_t dif_alert_handler_is_class_locked(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, bool *is_locked) {
  if (alert_handler == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_REGWENS_CASE_)
    default:
      return kDifBadArg;
  }

  *is_locked = !mmio_region_read32(alert_handler->base_addr, regwen_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_lock_ping_timer(
    const dif_alert_handler_t *alert_handler) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(alert_handler->base_addr,
                      ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET, 0);

  return kDifOk;
}

dif_result_t dif_alert_handler_is_ping_timer_locked(
    const dif_alert_handler_t *alert_handler, bool *is_locked) {
  if (alert_handler == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = !mmio_region_read32(alert_handler->base_addr,
                                   ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_alert_handler_alert_is_cause(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    bool *is_cause) {
  if (alert_handler == NULL || is_cause == NULL ||
      alert >= ALERT_HANDLER_PARAM_N_ALERTS) {
    return kDifBadArg;
  }

  ptrdiff_t cause_reg_offset = ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET +
                               (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  *is_cause = mmio_region_read32(alert_handler->base_addr, cause_reg_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_alert_acknowledge(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert) {
  if (alert_handler == NULL || alert >= ALERT_HANDLER_PARAM_N_ALERTS) {
    return kDifBadArg;
  }

  ptrdiff_t cause_reg_offset = ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET +
                               (ptrdiff_t)alert * (ptrdiff_t)sizeof(uint32_t);
  mmio_region_write32(alert_handler->base_addr, cause_reg_offset, 0x1);

  return kDifOk;
}

dif_result_t dif_alert_handler_local_alert_is_cause(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert, bool *is_cause) {
  if (alert_handler == NULL || is_cause == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t cause_reg_offset;
  switch (local_alert) {
    LIST_OF_LOC_ALERTS(LOC_ALERT_CAUSE_REGS_CASE_)
    default:
      return kDifBadArg;
  }

  *is_cause = mmio_region_read32(alert_handler->base_addr, cause_reg_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_local_alert_acknowledge(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t cause_reg_offset;
  switch (local_alert) {
    LIST_OF_LOC_ALERTS(LOC_ALERT_CAUSE_REGS_CASE_)
    default:
      return kDifBadArg;
  }

  mmio_region_write32(alert_handler->base_addr, cause_reg_offset, 0x1);

  return kDifOk;
}

dif_result_t dif_alert_handler_escalation_can_clear(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, bool *can_clear) {
  if (alert_handler == NULL || can_clear == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_CLEAR_REGWENS_CASE_)
    default:
      return kDifBadArg;
  }

  *can_clear = mmio_region_read32(alert_handler->base_addr, regwen_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_escalation_disable_clearing(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t regwen_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_CLEAR_REGWENS_CASE_)
    default:
      return kDifBadArg;
  }

  mmio_region_write32(alert_handler->base_addr, regwen_offset, 0);

  return kDifOk;
}

dif_result_t dif_alert_handler_escalation_clear(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

#define ALERT_CLASS_CLEAR_CASE_(class_, value_)                         \
  case kDifAlertHandlerClass##class_:                                   \
    reg_offset = ALERT_HANDLER_CLASS##class_##_CLR_SHADOWED_REG_OFFSET; \
    break;

  ptrdiff_t reg_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_CLEAR_CASE_)
    default:
      return kDifBadArg;
  }

#undef ALERT_CLASS_CLEAR_CASE_

  mmio_region_write32_shadowed(alert_handler->base_addr, reg_offset, 0x1);

  return kDifOk;
}

dif_result_t dif_alert_handler_get_accumulator(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, uint16_t *num_alerts) {
  if (alert_handler == NULL || num_alerts == NULL) {
    return kDifBadArg;
  }

#define ALERT_CLASS_ACCUM_CASE_(class_, value_)                                  \
  case kDifAlertHandlerClass##class_:                                            \
    reg_offset = ALERT_HANDLER_CLASS##class_##_ACCUM_CNT_REG_OFFSET;             \
    field =                                                                      \
        ALERT_HANDLER_CLASS##class_##_ACCUM_CNT_CLASS##class_##_ACCUM_CNT_FIELD; \
    break;

  ptrdiff_t reg_offset;
  bitfield_field32_t field;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_ACCUM_CASE_)
    default:
      return kDifBadArg;
  }

#undef ALERT_CLASS_ACCUM_CASE_

  uint32_t reg = mmio_region_read32(alert_handler->base_addr, reg_offset);
  *num_alerts = (uint16_t)bitfield_field32_read(reg, field);

  return kDifOk;
}

dif_result_t dif_alert_handler_get_escalation_counter(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, uint32_t *cycles) {
  if (alert_handler == NULL || cycles == NULL) {
    return kDifBadArg;
  }

#define ALERT_CLASS_ESC_CNT_CASE_(class_, value_)                  \
  case kDifAlertHandlerClass##class_:                              \
    reg_offset = ALERT_HANDLER_CLASS##class_##_ESC_CNT_REG_OFFSET; \
    break;

  ptrdiff_t reg_offset;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_ESC_CNT_CASE_)
    default:
      return kDifBadArg;
  }

#undef ALERT_CLASS_ESC_CNT_CASE_

  *cycles = mmio_region_read32(alert_handler->base_addr, reg_offset);

  return kDifOk;
}

dif_result_t dif_alert_handler_get_class_state(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class,
    dif_alert_handler_class_state_t *state) {
  if (alert_handler == NULL || state == NULL) {
    return kDifBadArg;
  }

#define ALERT_CLASS_STATE_CASE_(class_, value_)                              \
  case kDifAlertHandlerClass##class_:                                        \
    reg_offset = ALERT_HANDLER_CLASS##class_##_STATE_REG_OFFSET;             \
    field = ALERT_HANDLER_CLASS##class_##_STATE_CLASS##class_##_STATE_FIELD; \
    break;

  ptrdiff_t reg_offset;
  bitfield_field32_t field;
  switch (alert_class) {
    LIST_OF_CLASSES(ALERT_CLASS_STATE_CASE_)
    default:
      return kDifBadArg;
  }

#undef ALERT_CLASS_STATE_CASE_

  uint32_t reg = mmio_region_read32(alert_handler->base_addr, reg_offset);
  switch (bitfield_field32_read(reg, field)) {
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_IDLE:
      *state = kDifAlertHandlerClassStateIdle;
      break;
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TIMEOUT:
      *state = kDifAlertHandlerClassStateTimeout;
      break;
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE0:
      *state = kDifAlertHandlerClassStatePhase0;
      break;
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE1:
      *state = kDifAlertHandlerClassStatePhase1;
      break;
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE2:
      *state = kDifAlertHandlerClassStatePhase2;
      break;
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE3:
      *state = kDifAlertHandlerClassStatePhase3;
      break;
    case ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TERMINAL:
      *state = kDifAlertHandlerClassStateTerminal;
      break;
    default:
      return kDifError;
  }

  return kDifOk;
}
