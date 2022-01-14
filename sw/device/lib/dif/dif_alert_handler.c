// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include <assert.h>

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

// TODO(#9899): add static assert for accumulator_threshold field size

/**
 * We use this to convert the class enum to the integer value that is assigned
 * to each class in auto-generated register header file. We do this to make this
 * code robust against changes to the class values in the auto-generated
 * register header file.
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
  ptrdiff_t regwen_offset =
      ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET + alert * sizeof(uint32_t);
  if (!mmio_region_read32(alert_handler->base_addr, regwen_offset)) {
    return kDifLocked;
  }

  // Enable the alert.
  ptrdiff_t enable_reg_offset =
      ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET + alert * sizeof(uint32_t);
  uint32_t enable_reg = bitfield_bit32_write(
      0, ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true);
  mmio_region_write32_shadowed(alert_handler->base_addr, enable_reg_offset,
                               enable_reg);

  // Classify the alert.
  ptrdiff_t class_reg_offset = ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
                               alert * sizeof(uint32_t);
  uint32_t class_reg = bitfield_field32_write(
      0, ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_FIELD, classification);
  mmio_region_write32_shadowed(alert_handler->base_addr, class_reg_offset,
                               class_reg);

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

#define LOC_ALERT_REGS_CASE_(loc_alert_, value_)                                     \
  case loc_alert_:                                                                   \
    enable_reg_offset =                                                              \
        ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_##value_##_REG_OFFSET;                   \
    enable_bit =                                                                     \
        ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_##value_##_EN_LA_##value_##_BIT;         \
    class_reg_offset =                                                               \
        ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_##value_##_REG_OFFSET;                \
    class_field =                                                                    \
        ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_##value_##_CLASS_LA_##value_##_FIELD; \
    regwen_offset = ALERT_HANDLER_LOC_ALERT_REGWEN_##value_##_REG_OFFSET;            \
    break;

  // Get register/field offsets for local alert type.
  ptrdiff_t enable_reg_offset;
  bitfield_bit32_index_t enable_bit;
  ptrdiff_t class_reg_offset;
  bitfield_field32_t class_field;
  ptrdiff_t regwen_offset;
  switch (local_alert) {
    LIST_OF_LOC_ALERTS(LOC_ALERT_REGS_CASE_)
    default:
      return kDifBadArg;
  }

#undef LOC_ALERT_ENUM_INIT_

  // Check if configuration is locked.
  if (!mmio_region_read32(alert_handler->base_addr, regwen_offset)) {
    return kDifLocked;
  }

  // Enable the alert.
  // NOTE: the alert ID corresponds directly to the multireg index.
  // (I.e., alert N has enable multireg N).
  uint32_t enable_reg = bitfield_bit32_write(0, enable_bit, true);
  mmio_region_write32_shadowed(alert_handler->base_addr, enable_reg_offset,
                               enable_reg);

  // Classify the alert.
  uint32_t class_reg = bitfield_field32_write(0, class_field, classification);
  mmio_region_write32_shadowed(alert_handler->base_addr, class_reg_offset,
                               class_reg);

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

    if (!is_valid_escalation_phase(phase) ||
        signal >= ALERT_HANDLER_PARAM_N_ESC_SEV) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t signal_enable_bit;
    bitfield_field32_t signal_map_field;
    switch (signal) {
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
      default:
        return kDifBadArg;
    }

    ctrl_reg = bitfield_bit32_write(ctrl_reg, signal_enable_bit, true);
    ctrl_reg = bitfield_field32_write(
        ctrl_reg, signal_map_field,
        (uint32_t)(phase - kDifAlertHandlerClassStatePhase0));

    // TODO(#9899): alter this to leave no hardware configuration effects if
    // kDifBadArg needs to be returned.
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

  mmio_region_write32_shadowed(alert_handler->base_addr, ctrl_reg_offset,
                               ctrl_reg);

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

// TODO(#9899): make this a testutil function.
dif_result_t dif_alert_handler_configure(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_config_t config,
    dif_toggle_t locked) {
  if (alert_handler == NULL || !dif_is_valid_toggle(locked)) {
    return kDifBadArg;
  }

  // Check lengths of alert, local alert, and class arrays.
  if ((config.alerts_len == 0 &&
       (config.alerts != NULL || config.alert_classes != NULL)) ||
      (config.alerts_len > 0 &&
       (config.alerts == NULL || config.alert_classes == NULL))) {
    return kDifBadArg;
  }
  if ((config.local_alerts_len == 0 &&
       (config.local_alerts != NULL || config.local_alert_classes != NULL)) ||
      (config.local_alerts_len > 0 &&
       (config.local_alerts == NULL || config.local_alert_classes == NULL))) {
    return kDifBadArg;
  }
  if ((config.classes_len == 0 &&
       (config.classes != NULL || config.class_configs != NULL)) ||
      (config.classes_len > 0 &&
       (config.classes == NULL || config.class_configs == NULL))) {
    return kDifBadArg;
  }

  // Check that the provided ping timeout actually fits in the timeout
  // register, which is smaller than a native word length.
  if (config.ping_timeout >
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK) {
    return kDifBadArg;
  }

  // Configure and enable the requested alerts.
  for (int i = 0; i < config.alerts_len; ++i) {
    // TODO(#9899): replace with CHECK_DIF_OK(...) when the parent function
    // becomes a testutil function.
    if (dif_alert_handler_configure_alert(
            alert_handler, config.alerts[i], config.alert_classes[i],
            kDifToggleEnabled, locked) != kDifOk) {
      return kDifError;
    }
  }

  // Configure and enable the requested local alerts.
  // TODO(#9899): replace with CHECK_DIF_OK(...) when the parent function
  // becomes a testutil function.
  for (int i = 0; i < config.local_alerts_len; ++i) {
    if (dif_alert_handler_configure_local_alert(
            alert_handler, config.local_alerts[i],
            config.local_alert_classes[i], kDifToggleEnabled,
            locked) != kDifOk) {
      return kDifError;
    }
  }

  // Configure and enable the requested classes.
  // TODO(#9899): replace with CHECK_DIF_OK(...) when the parent function
  // becomes a testutil function.
  for (int i = 0; i < config.classes_len; ++i) {
    if (dif_alert_handler_configure_class(
            alert_handler, config.classes[i], config.class_configs[i],
            kDifToggleEnabled, locked) != kDifOk) {
      return kDifError;
    }
  }

  // Configure the ping timer.
  // TODO(#9899): replace with CHECK_DIF_OK(...) when the parent function
  // becomes a testutil function.
  if (dif_alert_handler_configure_ping_timer(alert_handler, config.ping_timeout,
                                             kDifToggleEnabled,
                                             locked) != kDifOk) {
    return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_alert_handler_lock_ping_timer(
    const dif_alert_handler_t *alert_handler) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(
      1, ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT, true);
  mmio_region_write32_shadowed(alert_handler->base_addr,
                               ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET,
                               reg);

  return kDifOk;
}

dif_result_t dif_alert_handler_is_ping_timer_locked(
    const dif_alert_handler_t *alert_handler, bool *is_locked) {
  if (alert_handler == NULL || is_locked == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(alert_handler->base_addr,
                         ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET);
  *is_locked = bitfield_bit32_read(
      reg, ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT);

  return kDifOk;
}

dif_result_t dif_alert_handler_alert_is_cause(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    bool *is_cause) {
  if (alert_handler == NULL || is_cause == NULL ||
      alert >= ALERT_HANDLER_PARAM_N_ALERTS) {
    return kDifBadArg;
  }

  ptrdiff_t cause_reg_offset =
      ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET + alert * sizeof(uint32_t);
  uint32_t cause_reg =
      mmio_region_read32(alert_handler->base_addr, cause_reg_offset);
  // NOTE: assuming all cause registers across all alerts use the same bit
  // index for the cause bit
  *is_cause =
      bitfield_bit32_read(cause_reg, ALERT_HANDLER_ALERT_CAUSE_0_A_0_BIT);

  return kDifOk;
}

dif_result_t dif_alert_handler_alert_acknowledge(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert) {
  if (alert_handler == NULL || alert >= ALERT_HANDLER_PARAM_N_ALERTS) {
    return kDifBadArg;
  }

  ptrdiff_t cause_reg_offset =
      ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET + alert * sizeof(uint32_t);
  // NOTE: assuming all cause registers across all alerts use the same bit
  // index for the cause bit
  uint32_t cause_reg =
      bitfield_bit32_write(0, ALERT_HANDLER_ALERT_CAUSE_0_A_0_BIT, true);
  mmio_region_write32(alert_handler->base_addr, cause_reg_offset, cause_reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
static bool loc_alert_cause_reg_offset(dif_alert_handler_local_alert_t alert,
                                       ptrdiff_t *offset) {
  switch (alert) {
    case kDifAlertHandlerLocalAlertAlertPingFail:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET;
      break;
    case kDifAlertHandlerLocalAlertEscalationPingFail:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_1_REG_OFFSET;
      break;
    case kDifAlertHandlerLocalAlertAlertIntegrityFail:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_2_REG_OFFSET;
      break;
    case kDifAlertHandlerLocalAlertEscalationIntegrityFail:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_3_REG_OFFSET;
      break;
    case kDifAlertHandlerLocalAlertBusIntegrityFail:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_4_REG_OFFSET;
      break;
    case kDifAlertHandlerLocalAlertShadowedUpdateError:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_5_REG_OFFSET;
      break;
    case kDifAlertHandlerLocalAlertShadowedStorageError:
      *offset = ALERT_HANDLER_LOC_ALERT_CAUSE_6_REG_OFFSET;
      break;
    default:
      return false;
  }
  return true;
}

OT_WARN_UNUSED_RESULT
static bool loc_alert_cause_bit_index(dif_alert_handler_local_alert_t alert,
                                      bitfield_bit32_index_t *index) {
  switch (alert) {
    case kDifAlertHandlerLocalAlertAlertPingFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_0_LA_0_BIT;
      break;
    case kDifAlertHandlerLocalAlertEscalationPingFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_1_LA_1_BIT;
      break;
    case kDifAlertHandlerLocalAlertAlertIntegrityFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_2_LA_2_BIT;
      break;
    case kDifAlertHandlerLocalAlertEscalationIntegrityFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_3_LA_3_BIT;
      break;
    case kDifAlertHandlerLocalAlertBusIntegrityFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_4_LA_4_BIT;
      break;
    case kDifAlertHandlerLocalAlertShadowedUpdateError:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_5_LA_5_BIT;
      break;
    case kDifAlertHandlerLocalAlertShadowedStorageError:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_6_LA_6_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_alert_handler_local_alert_is_cause(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t alert, bool *is_cause) {
  if (alert_handler == NULL || is_cause == NULL) {
    return kDifBadArg;
  }

  // Get offset of cause register.
  ptrdiff_t offset;
  if (!loc_alert_cause_reg_offset(alert, &offset)) {
    return kDifBadArg;
  }

  // Get bit index within cause register.
  bitfield_bit32_index_t index;
  if (!loc_alert_cause_bit_index(alert, &index)) {
    return kDifBadArg;
  }

  // Read the cause register.
  uint32_t reg = mmio_region_read32(alert_handler->base_addr, offset);
  *is_cause = bitfield_bit32_read(reg, index);

  return kDifOk;
}

dif_result_t dif_alert_handler_local_alert_acknowledge(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t alert) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  // Get offset of cause register.
  ptrdiff_t offset;
  if (!loc_alert_cause_reg_offset(alert, &offset)) {
    return kDifBadArg;
  }

  // Get bit index within cause register.
  bitfield_bit32_index_t index;
  if (!loc_alert_cause_bit_index(alert, &index)) {
    return kDifBadArg;
  }

  // Clear the cause register by writing setting the index bit.
  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(alert_handler->base_addr, offset, reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
static bool get_clear_enable_reg_offset(dif_alert_handler_class_t class,
                                        ptrdiff_t *reg_offset) {
  switch (class) {
    case kDifAlertHandlerClassA:
      *reg_offset = ALERT_HANDLER_CLASSA_CLR_REGWEN_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      *reg_offset = ALERT_HANDLER_CLASSB_CLR_REGWEN_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      *reg_offset = ALERT_HANDLER_CLASSC_CLR_REGWEN_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      *reg_offset = ALERT_HANDLER_CLASSD_CLR_REGWEN_REG_OFFSET;
      break;
    default:
      return false;
  }
  return true;
}

dif_result_t dif_alert_handler_escalation_can_clear(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, bool *can_clear) {
  if (alert_handler == NULL || can_clear == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  if (!get_clear_enable_reg_offset(alert_class, &reg_offset)) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(alert_handler->base_addr, reg_offset);
  *can_clear = bitfield_bit32_read(
      reg, ALERT_HANDLER_CLASSA_CLR_REGWEN_CLASSA_CLR_REGWEN_BIT);

  return kDifOk;
}

dif_result_t dif_alert_handler_escalation_disable_clearing(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  if (!get_clear_enable_reg_offset(alert_class, &reg_offset)) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(
      0, ALERT_HANDLER_CLASSA_CLR_REGWEN_CLASSA_CLR_REGWEN_BIT, true);
  mmio_region_write32(alert_handler->base_addr, reg_offset, reg);

  return kDifOk;
}

dif_result_t dif_alert_handler_escalation_clear(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  switch (alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_CLR_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_CLR_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_CLR_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_CLR_SHADOWED_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(
      0, ALERT_HANDLER_CLASSA_CLR_SHADOWED_CLASSA_CLR_SHADOWED_BIT, true);
  mmio_region_write32_shadowed(alert_handler->base_addr, reg_offset, reg);

  return kDifOk;
}

dif_result_t dif_alert_handler_get_accumulator(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, uint16_t *alerts) {
  if (alert_handler == NULL || alerts == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  bitfield_field32_t field;
  switch (alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_ACCUM_CNT_REG_OFFSET;
      field = ALERT_HANDLER_CLASSA_ACCUM_CNT_CLASSA_ACCUM_CNT_FIELD;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET;
      field = ALERT_HANDLER_CLASSB_ACCUM_CNT_CLASSB_ACCUM_CNT_FIELD;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_ACCUM_CNT_REG_OFFSET;
      field = ALERT_HANDLER_CLASSC_ACCUM_CNT_CLASSC_ACCUM_CNT_FIELD;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_ACCUM_CNT_REG_OFFSET;
      field = ALERT_HANDLER_CLASSD_ACCUM_CNT_CLASSD_ACCUM_CNT_FIELD;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(alert_handler->base_addr, reg_offset);
  *alerts = bitfield_field32_read(reg, field);

  return kDifOk;
}

dif_result_t dif_alert_handler_get_escalation_counter(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, uint32_t *cycles) {
  if (alert_handler == NULL || cycles == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg_offset;
  switch (alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_ESC_CNT_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_ESC_CNT_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_ESC_CNT_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_ESC_CNT_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }

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

  ptrdiff_t reg_offset;
  bitfield_field32_t field;
  switch (alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_STATE_REG_OFFSET;
      field = ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_FIELD;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_STATE_REG_OFFSET;
      field = ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_FIELD;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_STATE_REG_OFFSET;
      field = ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_FIELD;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_STATE_REG_OFFSET;
      field = ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_FIELD;
      break;
    default:
      return kDifBadArg;
  }

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
