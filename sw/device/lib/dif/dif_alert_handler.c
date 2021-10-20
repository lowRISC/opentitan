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

/**
 * Classifies alerts for a single alert class. Returns `false` if any of the
 * provided configuration is invalid.
 */
OT_WARN_UNUSED_RESULT
static bool classify_alerts(const dif_alert_handler_t *alert_handler,
                            const dif_alert_handler_class_config_t *class) {
  if (class->alerts == NULL && class->alerts_len != 0) {
    return false;
  }

  for (int i = 0; i < class->alerts_len; ++i) {
    if (class->alerts[i] >= ALERT_HANDLER_PARAM_N_ALERTS) {
      return false;
    }

    // Enable the alert.
    // NOTE: the value in alerts[i] corresponds directly to the multireg index.
    // (I.e., alert N has enable multireg N).
    ptrdiff_t enable_reg_offset = ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET +
                                  class->alerts[i] * sizeof(uint32_t);
    uint32_t enable_reg =
        mmio_region_read32(alert_handler->base_addr, enable_reg_offset);
    // TODO: we would like to use the generated macro for the ENABLE BIT OFFSET
    // below for the alert with the given index/ID, not just assume they are
    // the same across all regs in the multireg. However, making this assumption
    // for now.
    enable_reg = bitfield_bit32_write(
        enable_reg, ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT, true);
    mmio_region_write32_shadowed(alert_handler->base_addr, enable_reg_offset,
                                 enable_reg);

    // Determine alert classification.
    uint32_t classification;
    switch (class->alert_class) {
      case kDifAlertHandlerClassA:
        classification =
            ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSA;
        break;
      case kDifAlertHandlerClassB:
        classification =
            ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSB;
        break;
      case kDifAlertHandlerClassC:
        classification =
            ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSC;
        break;
      case kDifAlertHandlerClassD:
        classification =
            ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSD;
        break;
      default:
        return false;
    }

    // Classify the alert.
    // NOTE: the value in alerts[i] corresponds directly to the multireg index.
    // (I.e., alert N has enable multireg N).
    ptrdiff_t class_reg_offset =
        ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET +
        class->alerts[i] * sizeof(uint32_t);
    uint32_t class_reg =
        mmio_region_read32(alert_handler->base_addr, class_reg_offset);
    // TODO: we would like to use the generated macro for the BITFIELD
    // below for the alert with the given index/ID, not just assume they are
    // the same across all regs in the multireg.
    class_reg = bitfield_field32_write(
        class_reg, ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_FIELD,
        classification);
    mmio_region_write32_shadowed(alert_handler->base_addr, class_reg_offset,
                                 class_reg);

    // TODO: support locking the alert class configuration.
  }

  return true;
}

/**
 * Classifies local alerts for a single alert class. Returns `false` if any of
 * the provided configuration is invalid.
 */
OT_WARN_UNUSED_RESULT
static bool classify_local_alerts(
    const dif_alert_handler_t *alert_handler,
    const dif_alert_handler_class_config_t *class) {
  if (class->local_alerts == NULL && class->local_alerts_len != 0) {
    return false;
  }

  for (int i = 0; i < class->local_alerts_len; ++i) {
    uint32_t classification;
    switch (class->alert_class) {
      case kDifAlertHandlerClassA:
        classification =
            ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSA;
        break;
      case kDifAlertHandlerClassB:
        classification =
            ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSB;
        break;
      case kDifAlertHandlerClassC:
        classification =
            ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSC;
        break;
      case kDifAlertHandlerClassD:
        classification =
            ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSD;
        break;
      default:
        return false;
    }

    ptrdiff_t enable_reg_offset;
    bitfield_bit32_index_t enable_bit;
    ptrdiff_t class_reg_offset;
    bitfield_field32_t class_field;
    switch (class->local_alerts[i]) {
      case kDifAlertHandlerLocalAlertAlertPingFail:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_FIELD;
        break;
      case kDifAlertHandlerLocalAlertEscalationPingFail:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_EN_LA_1_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_CLASS_LA_1_FIELD;
        break;
      case kDifAlertHandlerLocalAlertAlertIntegrityFail:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_EN_LA_2_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_CLASS_LA_2_FIELD;
        break;
      case kDifAlertHandlerLocalAlertEscalationIntegrityFail:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_3_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_3_EN_LA_3_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_3_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_3_CLASS_LA_3_FIELD;
        break;
      case kDifAlertHandlerLocalAlertBusIntegrityFail:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_4_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_4_EN_LA_4_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_4_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_4_CLASS_LA_4_FIELD;
        break;
      case kDifAlertHandlerLocalAlertShadowedUpdateError:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_5_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_5_EN_LA_5_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_5_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_5_CLASS_LA_5_FIELD;
        break;
      case kDifAlertHandlerLocalAlertShadowedStorageError:
        enable_reg_offset = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_6_REG_OFFSET;
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_6_EN_LA_6_BIT;
        class_reg_offset = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_6_REG_OFFSET;
        class_field = ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_6_CLASS_LA_6_FIELD;
        break;
      default:
        return false;
    }

    uint32_t enable_reg =
        mmio_region_read32(alert_handler->base_addr, enable_reg_offset);
    uint32_t class_reg =
        mmio_region_read32(alert_handler->base_addr, class_reg_offset);
    enable_reg = bitfield_bit32_write(enable_reg, enable_bit, true);
    class_reg = bitfield_field32_write(class_reg, class_field, classification);
    mmio_region_write32_shadowed(alert_handler->base_addr, enable_reg_offset,
                                 enable_reg);
    mmio_region_write32_shadowed(alert_handler->base_addr, class_reg_offset,
                                 class_reg);
  }

  return true;
}

/**
 * Converts a toggle_t to bool.
 *
 * Returns false if `toggle` is out of range.
 */
OT_WARN_UNUSED_RESULT
static bool toggle_to_bool(dif_toggle_t toggle, bool *flag) {
  switch (toggle) {
    case kDifToggleEnabled:
      *flag = true;
      break;
    case kDifToggleDisabled:
      *flag = false;
      break;
    default:
      return false;
  }
  return true;
}

/**
 * Configures the control registers of a particular alert handler class.
 */
OT_WARN_UNUSED_RESULT
static bool configure_class(const dif_alert_handler_t *alert_handler,
                            const dif_alert_handler_class_config_t *class) {
  ptrdiff_t reg_offset;
  switch (class->alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_CTRL_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_CTRL_SHADOWED_REG_OFFSET;
      break;
    default:
      return false;
  }

  // NOTE: from this point on, we assume that Class A's constants are
  // representative of all alert class control register layouts.

  // We're going to configure the entire register, so there's no point in
  // reading it. In particular, this makes sure that the enable bits for each
  // escalation signal default to disabled.
  uint32_t ctrl_reg = 0;

  // Configure the escalation protocol enable flag.
  bool use_escalation_protocol;
  if (!toggle_to_bool(class->use_escalation_protocol,
                      &use_escalation_protocol)) {
    return false;
  }
  ctrl_reg =
      bitfield_bit32_write(ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT,
                           use_escalation_protocol);

  // Configure the escalation protocol auto-lock flag.
  bool automatic_locking;
  if (!toggle_to_bool(class->automatic_locking, &automatic_locking)) {
    return false;
  }
  ctrl_reg = bitfield_bit32_write(
      ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT, automatic_locking);

  if (class->phase_signals == NULL && class->phase_signals_len != 0) {
    return false;
  }
  // Configure the escalation signals for each escalation phase. In particular,
  // if an escalation phase is configured, it is also enabled.
  for (int i = 0; i < class->phase_signals_len; ++i) {
    if (class->phase_signals[i].signal >= ALERT_HANDLER_PARAM_N_ESC_SEV) {
      return false;
    }

    bitfield_bit32_index_t enable_bit;
    bitfield_field32_t map_field;
    switch (class->phase_signals[i].phase) {
      case kDifAlertHandlerClassStatePhase0:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_FIELD;
        break;
      case kDifAlertHandlerClassStatePhase1:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_FIELD;
        break;
      case kDifAlertHandlerClassStatePhase2:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_FIELD;
        break;
      case kDifAlertHandlerClassStatePhase3:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_FIELD;
        break;
      default:
        return false;
    }

    ctrl_reg = bitfield_bit32_write(ctrl_reg, enable_bit, true);
    ctrl_reg = bitfield_field32_write(ctrl_reg, map_field,
                                      class->phase_signals[i].signal);
  }

  mmio_region_write32_shadowed(alert_handler->base_addr, reg_offset, ctrl_reg);

  // Configure the class accumulator threshold.
  ptrdiff_t acc_offset;
  switch (class->alert_class) {
    case kDifAlertHandlerClassA:
      acc_offset = ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      acc_offset = ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      acc_offset = ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      acc_offset = ALERT_HANDLER_CLASSD_ACCUM_THRESH_SHADOWED_REG_OFFSET;
      break;
    default:
      return false;
  }
  mmio_region_write32_shadowed(alert_handler->base_addr, acc_offset,
                               class->accumulator_threshold);

  // Configure the class IRQ deadline.
  ptrdiff_t deadline_offset;
  switch (class->alert_class) {
    case kDifAlertHandlerClassA:
      deadline_offset = ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      deadline_offset = ALERT_HANDLER_CLASSB_TIMEOUT_CYC_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      deadline_offset = ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      deadline_offset = ALERT_HANDLER_CLASSD_TIMEOUT_CYC_SHADOWED_REG_OFFSET;
      break;
    default:
      return false;
  }
  mmio_region_write32_shadowed(alert_handler->base_addr, deadline_offset,
                               class->irq_deadline_cycles);

  return true;
}

/**
 * Configures phase durations of a particular class.
 */
OT_WARN_UNUSED_RESULT
static bool configure_phase_durations(
    const dif_alert_handler_t *alert_handler,
    const dif_alert_handler_class_config_t *class) {
  if (class->phase_durations == NULL && class->phase_durations_len != 0) {
    return false;
  }

  for (int i = 0; i < class->phase_durations_len; ++i) {
    // To save on writing a fairly ridiculous `if` chain, we use a lookup table
    // that leverages the numeric values of enum constants.
    static const ptrdiff_t kRegOffsets
        [ALERT_HANDLER_PARAM_N_CLASSES][ALERT_HANDLER_PARAM_N_PHASES] = {
            [kDifAlertHandlerClassA] =
                {
                    ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSA_PHASE3_CYC_SHADOWED_REG_OFFSET,
                },
            [kDifAlertHandlerClassB] =
                {
                    ALERT_HANDLER_CLASSB_PHASE0_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSB_PHASE1_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSB_PHASE2_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSB_PHASE3_CYC_SHADOWED_REG_OFFSET,
                },
            [kDifAlertHandlerClassC] =
                {
                    ALERT_HANDLER_CLASSC_PHASE0_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSC_PHASE1_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSC_PHASE2_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSC_PHASE3_CYC_SHADOWED_REG_OFFSET,
                },
            [kDifAlertHandlerClassD] =
                {
                    ALERT_HANDLER_CLASSD_PHASE0_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSD_PHASE1_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSD_PHASE2_CYC_SHADOWED_REG_OFFSET,
                    ALERT_HANDLER_CLASSD_PHASE3_CYC_SHADOWED_REG_OFFSET,
                },
        };

    if (class->alert_class >= ALERT_HANDLER_PARAM_N_CLASSES) {
      return false;
    }

    // NOTE: phase need not be an escalation phase!
    dif_alert_handler_class_state_t phase = class->phase_durations[i].phase;
    if (phase < kDifAlertHandlerClassStatePhase0 ||
        phase > kDifAlertHandlerClassStatePhase3) {
      return false;
    }
    ptrdiff_t reg_offset =
        kRegOffsets[class->alert_class]
                   [phase - kDifAlertHandlerClassStatePhase0];

    mmio_region_write32_shadowed(alert_handler->base_addr, reg_offset,
                                 class->phase_durations[i].cycles);
  }

  return true;
}

dif_result_t dif_alert_handler_configure(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_config_t config) {
  if (alert_handler == NULL) {
    return kDifBadArg;
  }
  // Check that the provided ping timeout actually fits in the timeout register,
  // which is smaller than a native word length.
  if (config.ping_timeout >
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK) {
    return kDifBadArg;
  }
  if (config.classes == NULL && config.classes_len != 0) {
    return kDifBadArg;
  }

  bool is_locked;
  dif_result_t result = dif_alert_handler_is_locked(alert_handler, &is_locked);
  if (result != kDifOk) {
    return result;
  }
  if (is_locked) {
    return kDifLocked;
  }

  for (int i = 0; i < config.classes_len; ++i) {
    if (!classify_alerts(alert_handler, &config.classes[i])) {
      return kDifError;
    }
    if (!classify_local_alerts(alert_handler, &config.classes[i])) {
      return kDifError;
    }
    if (!configure_class(alert_handler, &config.classes[i])) {
      return kDifError;
    }
    if (!configure_phase_durations(alert_handler, &config.classes[i])) {
      return kDifError;
    }
  }

  uint32_t ping_timeout_reg = bitfield_field32_write(
      0,
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_FIELD,
      config.ping_timeout);
  mmio_region_write32_shadowed(
      alert_handler->base_addr,
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET, ping_timeout_reg);

  return kDifOk;
}

dif_result_t dif_alert_handler_lock(const dif_alert_handler_t *alert_handler) {
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

dif_result_t dif_alert_handler_is_locked(
    const dif_alert_handler_t *alert_handler, bool *is_locked) {
  if (alert_handler == NULL || is_locked == NULL) {
    return kDifBadArg;
  }
  // TODO(timothytrippel): more "locking" functionality has been added that
  // can lock the ping-timer-en and ping-timer-cyc with the
  // ping-timer-regwen, and likewise with the alert-en-x and alert-class-x
  // registers. We need to check for this here, otherwise the alerts cannot be
  // enabled.

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
  // NOTE: assuming all cause registers across all alerts use the same bit index
  // for the cause bit
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
  // NOTE: assuming all cause registers across all alerts use the same bit index
  // for the cause bit
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
