// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include "sw/device/lib/base/bitfield.h"

#include "alert_handler_regs.h"  // Generated.

_Static_assert(ALERT_HANDLER_PARAM_N_CLASSES == 4,
               "Expected four alert classes!");
_Static_assert(ALERT_HANDLER_PARAM_N_ESC_SEV == 4,
               "Expected four escalation signals!");
_Static_assert(ALERT_HANDLER_PARAM_N_PHASES == 4,
               "Expected four escalation phases!");

dif_alert_handler_result_t dif_alert_handler_init(
    dif_alert_handler_params_t params, dif_alert_handler_t *handler) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  // TODO: We currently don't support more than 16 alerts correctly.
  // See: #3826
  if (params.alert_count > 16) {
    return kDifAlertHandlerBadArg;
  }

  // For now, the hardware is hardwired to four signals.
  if (params.escalation_signal_count != ALERT_HANDLER_PARAM_N_ESC_SEV) {
    return kDifAlertHandlerBadArg;
  }

  handler->params = params;

  return kDifAlertHandlerOk;
}

/**
 * Classifies alerts for a single alert class. Returns `false` if any of the
 * provided configuration is invalid.
 */
DIF_WARN_UNUSED_RESULT
static bool classify_alerts(const dif_alert_handler_t *handler,
                            const dif_alert_handler_class_config_t *class) {
  if (class->alerts == NULL && class->alerts_len != 0) {
    return false;
  }

  uint32_t enable_reg = mmio_region_read32(handler->params.base_addr,
                                           ALERT_HANDLER_ALERT_EN_REG_OFFSET);
  uint32_t alerts_reg = mmio_region_read32(
      handler->params.base_addr, ALERT_HANDLER_ALERT_CLASS_REG_OFFSET);

  for (int i = 0; i < class->alerts_len; ++i) {
    if (class->alerts[i] >= handler->params.alert_count) {
      return false;
    }

    // Note: the value in alerts[i] corresponds directly to the bit index within
    // the register. (I.e., alert N has enable bit N).
    enable_reg = bitfield_bit32_write(enable_reg, class->alerts[i], true);

    uint32_t classification;
    switch (class->alert_class) {
      case kDifAlertHandlerClassA:
        classification = ALERT_HANDLER_ALERT_CLASS_CLASS_A_0_VALUE_CLASSA;
        break;
      case kDifAlertHandlerClassB:
        classification = ALERT_HANDLER_ALERT_CLASS_CLASS_A_0_VALUE_CLASSB;
        break;
      case kDifAlertHandlerClassC:
        classification = ALERT_HANDLER_ALERT_CLASS_CLASS_A_0_VALUE_CLASSC;
        break;
      case kDifAlertHandlerClassD:
        classification = ALERT_HANDLER_ALERT_CLASS_CLASS_A_0_VALUE_CLASSD;
        break;
      default:
        return false;
    }

    // TODO: Currently, we assume all fields are of equal width.
    // See: #3826
    uint32_t field_width =
        bitfield_popcount32(ALERT_HANDLER_ALERT_CLASS_CLASS_A_0_MASK);
    uint32_t field_offset = field_width * class->alerts[i];

    alerts_reg = bitfield_field32_write(
        alerts_reg,
        (bitfield_field32_t){
            .mask = ALERT_HANDLER_ALERT_CLASS_CLASS_A_0_MASK,
            .index = field_offset,
        },
        classification);
  }

  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_ALERT_EN_REG_OFFSET, enable_reg);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_ALERT_CLASS_REG_OFFSET, alerts_reg);
  return true;
}

/**
 * Classifies local alerts for a single alert class. Returns `false` if any of
 * the provided configuration is invalid.
 */
DIF_WARN_UNUSED_RESULT
static bool classify_local_alerts(
    const dif_alert_handler_t *handler,
    const dif_alert_handler_class_config_t *class) {
  if (class->local_alerts == NULL && class->local_alerts_len != 0) {
    return false;
  }

  uint32_t enable_reg = mmio_region_read32(
      handler->params.base_addr, ALERT_HANDLER_LOC_ALERT_EN_REG_OFFSET);
  uint32_t alerts_reg = mmio_region_read32(
      handler->params.base_addr, ALERT_HANDLER_LOC_ALERT_CLASS_REG_OFFSET);

  for (int i = 0; i < class->local_alerts_len; ++i) {
    uint32_t classification;
    switch (class->alert_class) {
      case kDifAlertHandlerClassA:
        classification = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_VALUE_CLASSA;
        break;
      case kDifAlertHandlerClassB:
        classification = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_VALUE_CLASSB;
        break;
      case kDifAlertHandlerClassC:
        classification = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_VALUE_CLASSC;
        break;
      case kDifAlertHandlerClassD:
        classification = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_VALUE_CLASSD;
        break;
      default:
        return false;
    }

    bitfield_bit32_index_t enable_bit;
    bitfield_field32_t field;
    switch (class->local_alerts[i]) {
      case kDifAlertHandlerLocalAlertAlertPingFail:
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_EN_LA_0_BIT;
        field = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_0_FIELD;
        break;
      case kDifAlertHandlerLocalAlertEscalationPingFail:
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_EN_LA_1_BIT;
        field = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_1_FIELD;
        break;
      case kDifAlertHandlerLocalAlertAlertIntegrityFail:
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_EN_LA_2_BIT;
        field = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_2_FIELD;
        break;
      case kDifAlertHandlerLocalAlertEscalationIntegrityFail:
        enable_bit = ALERT_HANDLER_LOC_ALERT_EN_EN_LA_3_BIT;
        field = ALERT_HANDLER_LOC_ALERT_CLASS_CLASS_LA_3_FIELD;
        break;
      default:
        return false;
    }

    enable_reg = bitfield_bit32_write(enable_reg, enable_bit, true);
    alerts_reg = bitfield_field32_write(alerts_reg, field, classification);
  }

  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_LOC_ALERT_EN_REG_OFFSET, enable_reg);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_LOC_ALERT_CLASS_REG_OFFSET, alerts_reg);
  return true;
}

/**
 * Converts a toggle_t to bool.
 *
 * Returns false if `toggle` is out of range.
 */
DIF_WARN_UNUSED_RESULT
static bool toggle_to_bool(dif_alert_handler_toggle_t toggle, bool *flag) {
  switch (toggle) {
    case kDifAlertHandlerToggleEnabled:
      *flag = true;
      break;
    case kDifAlertHandlerToggleDisabled:
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
DIF_WARN_UNUSED_RESULT
static bool configure_class(const dif_alert_handler_t *handler,
                            const dif_alert_handler_class_config_t *class) {
  ptrdiff_t reg_offset;
  switch (class->alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_CTRL_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_CTRL_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_CTRL_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_CTRL_REG_OFFSET;
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
  ctrl_reg = bitfield_bit32_write(ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_EN_BIT,
                                  use_escalation_protocol);

  // Configure the escalation protocol auto-lock flag.
  bool automatic_locking;
  if (!toggle_to_bool(class->automatic_locking, &automatic_locking)) {
    return false;
  }
  ctrl_reg = bitfield_bit32_write(ctrl_reg, ALERT_HANDLER_CLASSA_CTRL_LOCK_BIT,
                                  automatic_locking);

  if (class->phase_signals == NULL && class->phase_signals_len != 0) {
    return false;
  }
  // Configure the escalation signals for each escalation phase. In particular,
  // if an escalation phase is configured, it is also enabled.
  for (int i = 0; i < class->phase_signals_len; ++i) {
    if (class->phase_signals[i].signal >=
        handler->params.escalation_signal_count) {
      return false;
    }

    bitfield_bit32_index_t enable_bit;
    bitfield_field32_t map_field;
    switch (class->phase_signals[i].phase) {
      case kDifAlertHandlerClassStatePhase0:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_EN_E0_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_MAP_E0_FIELD;
        break;
      case kDifAlertHandlerClassStatePhase1:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_EN_E1_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_MAP_E1_FIELD;
        break;
      case kDifAlertHandlerClassStatePhase2:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_EN_E2_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_MAP_E2_FIELD;
        break;
      case kDifAlertHandlerClassStatePhase3:
        enable_bit = ALERT_HANDLER_CLASSA_CTRL_EN_E3_BIT;
        map_field = ALERT_HANDLER_CLASSA_CTRL_MAP_E3_FIELD;
        break;
      default:
        return false;
    }

    ctrl_reg = bitfield_bit32_write(ctrl_reg, enable_bit, true);
    ctrl_reg = bitfield_field32_write(ctrl_reg, map_field,
                                      class->phase_signals[i].signal);
  }

  mmio_region_write32(handler->params.base_addr, reg_offset, ctrl_reg);

  // Configure the class accumulator threshold.
  ptrdiff_t acc_offset;
  switch (class->alert_class) {
    case kDifAlertHandlerClassA:
      acc_offset = ALERT_HANDLER_CLASSA_ACCUM_THRESH_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      acc_offset = ALERT_HANDLER_CLASSB_ACCUM_THRESH_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      acc_offset = ALERT_HANDLER_CLASSC_ACCUM_THRESH_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      acc_offset = ALERT_HANDLER_CLASSD_ACCUM_THRESH_REG_OFFSET;
      break;
    default:
      return false;
  }
  mmio_region_write32(handler->params.base_addr, acc_offset,
                      class->accumulator_threshold);

  // Configure the class IRQ deadline.
  ptrdiff_t deadline_offset;
  switch (class->alert_class) {
    case kDifAlertHandlerClassA:
      deadline_offset = ALERT_HANDLER_CLASSA_TIMEOUT_CYC_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      deadline_offset = ALERT_HANDLER_CLASSB_TIMEOUT_CYC_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      deadline_offset = ALERT_HANDLER_CLASSC_TIMEOUT_CYC_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      deadline_offset = ALERT_HANDLER_CLASSD_TIMEOUT_CYC_REG_OFFSET;
      break;
    default:
      return false;
  }
  mmio_region_write32(handler->params.base_addr, deadline_offset,
                      class->irq_deadline_cycles);

  return true;
}

/**
 * Configures phase durations of a particular class.
 */
DIF_WARN_UNUSED_RESULT
static bool configure_phase_durations(
    const dif_alert_handler_t *handler,
    const dif_alert_handler_class_config_t *class) {
  if (class->phase_durations == NULL && class->phase_durations_len != 0) {
    return false;
  }

  for (int i = 0; i < class->phase_durations_len; ++i) {
    // To save on writing a fairly ridiculous `if` chain, we use a lookup table
    // that leverages the numeric values of enum constants.
    static const ptrdiff_t
        kRegOffsets[ALERT_HANDLER_PARAM_N_CLASSES]
                   [ALERT_HANDLER_PARAM_N_PHASES] = {
                       [kDifAlertHandlerClassA] =
                           {
                               ALERT_HANDLER_CLASSA_PHASE0_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSA_PHASE1_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSA_PHASE2_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSA_PHASE3_CYC_REG_OFFSET,
                           },
                       [kDifAlertHandlerClassB] =
                           {
                               ALERT_HANDLER_CLASSB_PHASE0_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSB_PHASE1_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSB_PHASE2_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSB_PHASE3_CYC_REG_OFFSET,
                           },
                       [kDifAlertHandlerClassC] =
                           {
                               ALERT_HANDLER_CLASSC_PHASE0_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSC_PHASE1_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSC_PHASE2_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSC_PHASE3_CYC_REG_OFFSET,
                           },
                       [kDifAlertHandlerClassD] =
                           {
                               ALERT_HANDLER_CLASSD_PHASE0_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSD_PHASE1_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSD_PHASE2_CYC_REG_OFFSET,
                               ALERT_HANDLER_CLASSD_PHASE3_CYC_REG_OFFSET,
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

    mmio_region_write32(handler->params.base_addr, reg_offset,
                        class->phase_durations[i].cycles);
  }

  return true;
}

dif_alert_handler_config_result_t dif_alert_handler_configure(
    const dif_alert_handler_t *handler, dif_alert_handler_config_t config) {
  if (handler == NULL) {
    return kDifAlertHandlerConfigBadArg;
  }
  // Check that the provided ping timeout actually fits in the timeout register,
  // which is smaller than a native word length.
  if (config.ping_timeout >
      ALERT_HANDLER_PING_TIMEOUT_CYC_PING_TIMEOUT_CYC_MASK) {
    return kDifAlertHandlerConfigBadArg;
  }
  if (config.classes == NULL && config.classes_len != 0) {
    return kDifAlertHandlerConfigBadArg;
  }

  bool is_locked;
  dif_alert_handler_result_t result =
      dif_alert_handler_is_locked(handler, &is_locked);
  if (result != kDifAlertHandlerOk) {
    return (dif_alert_handler_config_result_t)result;
  }
  if (is_locked) {
    return kDifAlertHandlerConfigLocked;
  }

  for (int i = 0; i < config.classes_len; ++i) {
    if (!classify_alerts(handler, &config.classes[i])) {
      return kDifAlertHandlerConfigError;
    }
    if (!classify_local_alerts(handler, &config.classes[i])) {
      return kDifAlertHandlerConfigError;
    }
    if (!configure_class(handler, &config.classes[i])) {
      return kDifAlertHandlerConfigError;
    }
    if (!configure_phase_durations(handler, &config.classes[i])) {
      return kDifAlertHandlerConfigError;
    }
  }

  uint32_t ping_timeout_reg = bitfield_field32_write(
      0, ALERT_HANDLER_PING_TIMEOUT_CYC_PING_TIMEOUT_CYC_FIELD,
      config.ping_timeout);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_PING_TIMEOUT_CYC_REG_OFFSET,
                      ping_timeout_reg);

  return kDifAlertHandlerConfigOk;
}

dif_alert_handler_result_t dif_alert_handler_lock(
    const dif_alert_handler_t *handler) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, ALERT_HANDLER_REGEN_REGEN_BIT, true);
  mmio_region_write32(handler->params.base_addr, ALERT_HANDLER_REGEN_REG_OFFSET,
                      reg);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_is_locked(
    const dif_alert_handler_t *handler, bool *is_locked) {
  if (handler == NULL || is_locked == NULL) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_REGEN_REG_OFFSET);
  // Note that "true" indicates "enabled", so we negated to get "locked".
  *is_locked = !bitfield_bit32_read(reg, ALERT_HANDLER_REGEN_REGEN_BIT);

  return kDifAlertHandlerOk;
}

DIF_WARN_UNUSED_RESULT
static bool irq_index(dif_alert_handler_class_t class,
                      bitfield_bit32_index_t *index) {
  switch (class) {
    case kDifAlertHandlerClassA:
      *index = ALERT_HANDLER_INTR_COMMON_CLASSA_BIT;
      break;
    case kDifAlertHandlerClassB:
      *index = ALERT_HANDLER_INTR_COMMON_CLASSB_BIT;
      break;
    case kDifAlertHandlerClassC:
      *index = ALERT_HANDLER_INTR_COMMON_CLASSC_BIT;
      break;
    case kDifAlertHandlerClassD:
      *index = ALERT_HANDLER_INTR_COMMON_CLASSD_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_alert_handler_result_t dif_alert_handler_irq_is_pending(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    bool *is_pending) {
  if (handler == NULL || is_pending == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(alert_class, &index)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg, index);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_irq_acknowledge(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(alert_class, &index)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_INTR_STATE_REG_OFFSET);
  reg = bitfield_bit32_write(reg, index, true);  // Write-one clear.
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_INTR_STATE_REG_OFFSET, reg);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_irq_get_enabled(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    dif_alert_handler_toggle_t *state) {
  if (handler == NULL || state == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(alert_class, &index)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_INTR_ENABLE_REG_OFFSET);
  *state = bitfield_bit32_read(reg, index) ? kDifAlertHandlerToggleEnabled
                                           : kDifAlertHandlerToggleDisabled;

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_irq_set_enabled(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    dif_alert_handler_toggle_t state) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(alert_class, &index)) {
    return kDifAlertHandlerBadArg;
  }

  bool flag;
  if (!toggle_to_bool(state, &flag)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_INTR_ENABLE_REG_OFFSET);
  reg = bitfield_bit32_write(reg, index, flag);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, reg);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_irq_force(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(alert_class, &index)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_INTR_TEST_REG_OFFSET, reg);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_irq_disable_all(
    const dif_alert_handler_t *handler,
    dif_alert_handler_irq_snapshot_t *snapshot) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(handler->params.base_addr,
                                   ALERT_HANDLER_INTR_ENABLE_REG_OFFSET);
  }

  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, 0);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_irq_restore_all(
    const dif_alert_handler_t *handler,
    const dif_alert_handler_irq_snapshot_t *snapshot) {
  if (handler == NULL || snapshot == NULL) {
    return kDifAlertHandlerBadArg;
  }

  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_INTR_ENABLE_REG_OFFSET, *snapshot);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_alert_is_cause(
    const dif_alert_handler_t *handler, dif_alert_handler_alert_t alert,
    bool *is_cause) {
  if (handler == NULL || is_cause == NULL ||
      alert >= handler->params.alert_count) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_ALERT_CAUSE_REG_OFFSET);
  *is_cause = bitfield_bit32_read(reg, alert);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_alert_acknowledge(
    const dif_alert_handler_t *handler, dif_alert_handler_alert_t alert) {
  if (handler == NULL || alert >= handler->params.alert_count) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, alert, true);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_ALERT_CAUSE_REG_OFFSET, reg);

  return kDifAlertHandlerOk;
}

DIF_WARN_UNUSED_RESULT
static bool loc_alert_index(dif_alert_handler_local_alert_t alert,
                            bitfield_bit32_index_t *index) {
  switch (alert) {
    case kDifAlertHandlerLocalAlertAlertPingFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_LA_0_BIT;
      break;
    case kDifAlertHandlerLocalAlertEscalationPingFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_LA_1_BIT;
      break;
    case kDifAlertHandlerLocalAlertAlertIntegrityFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_LA_2_BIT;
      break;
    case kDifAlertHandlerLocalAlertEscalationIntegrityFail:
      *index = ALERT_HANDLER_LOC_ALERT_CAUSE_LA_3_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_alert_handler_result_t dif_alert_handler_local_alert_is_cause(
    const dif_alert_handler_t *handler, dif_alert_handler_local_alert_t alert,
    bool *is_cause) {
  if (handler == NULL || is_cause == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!loc_alert_index(alert, &index)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr,
                                    ALERT_HANDLER_LOC_ALERT_CAUSE_REG_OFFSET);
  *is_cause = bitfield_bit32_read(reg, index);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_local_alert_acknowledge(
    const dif_alert_handler_t *handler, dif_alert_handler_local_alert_t alert) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  bitfield_bit32_index_t index;
  if (!loc_alert_index(alert, &index)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(handler->params.base_addr,
                      ALERT_HANDLER_LOC_ALERT_CAUSE_REG_OFFSET, reg);

  return kDifAlertHandlerOk;
}

DIF_WARN_UNUSED_RESULT
static bool get_clear_enable_reg_offset(dif_alert_handler_class_t class,
                                        ptrdiff_t *reg_offset) {
  switch (class) {
    case kDifAlertHandlerClassA:
      *reg_offset = ALERT_HANDLER_CLASSA_CLREN_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      *reg_offset = ALERT_HANDLER_CLASSB_CLREN_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      *reg_offset = ALERT_HANDLER_CLASSC_CLREN_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      *reg_offset = ALERT_HANDLER_CLASSD_CLREN_REG_OFFSET;
      break;
    default:
      return false;
  }
  return true;
}

dif_alert_handler_result_t dif_alert_handler_escalation_can_clear(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    bool *can_clear) {
  if (handler == NULL || can_clear == NULL) {
    return kDifAlertHandlerBadArg;
  }

  ptrdiff_t reg_offset;
  if (!get_clear_enable_reg_offset(alert_class, &reg_offset)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr, reg_offset);
  *can_clear =
      bitfield_bit32_read(reg, ALERT_HANDLER_CLASSA_CLREN_CLASSA_CLREN_BIT);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_escalation_disable_clearing(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  ptrdiff_t reg_offset;
  if (!get_clear_enable_reg_offset(alert_class, &reg_offset)) {
    return kDifAlertHandlerBadArg;
  }

  uint32_t reg = bitfield_bit32_write(
      0, ALERT_HANDLER_CLASSA_CLREN_CLASSA_CLREN_BIT, true);
  mmio_region_write32(handler->params.base_addr, reg_offset, reg);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_escalation_clear(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class) {
  if (handler == NULL) {
    return kDifAlertHandlerBadArg;
  }

  ptrdiff_t reg_offset;
  switch (alert_class) {
    case kDifAlertHandlerClassA:
      reg_offset = ALERT_HANDLER_CLASSA_CLR_REG_OFFSET;
      break;
    case kDifAlertHandlerClassB:
      reg_offset = ALERT_HANDLER_CLASSB_CLR_REG_OFFSET;
      break;
    case kDifAlertHandlerClassC:
      reg_offset = ALERT_HANDLER_CLASSC_CLR_REG_OFFSET;
      break;
    case kDifAlertHandlerClassD:
      reg_offset = ALERT_HANDLER_CLASSD_CLR_REG_OFFSET;
      break;
    default:
      return kDifAlertHandlerBadArg;
  }

  uint32_t reg =
      bitfield_bit32_write(0, ALERT_HANDLER_CLASSA_CLR_CLASSA_CLR_BIT, true);
  mmio_region_write32(handler->params.base_addr, reg_offset, reg);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_get_accumulator(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    uint16_t *alerts) {
  if (handler == NULL || alerts == NULL) {
    return kDifAlertHandlerBadArg;
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
      return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr, reg_offset);
  *alerts = bitfield_field32_read(reg, field);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_get_escalation_counter(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    uint32_t *cycles) {
  if (handler == NULL || cycles == NULL) {
    return kDifAlertHandlerBadArg;
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
      return kDifAlertHandlerBadArg;
  }

  *cycles = mmio_region_read32(handler->params.base_addr, reg_offset);

  return kDifAlertHandlerOk;
}

dif_alert_handler_result_t dif_alert_handler_get_class_state(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    dif_alert_handler_class_state_t *state) {
  if (handler == NULL || state == NULL) {
    return kDifAlertHandlerBadArg;
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
      return kDifAlertHandlerBadArg;
  }

  uint32_t reg = mmio_region_read32(handler->params.base_addr, reg_offset);
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
      return kDifAlertHandlerError;
  }

  return kDifAlertHandlerOk;
}
