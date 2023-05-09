// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%doc>
    This file is the "auto-generated DIF library implementation template", which
    provides implementations of some mandatory DIFs that are similar across all
    IPs. When rendered, this template implements the DIFs defined in the
    auto-generated DIF header file (see util/make_new_dif/dif_autogen.inc.tpl).

    Note, this template requires the following Python objects to be passed:

    1. ip: See util/make_new_dif.py for the definition of the `ip` obj.
</%doc>

<%def name="mmio_region_read32(intr_reg_offset)">mmio_region_read32(
    ${ip.name_snake}->base_addr,
    (ptrdiff_t)${intr_reg_offset});
</%def>

<%def name="mmio_region_write32(intr_reg_offset, value)">mmio_region_write32(
    ${ip.name_snake}->base_addr,
    (ptrdiff_t)${intr_reg_offset},
    ${value});
</%def>

${autogen_banner}

#include <stdint.h>

#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/autogen/dif_${ip.name_snake}_autogen.h"

#include "${ip.name_snake}_regs.h"  // Generated.

% if ip.name_snake == "aon_timer":
  #include <assert.h>

  % for irq in ip.irqs:
    static_assert(${ip.name_upper}_INTR_STATE_${irq.name_upper}_BIT == 
                  ${ip.name_upper}_INTR_TEST_${irq.name_upper}_BIT,
                  "Expected IRQ bit offsets to match across STATE/TEST regs.");
  % endfor

% elif ip.name_snake == "rv_timer":
  #include <assert.h>

  % for irq in ip.irqs:
    static_assert(${ip.name_upper}_INTR_STATE0_IS_${loop.index}_BIT == 
                  ${ip.name_upper}_INTR_ENABLE0_IE_${loop.index}_BIT,
                  "Expected IRQ bit offsets to match across STATE/ENABLE regs.");
    static_assert(${ip.name_upper}_INTR_STATE0_IS_${loop.index}_BIT == 
                  ${ip.name_upper}_INTR_TEST0_T_${loop.index}_BIT,
                  "Expected IRQ bit offsets to match across STATE/ENABLE regs.");
  % endfor
% endif

OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_init(
  mmio_region_t base_addr,
  dif_${ip.name_snake}_t *${ip.name_snake}) {
  if (${ip.name_snake} == NULL) {
    return kDifBadArg;
  }

  ${ip.name_snake}->base_addr = base_addr;

  return kDifOk;
}

% if ip.alerts:
  dif_result_t dif_${ip.name_snake}_alert_force(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_alert_t alert) {
  if (${ip.name_snake} == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t alert_idx;
  switch (alert) {
  % for alert in ip.alerts:
    case kDif${ip.name_camel}Alert${alert.name_camel}:
      alert_idx = ${ip.name_upper}_ALERT_TEST_${alert.name_upper}_BIT;
      break;
  % endfor
    default:
      return kDifBadArg;
  }

  uint32_t alert_test_reg = bitfield_bit32_write(0, alert_idx, true);
  ${mmio_region_write32(ip.name_upper + "_ALERT_TEST_REG_OFFSET", "alert_test_reg")}

  return kDifOk;
}
% endif

% if ip.irqs:
  % if ip.name_snake == "rv_timer":
    typedef enum dif_${ip.name_snake}_intr_reg {
      kDif${ip.name_camel}IntrRegState = 0,
      kDif${ip.name_camel}IntrRegEnable = 1,
      kDif${ip.name_camel}IntrRegTest = 2,
    } dif_${ip.name_snake}_intr_reg_t;

    static bool ${ip.name_snake}_get_irq_reg_offset(
      dif_${ip.name_snake}_intr_reg_t intr_reg,
      dif_${ip.name_snake}_irq_t irq,
      uint32_t *intr_reg_offset) {

      switch (intr_reg) {

      % for intr_reg_str in ["State", "Enable", "Test"]:
        case kDif${ip.name_camel}IntrReg${intr_reg_str}:
          switch (irq) {
          % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
            % for timer_id in range(int(ip.parameters["N_TIMERS"].default)):
              case kDif${ip.name_camel}IrqTimerExpiredHart${hart_id}Timer${timer_id}:
                *intr_reg_offset = ${ip.name_upper}_INTR_${intr_reg_str.upper()}${hart_id}_REG_OFFSET;
                break;
            % endfor
          % endfor
            default:
              return false;
          }
          break;
      % endfor
        default:
          return false;
      }

      return true;
    }
  % endif

  /**
   * Get the corresponding interrupt register bit offset of the IRQ.
   */
  ## If the IP's HJSON does NOT have a field "no_auto_intr_regs = true", then
  ## the "<ip>_INTR_COMMON_<irq>_BIT" macro can be used. Otherwise, special
  ## cases will exist, as templated below.
  static bool ${ip.name_snake}_get_irq_bit_index(
    dif_${ip.name_snake}_irq_t irq,
    bitfield_bit32_index_t *index_out) {

    switch (irq) {
  % for irq in ip.irqs:
    ## This handles the GPIO IP case where there is a multi-bit interrupt.
    % if irq.width > 1:
      % for irq_idx in range(irq.width):
        case kDif${ip.name_camel}Irq${irq.name_camel}${irq_idx}:
          *index_out = ${irq_idx};
          break;
      % endfor
    ## This handles all other IPs.
    % else:
      case kDif${ip.name_camel}Irq${irq.name_camel}:
      ## This handles the RV Timer IP.
      % if ip.name_snake == "aon_timer":
        *index_out = ${ip.name_upper}_INTR_STATE_${irq.name_upper}_BIT;
      ## This handles the RV Timer IP.
      % elif ip.name_snake == "rv_timer":
        *index_out = ${ip.name_upper}_INTR_STATE0_IS_${loop.index}_BIT;
      ## This handles all other IPs that do not have the "no_auto_intr_regs" in
      ## their HJSON files.
      % else:
        *index_out = ${ip.name_upper}_INTR_COMMON_${irq.name_upper}_BIT;
      % endif
        break;
    % endif
  % endfor
      default:
        return false;
    }

    return true;
  }

  static dif_irq_type_t irq_types[] = {
  % for irq in ip.irqs:
    ## This handles the GPIO IP case where there is a multi-bit interrupt.
    % if irq.width > 1:
      % if irq.type == "event":
        ${', '.join(["kDifIrqTypeEvent"] * irq.width) + ','}
      % else:
        ${', '.join(["kDifIrqTypeStatus"] * irq.width) + ','}
      % endif
    ## This handles all other IPs.
    % else:
      % if irq.type == "event":
        kDifIrqTypeEvent,
      % else:
        kDifIrqTypeStatus,
      % endif
    % endif
  % endfor
  };

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_get_type(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    dif_irq_type_t *type) {

    % if ip.irqs[-1].width == 1:
      if (${ip.name_snake} == NULL ||
          type == NULL ||
          irq == kDif${ip.name_camel}Irq${ip.irqs[-1].name_camel} + 1) {
    % else:
      if (${ip.name_snake} == NULL ||
          type == NULL ||
          irq == kDif${ip.name_camel}Irq${ip.irqs[-1].name_camel}${ip.irqs[-1].width - 1} + 1) {
    % endif
      return kDifBadArg;
    }

    *type = irq_types[irq];

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_get_state(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    dif_${ip.name_snake}_irq_state_snapshot_t *snapshot) {

    if (${ip.name_snake} == NULL || snapshot == NULL) {
      return kDifBadArg;
    }

  % if ip.name_snake == "rv_timer":
    switch (hart_id) {
      % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
        case ${hart_id}:
          *snapshot = ${mmio_region_read32("RV_TIMER_INTR_STATE%d_REG_OFFSET" % hart_id)}
          break;
      % endfor
      default:
        return kDifBadArg;
    }
  % else:
    *snapshot = ${mmio_region_read32(ip.name_upper + "_INTR_STATE_REG_OFFSET")}
  % endif

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_acknowledge_state(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    dif_${ip.name_snake}_irq_state_snapshot_t snapshot) {
    if (${ip.name_snake} == NULL) {
      return kDifBadArg;
    }

  % if ip.name_snake == "rv_timer":
    switch (hart_id) {
      % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
        case ${hart_id}:
          ${mmio_region_write32("RV_TIMER_INTR_STATE%d_REG_OFFSET" % hart_id, "snapshot")}
          break;
      % endfor
      default:
        return kDifBadArg;
    }
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_STATE_REG_OFFSET", "snapshot")}
  % endif

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_is_pending(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    bool *is_pending) {

    if (${ip.name_snake} == NULL || is_pending == NULL) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t index;
    if (!${ip.name_snake}_get_irq_bit_index(irq, &index)) {
      return kDifBadArg;
    }

  % if ip.name_snake == "rv_timer":
    uint32_t reg_offset = 0;
    if (!${ip.name_snake}_get_irq_reg_offset(kDif${ip.name_camel}IntrRegState,
                                             irq,
                                             &reg_offset)) {
      return kDifBadArg;
    }
    uint32_t intr_state_reg = ${mmio_region_read32("reg_offset")}
  % else:
    uint32_t intr_state_reg = ${mmio_region_read32(ip.name_upper + "_INTR_STATE_REG_OFFSET")}
  % endif

    *is_pending = bitfield_bit32_read(intr_state_reg, index);

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_acknowledge_all(
    const dif_${ip.name_snake}_t *${ip.name_snake}
  % if ip.name_snake == "rv_timer":
    , uint32_t hart_id
  % endif
    ) {

    if (${ip.name_snake} == NULL) {
      return kDifBadArg;
    }

    // Writing to the register clears the corresponding bits (Write-one clear).
  % if ip.name_snake == "rv_timer":
    switch (hart_id) {
      % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
        case ${hart_id}:
          ${mmio_region_write32("RV_TIMER_INTR_STATE%d_REG_OFFSET" % hart_id, "UINT32_MAX")}
          break;
      % endfor
      default:
        return kDifBadArg;
    }
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_STATE_REG_OFFSET", "UINT32_MAX")}
  % endif

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_acknowledge(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq) {

    if (${ip.name_snake} == NULL) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t index;
    if (!${ip.name_snake}_get_irq_bit_index(irq, &index)) {
      return kDifBadArg;
    }

    // Writing to the register clears the corresponding bits (Write-one clear).
    uint32_t intr_state_reg = bitfield_bit32_write(0, index, true);
  % if ip.name_snake == "rv_timer":
    uint32_t reg_offset = 0;
    if (!${ip.name_snake}_get_irq_reg_offset(kDif${ip.name_camel}IntrRegState,
                                             irq,
                                             &reg_offset)) {
      return kDifBadArg;
    }
    ${mmio_region_write32("reg_offset", "intr_state_reg")}
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_STATE_REG_OFFSET", "intr_state_reg")}
  % endif

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_force(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    const bool val) {

    if (${ip.name_snake} == NULL) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t index;
    if (!${ip.name_snake}_get_irq_bit_index(irq, &index)) {
      return kDifBadArg;
    }

    uint32_t intr_test_reg = bitfield_bit32_write(0, index, val);
  % if ip.name_snake == "rv_timer":
    uint32_t reg_offset = 0;
    if (!${ip.name_snake}_get_irq_reg_offset(kDif${ip.name_camel}IntrRegTest,
                                             irq,
                                             &reg_offset)) {
      return kDifBadArg;
    }
    ${mmio_region_write32("reg_offset", "intr_test_reg")}
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_TEST_REG_OFFSET", "intr_test_reg")}
  % endif

    return kDifOk;
  }

% if ip.name_snake != "aon_timer":
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_get_enabled(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    dif_toggle_t *state) {
    
    if (${ip.name_snake} == NULL || state == NULL) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t index;
    if (!${ip.name_snake}_get_irq_bit_index(irq, &index)) {
      return kDifBadArg;
    }

  % if ip.name_snake == "rv_timer":
    uint32_t reg_offset = 0;
    if (!${ip.name_snake}_get_irq_reg_offset(kDif${ip.name_camel}IntrRegEnable,
                                             irq,
                                             &reg_offset)) {
      return kDifBadArg;
    }
    uint32_t intr_enable_reg = ${mmio_region_read32("reg_offset")}
  % else:
    uint32_t intr_enable_reg = ${mmio_region_read32(ip.name_upper + "_INTR_ENABLE_REG_OFFSET")}
  % endif

    bool is_enabled = bitfield_bit32_read(intr_enable_reg, index);
    *state = is_enabled ? 
      kDifToggleEnabled : kDifToggleDisabled;

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_set_enabled(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    dif_toggle_t state) {

    if (${ip.name_snake} == NULL) {
      return kDifBadArg;
    }

    bitfield_bit32_index_t index;
    if (!${ip.name_snake}_get_irq_bit_index(irq, &index)) {
      return kDifBadArg;
    }

  % if ip.name_snake == "rv_timer":
    uint32_t reg_offset = 0;
    if (!${ip.name_snake}_get_irq_reg_offset(kDif${ip.name_camel}IntrRegEnable,
                                             irq,
                                             &reg_offset)) {
      return kDifBadArg;
    }
    uint32_t intr_enable_reg = ${mmio_region_read32("reg_offset")}
  % else:
    uint32_t intr_enable_reg = ${mmio_region_read32(ip.name_upper + "_INTR_ENABLE_REG_OFFSET")}
  % endif

    bool enable_bit = (state == kDifToggleEnabled) ? true : false;
    intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  % if ip.name_snake == "rv_timer":
    ${mmio_region_write32("reg_offset", "intr_enable_reg")}
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_ENABLE_REG_OFFSET", "intr_enable_reg")}
  % endif

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_disable_all(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot) {

    if (${ip.name_snake} == NULL) {
      return kDifBadArg;
    }

    // Pass the current interrupt state to the caller, if requested.
    if (snapshot != NULL) {
    % if ip.name_snake == "rv_timer":
      switch (hart_id) {
        % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
          case ${hart_id}:
            *snapshot = ${mmio_region_read32("RV_TIMER_INTR_ENABLE%d_REG_OFFSET" % hart_id)}
            break;
        % endfor
        default:
          return kDifBadArg;
      }
    % else:
      *snapshot = ${mmio_region_read32(ip.name_upper + "_INTR_ENABLE_REG_OFFSET")}
    % endif
    }

    // Disable all interrupts.
  % if ip.name_snake == "rv_timer":
    switch (hart_id) {
      % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
        case ${hart_id}:
          ${mmio_region_write32("RV_TIMER_INTR_ENABLE%d_REG_OFFSET" % hart_id, "0u")}
          break;
      % endfor
      default:
        return kDifBadArg;
    }
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_ENABLE_REG_OFFSET", "0u")}
  % endif

    return kDifOk;
  }

  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_restore_all(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    const dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot) {

    if (${ip.name_snake} == NULL || snapshot == NULL) {
      return kDifBadArg;
    }

  % if ip.name_snake == "rv_timer":
    switch (hart_id) {
      % for hart_id in range(int(ip.parameters["N_HARTS"].default)):
        case ${hart_id}:
          ${mmio_region_write32("RV_TIMER_INTR_ENABLE%d_REG_OFFSET" % hart_id, "*snapshot")}
          break;
      % endfor
      default:
        return kDifBadArg;
    }
  % else:
    ${mmio_region_write32(ip.name_upper + "_INTR_ENABLE_REG_OFFSET", "*snapshot")}
  % endif

    return kDifOk;
  }
% endif

% endif
