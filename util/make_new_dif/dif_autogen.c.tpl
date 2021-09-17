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
    2. list[irq]: See util/make_new_dif.py for the definition of the `irq` obj.
</%doc>

<%def name="mmio_region_read32(intr_reg_upper)">mmio_region_read32(
  ${ip.name_snake}->base_addr, 
  ${ip.name_upper}_INTR_${intr_reg_upper}_REG_OFFSET);
</%def>

<%def name="mmio_region_write32(intr_reg_upper, value)">mmio_region_write32(
  ${ip.name_snake}->base_addr, 
  ${ip.name_upper}_INTR_${intr_reg_upper}_REG_OFFSET,
  ${value});
</%def>

// This file is auto-generated.

#include "sw/device/lib/dif/dif_${ip.name_snake}.h"

#include "${ip.name_snake}_regs.h"  // Generated.

/**
 * Get the corresponding interrupt register bit offset. INTR_STATE,
 * INTR_ENABLE and INTR_TEST registers have the same bit offsets, so this
 * routine can be reused.
 */
static bool ${ip.name_snake}_get_irq_bit_index(
  dif_${ip.name_snake}_irq_t irq,
  bitfield_bit32_index_t *index_out) {

  switch (irq) {
% for irq in irqs:
    case kDif${ip.name_camel}Irq${irq.name_camel}:
      *index_out = ${ip.name_upper}_INTR_STATE_${irq.name_upper}_BIT;
      break;
% endfor
    default:
      return false;
  }

  return true;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_get_state(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_state_snapshot_t *snapshot) {

  if (${ip.name_snake} == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  *snapshot = ${mmio_region_read32("STATE")}

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

  uint32_t intr_state_reg = ${mmio_region_read32("STATE")}
  *is_pending = bitfield_bit32_read(intr_state_reg, index);

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
  ${mmio_region_write32("STATE", "intr_state_reg")}

  return kDifOk;
}

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

  uint32_t intr_enable_reg = ${mmio_region_read32("ENABLE")}
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

  uint32_t intr_enable_reg = ${mmio_region_read32("ENABLE")}
  bool enable_bit = (state == kDifToggleEnabled) ? true : false;
  intr_enable_reg = bitfield_bit32_write(intr_enable_reg, index, enable_bit);
  ${mmio_region_write32("ENABLE", "intr_enable_reg")}

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_force(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_t irq) {

  if (${ip.name_snake} == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t index;
  if (!${ip.name_snake}_get_irq_bit_index(irq, &index)) {
    return kDifBadArg;
  }

  uint32_t intr_test_reg = bitfield_bit32_write(0, index, true);
  ${mmio_region_write32("TEST", "intr_test_reg")}

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_disable_all(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot) {

  if (${ip.name_snake} == NULL) {
    return kDifBadArg;
  }

  // Pass the current interrupt state to the caller, if requested.
  if (snapshot != NULL) {
    *snapshot = ${mmio_region_read32("ENABLE")}
  }

  // Disable all interrupts.
  ${mmio_region_write32("ENABLE", "0u")}

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_restore_all(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  const dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot) {

  if (${ip.name_snake} == NULL || snapshot == NULL) {
    return kDifBadArg;
  }

  ${mmio_region_write32("ENABLE", "*snapshot")}

  return kDifOk;
}
