// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rv_plic.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "rv_plic_regs.h"  // Generated.

const uint32_t kDifRvPlicMinPriority = 0;
const uint32_t kDifRvPlicMaxPriority = RV_PLIC_PRIO0_PRIO0_MASK;

/**
 * PLIC register info.
 *
 * This data type is used to store IRQ source bit offset within a register,
 * and the offset of this register inside the PLIC.
 */
typedef struct plic_reg_info {
  ptrdiff_t offset;
  bitfield_bit32_index_t bit_index;
} plic_reg_info_t;

/**
 * Get an IE, IP or LE register offset (IE0_0, IE01, ...) from an IRQ source ID.
 *
 * With more than 32 IRQ sources, there is a multiple of these registers to
 * accommodate all the bits (1 bit per IRQ source). This function calculates
 * the offset for a specific IRQ source ID (ID 32 would be IE01, ...).
 */
static ptrdiff_t plic_offset_from_reg0(dif_rv_plic_irq_id_t irq) {
  uint8_t register_index = (uint8_t)(irq / RV_PLIC_PARAM_REG_WIDTH);
  return register_index * sizeof(uint32_t);
}

/**
 * Get an IE, IP, LE register bit index from an IRQ source ID.
 *
 * With more than 32 IRQ sources, there is a multiple of these registers to
 * accommodate all the bits (1 bit per IRQ source). This function calculates
 * the bit position within a register for a specific IRQ source ID (ID 32 would
 * be bit 0).
 */
static uint8_t plic_irq_bit_index(dif_rv_plic_irq_id_t irq) {
  return irq % RV_PLIC_PARAM_REG_WIDTH;
}

/**
 * Get the address of the first target N interrupt enable register (IEN0).
 */
static ptrdiff_t plic_irq_enable_base_for_target(dif_rv_plic_target_t target) {
  ptrdiff_t range = RV_PLIC_IE0_MULTIREG_COUNT * sizeof(uint32_t);
  return RV_PLIC_IE0_0_REG_OFFSET + (range * (ptrdiff_t)target);
}

/**
 * Get the address of the first target N software interrupt register (MSIPN).
 */
static ptrdiff_t plic_software_irq_base_for_target(
    dif_rv_plic_target_t target) {
  return RV_PLIC_MSIP0_REG_OFFSET + (ptrdiff_t)(target * sizeof(uint32_t));
}

/**
 * Get the address of the first target N threshold register (THRESHOLDN).
 */
static ptrdiff_t plic_threshold_base_for_target(dif_rv_plic_target_t target) {
  return RV_PLIC_THRESHOLD0_REG_OFFSET + (ptrdiff_t)(target * sizeof(uint32_t));
}

/**
 * Get the address of the first target N claim complete register (CCN).
 */
static ptrdiff_t plic_claim_complete_base_for_target(
    dif_rv_plic_target_t target) {
  return RV_PLIC_CC0_REG_OFFSET + (ptrdiff_t)(target * sizeof(uint32_t));
}

/**
 * Get a target and an IRQ source specific Interrupt Enable register info.
 */
static plic_reg_info_t plic_irq_enable_reg_info(dif_rv_plic_irq_id_t irq,
                                                dif_rv_plic_target_t target) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  return (plic_reg_info_t){
      .offset = plic_irq_enable_base_for_target(target) + offset,
      .bit_index = plic_irq_bit_index(irq),
  };
}

/**
 * Get an IRQ source specific Interrupt Pending register info.
 */
static plic_reg_info_t plic_irq_pending_reg_info(dif_rv_plic_irq_id_t irq) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  return (plic_reg_info_t){
      .offset = RV_PLIC_IP_0_REG_OFFSET + offset,
      .bit_index = plic_irq_bit_index(irq),
  };
}

/**
 * Get a PRIO register offset (PRIO0, PRIO1, ...) from an IRQ source ID.
 *
 * There is one PRIO register per IRQ source, this function calculates the IRQ
 * source specific PRIO register offset.
 */
static ptrdiff_t plic_priority_reg_offset(dif_rv_plic_irq_id_t irq) {
  ptrdiff_t offset = (ptrdiff_t)(irq * sizeof(uint32_t));
  return RV_PLIC_PRIO0_REG_OFFSET + offset;
}

dif_result_t dif_rv_plic_reset(const dif_rv_plic_t *plic) {
  if (plic == NULL) {
    return kDifBadArg;
  }

  // Clear all of the priority registers.
  for (uint32_t i = 0; i < RV_PLIC_PARAM_NUM_SRC; ++i) {
    ptrdiff_t offset = plic_priority_reg_offset(i);
    mmio_region_write32(plic->base_addr, offset, 0);
  }

  // Clear all of the target related registers.
  for (dif_rv_plic_target_t target = 0; target < RV_PLIC_PARAM_NUM_TARGET;
       ++target) {
    // Clear interrupt enable registers.
    ptrdiff_t offset = plic_irq_enable_base_for_target(target);
    for (size_t i = 0; i < RV_PLIC_IE0_MULTIREG_COUNT; ++i) {
      ptrdiff_t multireg_offset = offset + (ptrdiff_t)(i * sizeof(uint32_t));
      mmio_region_write32(plic->base_addr, multireg_offset, 0);
    }

    // Clear threshold registers.
    offset = plic_threshold_base_for_target(target);
    mmio_region_write32(plic->base_addr, offset, 0);

    // Clear software interrupt registers.
    offset = plic_software_irq_base_for_target(target);
    mmio_region_write32(plic->base_addr, offset, 0);
  }

  return kDifOk;
}

dif_result_t dif_rv_plic_irq_get_enabled(const dif_rv_plic_t *plic,
                                         dif_rv_plic_irq_id_t irq,
                                         dif_rv_plic_target_t target,
                                         dif_toggle_t *state) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUM_SRC ||
      target >= RV_PLIC_PARAM_NUM_TARGET) {
    return kDifBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_enable_reg_info(irq, target);

  uint32_t reg = mmio_region_read32(plic->base_addr, reg_info.offset);
  bool is_enabled = bitfield_bit32_read(reg, reg_info.bit_index);
  *state = is_enabled ? kDifToggleEnabled : kDifToggleDisabled;

  return kDifOk;
}

dif_result_t dif_rv_plic_irq_set_enabled(const dif_rv_plic_t *plic,
                                         dif_rv_plic_irq_id_t irq,
                                         dif_rv_plic_target_t target,
                                         dif_toggle_t state) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUM_SRC ||
      target >= RV_PLIC_PARAM_NUM_TARGET) {
    return kDifBadArg;
  }

  bool flag;
  switch (state) {
    case kDifToggleEnabled:
      flag = true;
      break;
    case kDifToggleDisabled:
      flag = false;
      break;
    default:
      return kDifBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_enable_reg_info(irq, target);

  uint32_t reg = mmio_region_read32(plic->base_addr, reg_info.offset);
  reg = bitfield_bit32_write(reg, reg_info.bit_index, flag);
  mmio_region_write32(plic->base_addr, reg_info.offset, reg);

  return kDifOk;
}

dif_result_t dif_rv_plic_irq_set_priority(const dif_rv_plic_t *plic,
                                          dif_rv_plic_irq_id_t irq,
                                          uint32_t priority) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUM_SRC ||
      priority > kDifRvPlicMaxPriority) {
    return kDifBadArg;
  }

  ptrdiff_t offset = plic_priority_reg_offset(irq);
  mmio_region_write32(plic->base_addr, offset, priority);

  return kDifOk;
}

dif_result_t dif_rv_plic_target_set_threshold(const dif_rv_plic_t *plic,
                                              dif_rv_plic_target_t target,
                                              uint32_t threshold) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUM_TARGET ||
      threshold > kDifRvPlicMaxPriority) {
    return kDifBadArg;
  }

  ptrdiff_t threshold_offset = plic_threshold_base_for_target(target);
  mmio_region_write32(plic->base_addr, threshold_offset, threshold);

  return kDifOk;
}

dif_result_t dif_rv_plic_irq_is_pending(const dif_rv_plic_t *plic,
                                        dif_rv_plic_irq_id_t irq,
                                        bool *is_pending) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUM_SRC || is_pending == NULL) {
    return kDifBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_pending_reg_info(irq);
  uint32_t reg = mmio_region_read32(plic->base_addr, reg_info.offset);
  *is_pending = bitfield_bit32_read(reg, reg_info.bit_index);

  return kDifOk;
}

dif_result_t dif_rv_plic_irq_claim(const dif_rv_plic_t *plic,
                                   dif_rv_plic_target_t target,
                                   dif_rv_plic_irq_id_t *claim_data) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUM_TARGET ||
      claim_data == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t claim_complete_reg = plic_claim_complete_base_for_target(target);
  *claim_data = mmio_region_read32(plic->base_addr, claim_complete_reg);

  return kDifOk;
}

dif_result_t dif_rv_plic_irq_complete(const dif_rv_plic_t *plic,
                                      dif_rv_plic_target_t target,
                                      dif_rv_plic_irq_id_t complete_data) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUM_TARGET) {
    return kDifBadArg;
  }

  // Write back the claimed IRQ ID to the target specific CC register,
  // to notify the PLIC of the IRQ completion.
  ptrdiff_t claim_complete_reg = plic_claim_complete_base_for_target(target);
  mmio_region_write32(plic->base_addr, claim_complete_reg, complete_data);

  return kDifOk;
}

dif_result_t dif_rv_plic_software_irq_force(const dif_rv_plic_t *plic,
                                            dif_rv_plic_target_t target) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUM_TARGET) {
    return kDifBadArg;
  }

  ptrdiff_t msip_offset = plic_software_irq_base_for_target(target);
  mmio_region_write32(plic->base_addr, msip_offset, 1);

  return kDifOk;
}

dif_result_t dif_rv_plic_software_irq_acknowledge(const dif_rv_plic_t *plic,
                                                  dif_rv_plic_target_t target) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUM_TARGET) {
    return kDifBadArg;
  }

  ptrdiff_t msip_offset = plic_software_irq_base_for_target(target);
  mmio_region_write32(plic->base_addr, msip_offset, 0);

  return kDifOk;
}

dif_result_t dif_rv_plic_software_irq_is_pending(const dif_rv_plic_t *plic,
                                                 dif_rv_plic_target_t target,
                                                 bool *is_pending) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUM_TARGET ||
      is_pending == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t msip_offset = plic_software_irq_base_for_target(target);
  uint32_t register_value = mmio_region_read32(plic->base_addr, msip_offset);

  *is_pending = (register_value == 1) ? true : false;

  return kDifOk;
}
