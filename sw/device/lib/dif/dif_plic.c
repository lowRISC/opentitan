// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_plic.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "rv_plic_regs.h"  // Generated.

// If either of these static assertions fail, then the assumptions in this DIF
// implementation should be revisited. In particular, `kPlicTargets`
// may need updating,
_Static_assert(RV_PLIC_PARAM_NUMSRC == 89,
               "PLIC instantiation parameters have changed.");
_Static_assert(RV_PLIC_PARAM_NUMTARGET == 1,
               "PLIC instantiation parameters have changed.");

const uint32_t kDifPlicMinPriority = 0;
const uint32_t kDifPlicMaxPriority = 0x3u;

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
 * PLIC target specific register offsets.
 *
 * PLIC is designed to support multiple targets, and every target has a set
 * of its own registers. This data type is used to store PLIC target specific
 * register offsets.
 */
typedef struct plic_target_reg_offset {
  /**
   * IRQ enable register offset for this target.
   */
  ptrdiff_t irq_enable;
  /**
   * Claim/complete register offset for this target.
   */
  ptrdiff_t claim_complete;
  /**
   * Threshold register offset for this target.
   */
  ptrdiff_t threshold;
  /**
   * Software interrupt register offset.
   */
  ptrdiff_t msip;
} plic_target_reg_offset_t;

// This array gives a way of getting the target-specific register offsets from
// a `dif_plic_target_t`.
//
// There should be an instance of `plic_target_reg_offset_t` for each possible
// target, so there should be `RV_PLIC_PARAM_NUMTARGET` entries in this array.
// The `i`th entry should contain the offsets of the `i`th target specific
// registers:
// - `RV_PLIC_IE<i>_0_REG_OFFSET` (the first IE reg for target `i`).
// - `RV_PLIC_CC<i>_REG_OFFSET`
// - `RV_PLIC_THRESHOLD<i>_REG_OFFSET`
// - `RV_PLIC_MSIP<i>_REG_OFFSET`
static const plic_target_reg_offset_t kPlicTargets[] = {
    [0] =
        {
            .irq_enable = RV_PLIC_IE0_0_REG_OFFSET,
            .claim_complete = RV_PLIC_CC0_REG_OFFSET,
            .threshold = RV_PLIC_THRESHOLD0_REG_OFFSET,
            .msip = RV_PLIC_MSIP0_REG_OFFSET,
        },
};
_Static_assert(sizeof(kPlicTargets) / sizeof(*kPlicTargets) ==
                   RV_PLIC_PARAM_NUMTARGET,
               "There should be an entry in kPlicTargets for every target");

/**
 * Get an IE, IP or LE register offset (IE0_0, IE01, ...) from an IRQ source ID.
 *
 * With more than 32 IRQ sources, there is a multiple of these registers to
 * accommodate all the bits (1 bit per IRQ source). This function calculates
 * the offset for a specific IRQ source ID (ID 32 would be IE01, ...).
 */
static ptrdiff_t plic_offset_from_reg0(dif_plic_irq_id_t irq) {
  uint8_t register_index = irq / RV_PLIC_PARAM_REG_WIDTH;
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
static uint8_t plic_irq_bit_index(dif_plic_irq_id_t irq) {
  return irq % RV_PLIC_PARAM_REG_WIDTH;
}

/**
 * Get a target and an IRQ source specific Interrupt Enable register info.
 */
static plic_reg_info_t plic_irq_enable_reg_info(dif_plic_irq_id_t irq,
                                                dif_plic_target_t target) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  return (plic_reg_info_t){
      .offset = kPlicTargets[target].irq_enable + offset,
      .bit_index = plic_irq_bit_index(irq),
  };
}

/**
 * Get an IRQ source specific Level/Edge register info.
 */
static plic_reg_info_t plic_irq_trigger_type_reg_info(dif_plic_irq_id_t irq) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  return (plic_reg_info_t){
      .offset = RV_PLIC_LE_0_REG_OFFSET + offset,
      .bit_index = plic_irq_bit_index(irq),
  };
}

/**
 * Get an IRQ source specific Interrupt Pending register info.
 */
static plic_reg_info_t plic_irq_pending_reg_info(dif_plic_irq_id_t irq) {
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
static ptrdiff_t plic_priority_reg_offset(dif_plic_irq_id_t irq) {
  ptrdiff_t offset = irq * sizeof(uint32_t);
  return RV_PLIC_PRIO0_REG_OFFSET + offset;
}

/**
 * Reset the requested PLIC peripheral.
 *
 * This function resets all the relevant PLIC registers, apart from the CC
 * register. There is no reliable way of knowing the ID of an IRQ that has
 * claimed the CC register, so we assume that the previous "owner" of the
 * resource has cleared/completed the CC access.
 */
static void plic_reset(const dif_plic_t *plic) {
  // Clear all of the Interrupt Enable registers.
  for (int i = 0; i < RV_PLIC_IE0_MULTIREG_COUNT; ++i) {
    ptrdiff_t offset = RV_PLIC_IE0_0_REG_OFFSET + (i * sizeof(uint32_t));
    mmio_region_write32(plic->params.base_addr, offset, 0);
  }

  // Clear all of the Level/Edge registers.
  for (int i = 0; i < RV_PLIC_LE_MULTIREG_COUNT; ++i) {
    ptrdiff_t offset = RV_PLIC_LE_0_REG_OFFSET + (i * sizeof(uint32_t));
    mmio_region_write32(plic->params.base_addr, offset, 0);
  }

  // Clear all of the priority registers.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    ptrdiff_t offset = plic_priority_reg_offset(i);
    mmio_region_write32(plic->params.base_addr, offset, 0);
  }

  // Clear all of the target threshold registers.
  for (dif_plic_target_t target = 0; target < RV_PLIC_PARAM_NUMTARGET;
       ++target) {
    ptrdiff_t offset = kPlicTargets[target].threshold;
    mmio_region_write32(plic->params.base_addr, offset, 0);
  }

  // Clear software interrupt pending register.
  mmio_region_write32(plic->params.base_addr, RV_PLIC_MSIP0_REG_OFFSET, 0);
}

dif_plic_result_t dif_plic_init(dif_plic_params_t params, dif_plic_t *plic) {
  if (plic == NULL) {
    return kDifPlicBadArg;
  }

  plic->params = params;

  // TODO: Move this out into its own function.
  plic_reset(plic);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_get_enabled(const dif_plic_t *plic,
                                           dif_plic_irq_id_t irq,
                                           dif_plic_target_t target,
                                           dif_plic_toggle_t *state) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC ||
      target >= RV_PLIC_PARAM_NUMTARGET) {
    return kDifPlicBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_enable_reg_info(irq, target);

  uint32_t reg = mmio_region_read32(plic->params.base_addr, reg_info.offset);
  bool is_enabled = bitfield_bit32_read(reg, reg_info.bit_index);
  *state = is_enabled ? kDifPlicToggleEnabled : kDifPlicToggleDisabled;

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_set_enabled(const dif_plic_t *plic,
                                           dif_plic_irq_id_t irq,
                                           dif_plic_target_t target,
                                           dif_plic_toggle_t state) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC ||
      target >= RV_PLIC_PARAM_NUMTARGET) {
    return kDifPlicBadArg;
  }

  bool flag;
  switch (state) {
    case kDifPlicToggleEnabled:
      flag = true;
      break;
    case kDifPlicToggleDisabled:
      flag = false;
      break;
    default:
      return kDifPlicBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_enable_reg_info(irq, target);

  uint32_t reg = mmio_region_read32(plic->params.base_addr, reg_info.offset);
  reg = bitfield_bit32_write(reg, reg_info.bit_index, flag);
  mmio_region_write32(plic->params.base_addr, reg_info.offset, reg);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_set_trigger(const dif_plic_t *plic,
                                           dif_plic_irq_id_t irq,
                                           dif_plic_irq_trigger_t trigger) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC) {
    return kDifPlicBadArg;
  }

  bool flag;
  switch (trigger) {
    case kDifPlicIrqTriggerEdge:
      flag = true;
      break;
    case kDifPlicIrqTriggerLevel:
      flag = false;
      break;
    default:
      return kDifPlicBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_trigger_type_reg_info(irq);

  uint32_t reg = mmio_region_read32(plic->params.base_addr, reg_info.offset);
  reg = bitfield_bit32_write(reg, reg_info.bit_index, flag);
  mmio_region_write32(plic->params.base_addr, reg_info.offset, reg);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_set_priority(const dif_plic_t *plic,
                                            dif_plic_irq_id_t irq,
                                            uint32_t priority) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC ||
      priority > kDifPlicMaxPriority) {
    return kDifPlicBadArg;
  }

  ptrdiff_t offset = plic_priority_reg_offset(irq);
  mmio_region_write32(plic->params.base_addr, offset, priority);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_target_set_threshold(const dif_plic_t *plic,
                                                dif_plic_target_t target,
                                                uint32_t threshold) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET ||
      threshold > kDifPlicMaxPriority) {
    return kDifPlicBadArg;
  }

  ptrdiff_t threshold_offset = kPlicTargets[target].threshold;
  mmio_region_write32(plic->params.base_addr, threshold_offset, threshold);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_is_pending(const dif_plic_t *plic,
                                          dif_plic_irq_id_t irq,
                                          bool *is_pending) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC || is_pending == NULL) {
    return kDifPlicBadArg;
  }

  plic_reg_info_t reg_info = plic_irq_pending_reg_info(irq);
  uint32_t reg = mmio_region_read32(plic->params.base_addr, reg_info.offset);
  *is_pending = bitfield_bit32_read(reg, reg_info.bit_index);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_claim(const dif_plic_t *plic,
                                     dif_plic_target_t target,
                                     dif_plic_irq_id_t *claim_data) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET || claim_data == NULL) {
    return kDifPlicBadArg;
  }

  ptrdiff_t claim_complete_reg = kPlicTargets[target].claim_complete;
  *claim_data = mmio_region_read32(plic->params.base_addr, claim_complete_reg);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_complete(
    const dif_plic_t *plic, dif_plic_target_t target,
    const dif_plic_irq_id_t *complete_data) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET ||
      complete_data == NULL) {
    return kDifPlicBadArg;
  }

  // Write back the claimed IRQ ID to the target specific CC register,
  // to notify the PLIC of the IRQ completion.
  ptrdiff_t claim_complete_reg = kPlicTargets[target].claim_complete;
  mmio_region_write32(plic->params.base_addr, claim_complete_reg,
                      *complete_data);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_software_irq_force(const dif_plic_t *plic,
                                              dif_plic_target_t target) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET) {
    return kDifPlicBadArg;
  }

  ptrdiff_t msip_offset = kPlicTargets[target].msip;
  mmio_region_write32(plic->params.base_addr, msip_offset, 1);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_software_irq_acknowledge(const dif_plic_t *plic,
                                                    dif_plic_target_t target) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET) {
    return kDifPlicBadArg;
  }

  ptrdiff_t msip_offset = kPlicTargets[target].msip;
  mmio_region_write32(plic->params.base_addr, msip_offset, 0);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_software_irq_is_pending(const dif_plic_t *plic,
                                                   dif_plic_target_t target,
                                                   bool *is_pending) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET || is_pending == NULL) {
    return kDifPlicBadArg;
  }

  ptrdiff_t msip_offset = kPlicTargets[target].msip;
  uint32_t register_value =
      mmio_region_read32(plic->params.base_addr, msip_offset);

  *is_pending = (register_value == 1) ? true : false;

  return kDifPlicOk;
}
