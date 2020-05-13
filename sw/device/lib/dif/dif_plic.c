// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_plic.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "rv_plic_regs.h"  // Generated.
#include "sw/device/lib/base/mmio.h"

// If either of these static assertions fail, then the assumptions in this DIF
// implementation should be revisited. In particular, `plic_target_reg_offsets`
// may need updating,
_Static_assert(RV_PLIC_PARAM_NUMSRC == 81,
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
  ptrdiff_t offset;  /*<< Register offset. */
  uint8_t bit_index; /*<< Bit index within the register. */
} plic_reg_info_t;

/**
 * PLIC target specific register offsets.
 *
 * PLIC is designed to support multiple targets, and every target has a set
 * of its own registers. This data type is used to store PLIC target specific
 * register offsets.
 */
typedef struct plic_target_reg_offset {
  ptrdiff_t ie;        /*<< Interrupt Enable register offset. */
  ptrdiff_t cc;        /*<< Claim/complete register offset. */
  ptrdiff_t threshold; /*<< Threshold register offset. */
} plic_target_reg_offset_t;

// This array gives a way of getting the target-specific register offsets from
// a `dif_plic_target_t`.
//
// There should be an instance of `plic_target_reg_offset_t` for each possible
// target, so there should be `RV_PLIC_PARAM_NUMTARGET` entries in this array.
// The `i`th entry should contain the offsets of the `i`th target specific
// registers:
// - `RV_PLIC_IE<i>0_REG_OFFSET` (the first IE reg for target `i`).
// - `RV_PLIC_CC<i>_REG_OFFSET`
// - `RV_PLIC_THRESHOLD<i>_REG_OFFSET`
static const plic_target_reg_offset_t plic_target_reg_offsets[] = {
        [0] =
            {
                .ie = RV_PLIC_IE00_REG_OFFSET,
                .cc = RV_PLIC_CC0_REG_OFFSET,
                .threshold = RV_PLIC_THRESHOLD0_REG_OFFSET,
            },
};
_Static_assert(
    sizeof(plic_target_reg_offsets) / sizeof(*plic_target_reg_offsets) ==
        RV_PLIC_PARAM_NUMTARGET,
    "There should be an entry in plic_target_reg_offsets for every target");

/**
 * Get an IE, IP or LE register offset (IE00, IE01, ...) from an IRQ source ID.
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
 * the bit position within a register for a specifci IRQ source ID (ID 32 would
 * be bit 0).
 */
static uint8_t plic_reg_bit_index_from_irq_id(dif_plic_irq_id_t irq) {
  return irq % RV_PLIC_PARAM_REG_WIDTH;
}

/**
 * Get a target and an IRQ source specific Interrupt Enable register info.
 */
static void plic_irq_enable_reg_info(dif_plic_irq_id_t irq,
                                     dif_plic_target_t target,
                                     plic_reg_info_t *reg_info) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  reg_info->offset = plic_target_reg_offsets[target].ie + offset;
  reg_info->bit_index = plic_reg_bit_index_from_irq_id(irq);
}

/**
 * Get an IRQ source specific Level/Edge register info.
 */
static void plic_irq_trigger_type_reg_info(dif_plic_irq_id_t irq,
                                           plic_reg_info_t *reg_info) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  reg_info->offset = RV_PLIC_LE0_REG_OFFSET + offset;
  reg_info->bit_index = plic_reg_bit_index_from_irq_id(irq);
}

/**
 * Get an IRQ source specific Interrupt Pending register info.
 */
static void plic_irq_pending_reg_info(dif_plic_irq_id_t irq,
                                      plic_reg_info_t *reg_info) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  reg_info->offset = RV_PLIC_IP0_REG_OFFSET + offset;
  reg_info->bit_index = plic_reg_bit_index_from_irq_id(irq);
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
    ptrdiff_t offset = RV_PLIC_IE00_REG_OFFSET + (i * sizeof(uint32_t));
    mmio_region_write32(plic->base_addr, offset, 0);
  }

  // Clear all of the Level/Edge registers.
  for (int i = 0; i < RV_PLIC_LE_MULTIREG_COUNT; ++i) {
    ptrdiff_t offset = RV_PLIC_LE0_REG_OFFSET + (i * sizeof(uint32_t));
    mmio_region_write32(plic->base_addr, offset, 0);
  }

  // Clear all of the priority registers.
  for (int i = 0; i < RV_PLIC_PARAM_NUMSRC; ++i) {
    ptrdiff_t offset = plic_priority_reg_offset(i);
    mmio_region_write32(plic->base_addr, offset, 0);
  }

  // Clear all of the target threshold registers.
  for (dif_plic_target_t target = 0; target < RV_PLIC_PARAM_NUMTARGET;
       ++target) {
    ptrdiff_t offset = plic_target_reg_offsets[target].threshold;
    mmio_region_write32(plic->base_addr, offset, 0);
  }

  // Clear software interrupt pending register.
  mmio_region_write32(plic->base_addr, RV_PLIC_MSIP0_REG_OFFSET, 0);
}

dif_plic_result_t dif_plic_init(mmio_region_t base_addr, dif_plic_t *plic) {
  if (plic == NULL) {
    return kDifPlicBadArg;
  }

  plic->base_addr = base_addr;

  plic_reset(plic);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_enable_set(const dif_plic_t *plic,
                                          dif_plic_irq_id_t irq,
                                          dif_plic_target_t target,
                                          dif_plic_enable_t enable) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC ||
      target >= RV_PLIC_PARAM_NUMTARGET) {
    return kDifPlicBadArg;
  }

  // Get a target and an IRQ source specific Interrupt Enable register info.
  plic_reg_info_t reg_info;
  plic_irq_enable_reg_info(irq, target, &reg_info);

  if (enable == kDifPlicEnable) {
    mmio_region_nonatomic_set_bit32(plic->base_addr, reg_info.offset,
                                    reg_info.bit_index);
  } else {
    mmio_region_nonatomic_clear_bit32(plic->base_addr, reg_info.offset,
                                      reg_info.bit_index);
  }

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_trigger_type_set(const dif_plic_t *plic,
                                                dif_plic_irq_id_t irq,
                                                dif_plic_enable_t enable) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC) {
    return kDifPlicBadArg;
  }

  // Get an IRQ source specific Level/Edge register info.
  plic_reg_info_t reg_info;
  plic_irq_trigger_type_reg_info(irq, &reg_info);

  if (enable == kDifPlicEnable) {
    mmio_region_nonatomic_set_bit32(plic->base_addr, reg_info.offset,
                                    reg_info.bit_index);
  } else {
    mmio_region_nonatomic_clear_bit32(plic->base_addr, reg_info.offset,
                                      reg_info.bit_index);
  }

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_priority_set(const dif_plic_t *plic,
                                            dif_plic_irq_id_t irq,
                                            uint32_t priority) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC ||
      priority > kDifPlicMaxPriority) {
    return kDifPlicBadArg;
  }

  ptrdiff_t offset = plic_priority_reg_offset(irq);
  mmio_region_write32(plic->base_addr, offset, priority);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_target_threshold_set(const dif_plic_t *plic,
                                                dif_plic_target_t target,
                                                uint32_t threshold) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET ||
      threshold > kDifPlicMaxPriority) {
    return kDifPlicBadArg;
  }

  ptrdiff_t threshold_offset = plic_target_reg_offsets[target].threshold;
  mmio_region_write32(plic->base_addr, threshold_offset, threshold);

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_pending_status_get(const dif_plic_t *plic,
                                                  dif_plic_irq_id_t irq,
                                                  dif_plic_flag_t *status) {
  if (plic == NULL || irq >= RV_PLIC_PARAM_NUMSRC || status == NULL) {
    return kDifPlicBadArg;
  }

  plic_reg_info_t reg_info;
  plic_irq_pending_reg_info(irq, &reg_info);

  if (mmio_region_get_bit32(plic->base_addr, reg_info.offset,
                            reg_info.bit_index)) {
    *status = kDifPlicSet;
  } else {
    *status = kDifPlicUnset;
  }

  return kDifPlicOk;
}

dif_plic_result_t dif_plic_irq_claim(const dif_plic_t *plic,
                                     dif_plic_target_t target,
                                     dif_plic_irq_id_t *claim_data) {
  if (plic == NULL || target >= RV_PLIC_PARAM_NUMTARGET || claim_data == NULL) {
    return kDifPlicBadArg;
  }

  // Get an IRQ ID from the target specific CC register.
  ptrdiff_t cc_offset = plic_target_reg_offsets[target].cc;
  uint32_t irq_id = mmio_region_read32(plic->base_addr, cc_offset);

  // Return the IRQ ID directly.
  *claim_data = irq_id;
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
  ptrdiff_t cc_offset = plic_target_reg_offsets[target].cc;
  mmio_region_write32(plic->base_addr, cc_offset, (uint32_t)*complete_data);

  return kDifPlicOk;
}
