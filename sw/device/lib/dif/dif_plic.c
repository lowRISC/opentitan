// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_plic.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

// Interrupt Pending register offsets from the PLIC base.
#define RV_PLIC_IP0 0x0u
#define RV_PLIC_IP1 0x4u

// Level/Edge register offsets from the PLIC base.
#define RV_PLIC_LE0 0x8u
#define RV_PLIC_LE1 0xCu

// Priority register offsets from the PLIC base.
#define RV_PLIC_PRIO0 0x10u

// Interrupt Enable register offsets from the PLIC base.
#define RV_PLIC_IE00 0x200u
#define RV_PLIC_IE01 0x204u

// Threshold register offsets from the PLIC base.
#define RV_PLIC_THRESHOLD0 0x208u

// Interrupt Claim register offsets from the PLIC base.
#define RV_PLIC_CC0 0x20cu

// The highest interrupt priority.
#define RV_PLIC_MAX_PRIORITY 0x3u

// These defines are used to calculate the IRQ index in IP, LE, IE registers.
// These registers are 32bit wide, and in order to accommodate all the IRQs,
// multiple of the same type registers are defined (IE00, IE01, ...). For
// example, IRQ ID 33 corresponds to bit 0 in registers IP1, LE1, IE01.
#define PLIC_ID_TO_INDEX_REG_SIZE 32u
#define PLIC_ID_TO_INDEX(id) ((uint32_t)id - 1)

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

/**
 * PLIC peripheral IRQ range.
 *
 * PLIC IRQ source IDs are grouped together by a peripheral they belong to.
 * Meaning that all IRQ IDs of the same peripheral are guaranteed to be
 * consecutive. This data type is used to store IRQ ID ranges of a peripheral.
 */
typedef struct plic_peripheral_range {
  dif_plic_irq_id_t first_irq_id; /*<< The first IRQ ID of a peripheral. */
  dif_plic_irq_id_t last_irq_id;  /*<< The last IRQ ID of a peripheral. */
} plic_peripheral_range_t;

// An array of target specific set of register offsets. Every supported PLIC
// target must have an entry in this array.
static const plic_target_reg_offset_t
    plic_target_reg_offsets[kDifPlicTargetCount] = {
            [kDifPlicTargetIbex0] =
                {
                    .ie = RV_PLIC_IE00,
                    .cc = RV_PLIC_CC0,
                    .threshold = RV_PLIC_THRESHOLD0,
                },
};

// An array of IRQ source ID ranges per peripheral. Every peripheral supported
// by the PLIC, must have an entry in this array.
static const plic_peripheral_range_t
    plic_peripheral_ranges[kDifPlicPeripheralCount] = {
            [kDifPlicPeripheralGpio] =
                {
                    .first_irq_id = kDifPlicIrqIdGpio0,
                    .last_irq_id = kDifPlicIrqIdGpio31,
                },
            [kDifPlicPeripheralUart] =
                {
                    .first_irq_id = kDifPlicIrqIdUartTxWatermark,
                    .last_irq_id = kDifPlicIrqIdUartRxParityErr,
                },
            [kDifPlicPeripheralSpiDevice] =
                {
                    .first_irq_id = kDifPlicIrqIdSpiDeviceRxF,
                    .last_irq_id = kDifPlicIrqIdSpiDeviceTxUnderflow,
                },
            [kDifPlicPeripheralFlashCtrl] =
                {
                    .first_irq_id = kDifPlicIrqIdFlashCtrlProgEmpty,
                    .last_irq_id = kDifPlicIrqIdFlashCtrlOpError,
                },
            [kDifPlicPeripheralHmac] =
                {
                    .first_irq_id = kDifPlicIrqIdHmacDone,
                    .last_irq_id = kDifPlicIrqIdHmacErr,
                },
            [kDifPlicPeripheralAlertHandler] =
                {
                    .first_irq_id = kDifPlicIrqIdAlertHandlerClassA,
                    .last_irq_id = kDifPlicIrqIdAlertHandlerClassD,
                },
            [kDifPlicPeripheralNmiGen] =
                {
                    .first_irq_id = kDifPlicIrqIdNmiGenEsc0,
                    .last_irq_id = kDifPlicIrqIdNmiGenEsc3,
                },
};

/**
 * Get an IE, IP or LE register offset (IE00, IE01, ...) from an IRQ source ID.
 *
 * With more than 32 IRQ sources, there is a multiple of these registers to
 * accommodate all the bits (1 bit per IRQ source). This function calculates
 * the offset for a specific IRQ source ID (ID 33 would be IE01, ...).
 */
static ptrdiff_t plic_offset_from_reg0(dif_plic_irq_id_t irq) {
  uint8_t register_index = PLIC_ID_TO_INDEX(irq) / PLIC_ID_TO_INDEX_REG_SIZE;
  return register_index * sizeof(uint32_t);
}

/**
 * Get an IE, IP, LE register bit index from an IRQ source ID.
 *
 * With more than 32 IRQ sources, there is a multiple of these registers to
 * accommodate all the bits (1 bit per IRQ source). This function calculates
 * the bit position within a register for a specifci IRQ source ID (ID 33 would
 * be bit 0).
 */
static uint8_t plic_reg_bit_index_from_irq_id(dif_plic_irq_id_t irq) {
  return PLIC_ID_TO_INDEX(irq) % PLIC_ID_TO_INDEX_REG_SIZE;
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
  reg_info->offset = RV_PLIC_LE0 + offset;
  reg_info->bit_index = plic_reg_bit_index_from_irq_id(irq);
}

/**
 * Get an IRQ source specific Interrupt Pending register info.
 */
static void plic_irq_pending_reg_info(dif_plic_irq_id_t irq,
                                      plic_reg_info_t *reg_info) {
  ptrdiff_t offset = plic_offset_from_reg0(irq);
  reg_info->offset = RV_PLIC_IP0 + offset;
  reg_info->bit_index = plic_reg_bit_index_from_irq_id(irq);
}

/**
 * Get a PRIO register offset (PRIO0, PRIO1, ...) from an IRQ source ID.
 *
 * There is one PRIO register per IRQ source, this function calculates the IRQ
 * source specific PRIO register offset.
 */
static ptrdiff_t plic_priority_reg_offset(dif_plic_irq_id_t irq) {
  ptrdiff_t offset = PLIC_ID_TO_INDEX(irq) * sizeof(uint32_t);
  return RV_PLIC_PRIO0 + offset;
}

bool dif_plic_init(mmio_region_t base_addr, dif_plic_t *plic) {
  if (plic == NULL) {
    return false;
  }

  plic->base_addr = base_addr;

  return true;
}

bool dif_plic_irq_enable_set(const dif_plic_t *plic, dif_plic_irq_id_t irq,
                             dif_plic_target_t target,
                             dif_plic_enable_t enable) {
  if (plic == NULL) {
    return false;
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

  return true;
}

bool dif_plic_irq_trigger_type_set(const dif_plic_t *plic,
                                   dif_plic_irq_id_t irq,
                                   dif_plic_enable_t enable) {
  if (plic == NULL) {
    return false;
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

  return true;
}

bool dif_plic_irq_priority_set(const dif_plic_t *plic, dif_plic_irq_id_t irq,
                               uint32_t priority) {
  if (plic == NULL || priority > RV_PLIC_MAX_PRIORITY) {
    return false;
  }

  ptrdiff_t offset = plic_priority_reg_offset(irq);
  mmio_region_write32(plic->base_addr, offset, priority);

  return true;
}

bool dif_plic_target_threshold_set(const dif_plic_t *plic,
                                   dif_plic_target_t target,
                                   uint32_t threshold) {
  if (plic == NULL || threshold > RV_PLIC_MAX_PRIORITY) {
    return false;
  }

  ptrdiff_t threshold_offset = plic_target_reg_offsets[target].threshold;
  mmio_region_write32(plic->base_addr, threshold_offset, threshold);

  return true;
}

bool dif_plic_irq_pending_status_get(const dif_plic_t *plic,
                                     dif_plic_irq_id_t irq,
                                     dif_plic_flag_t *status) {
  if (plic == NULL || status == NULL) {
    return false;
  }

  plic_reg_info_t reg_info;
  plic_irq_pending_reg_info(irq, &reg_info);

  if (mmio_region_get_bit32(plic->base_addr, reg_info.offset,
                            reg_info.bit_index)) {
    *status = kDifPlicSet;
  } else {
    *status = kDifPlicUnset;
  }

  return true;
}

bool dif_plic_irq_claim(const dif_plic_t *plic, dif_plic_target_t target,
                        dif_irq_claim_data_t *claim_data) {
  if (plic == NULL || claim_data == NULL) {
    return false;
  }

  // Get an IRQ ID from the target specific CC register.
  ptrdiff_t cc_offset = plic_target_reg_offsets[target].cc;
  uint32_t irq_id = mmio_region_read32(plic->base_addr, cc_offset);

  // Validate an IRQ source, and determine which peripheral it belongs to.
  dif_plic_irq_id_t irq_src = (dif_plic_irq_id_t)irq_id;
  for (dif_plic_peripheral_t peripheral = kDifPlicPeripheralGpio;
       peripheral < kDifPlicPeripheralCount; ++peripheral) {
    if (irq_src < plic_peripheral_ranges[peripheral].first_irq_id ||
        irq_src > plic_peripheral_ranges[peripheral].last_irq_id) {
      continue;
    }

    claim_data->peripheral = peripheral;
    claim_data->source = irq_src;
    claim_data->cc_offset = cc_offset;
    return true;
  }

  return false;
}

bool dif_plic_irq_complete(const dif_plic_t *plic,
                           const dif_irq_claim_data_t *complete_data) {
  if (plic == NULL || complete_data == NULL) {
    return false;
  }

  // Write back the claimed IRQ ID to the target specific CC register,
  // to notify the PLIC of the IRQ completion.
  mmio_region_write32(plic->base_addr, complete_data->cc_offset,
                      (uint32_t)complete_data->source);

  return true;
}
