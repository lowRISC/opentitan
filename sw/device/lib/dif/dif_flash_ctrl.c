// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include "dif_warn_unused_result.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "flash_ctrl_regs.h"

// The number of different types of info regions.
static const uint32_t kNumInfoTypes = 3;

// A more convenient mapping between the info regions and their configuration
// register offset.
static const ptrdiff_t
    kInfo0ConfigOffsets[FLASH_CTRL_PARAM_REGNUMBANKS]
                       [FLASH_CTRL_PARAM_NUMINFOS0] = {
                           {
                               FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_REG_OFFSET,
                               FLASH_CTRL_BANK0_INFO0_PAGE_CFG_1_REG_OFFSET,
                               FLASH_CTRL_BANK0_INFO0_PAGE_CFG_2_REG_OFFSET,
                               FLASH_CTRL_BANK0_INFO0_PAGE_CFG_3_REG_OFFSET,
                           },
                           {
                               FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_REG_OFFSET,
                               FLASH_CTRL_BANK1_INFO0_PAGE_CFG_1_REG_OFFSET,
                               FLASH_CTRL_BANK1_INFO0_PAGE_CFG_2_REG_OFFSET,
                               FLASH_CTRL_BANK1_INFO0_PAGE_CFG_3_REG_OFFSET,
                           }};

static const ptrdiff_t
    kInfo1ConfigOffsets[FLASH_CTRL_PARAM_REGNUMBANKS]
                       [FLASH_CTRL_PARAM_NUMINFOS1] = {
                           {
                               FLASH_CTRL_BANK0_INFO1_PAGE_CFG_REG_OFFSET,
                           },
                           {
                               FLASH_CTRL_BANK1_INFO1_PAGE_CFG_REG_OFFSET,
                           }};

static const ptrdiff_t
    kInfo2ConfigOffsets[FLASH_CTRL_PARAM_REGNUMBANKS]
                       [FLASH_CTRL_PARAM_NUMINFOS2] = {
                           {
                               FLASH_CTRL_BANK0_INFO2_PAGE_CFG_0_REG_OFFSET,
                               FLASH_CTRL_BANK0_INFO2_PAGE_CFG_1_REG_OFFSET,
                           },
                           {
                               FLASH_CTRL_BANK1_INFO2_PAGE_CFG_0_REG_OFFSET,
                               FLASH_CTRL_BANK1_INFO2_PAGE_CFG_1_REG_OFFSET,
                           }};

// A more convenient mapping between the info regions and their configuration
// lock register offsets.
static const ptrdiff_t
    kInfo0LockOffsets[FLASH_CTRL_PARAM_REGNUMBANKS]
                     [FLASH_CTRL_PARAM_NUMINFOS0] = {
                         {
                             FLASH_CTRL_BANK0_INFO0_REGWEN_0_REG_OFFSET,
                             FLASH_CTRL_BANK0_INFO0_REGWEN_1_REG_OFFSET,
                             FLASH_CTRL_BANK0_INFO0_REGWEN_2_REG_OFFSET,
                             FLASH_CTRL_BANK0_INFO0_REGWEN_3_REG_OFFSET,
                         },
                         {
                             FLASH_CTRL_BANK1_INFO0_REGWEN_0_REG_OFFSET,
                             FLASH_CTRL_BANK1_INFO0_REGWEN_1_REG_OFFSET,
                             FLASH_CTRL_BANK1_INFO0_REGWEN_2_REG_OFFSET,
                             FLASH_CTRL_BANK1_INFO0_REGWEN_3_REG_OFFSET,
                         }};

static const ptrdiff_t
    kInfo1LockOffsets[FLASH_CTRL_PARAM_REGNUMBANKS]
                     [FLASH_CTRL_PARAM_NUMINFOS1] = {
                         {
                             FLASH_CTRL_BANK0_INFO1_REGWEN_REG_OFFSET,
                         },
                         {
                             FLASH_CTRL_BANK1_INFO1_REGWEN_REG_OFFSET,
                         }};

static const ptrdiff_t
    kInfo2LockOffsets[FLASH_CTRL_PARAM_REGNUMBANKS]
                     [FLASH_CTRL_PARAM_NUMINFOS2] = {
                         {
                             FLASH_CTRL_BANK0_INFO2_REGWEN_0_REG_OFFSET,
                             FLASH_CTRL_BANK0_INFO2_REGWEN_1_REG_OFFSET,
                         },
                         {
                             FLASH_CTRL_BANK1_INFO2_REGWEN_0_REG_OFFSET,
                             FLASH_CTRL_BANK1_INFO2_REGWEN_1_REG_OFFSET,
                         }};

/** Helper function to get the offset for an interrupt type. */
DIF_WARN_UNUSED_RESULT
static bool get_irq_bit_index(dif_flash_ctrl_irq_t irq_type,
                              uint8_t *offset_out) {
  ptrdiff_t offset;
  switch (irq_type) {
    case kDifFlashCtrlIrqProgEmpty:
      offset = FLASH_CTRL_INTR_COMMON_PROG_EMPTY_BIT;
      break;
    case kDifFlashCtrlIrqProgLevel:
      offset = FLASH_CTRL_INTR_COMMON_PROG_LVL_BIT;
      break;
    case kDifFlashCtrlIrqRdFull:
      offset = FLASH_CTRL_INTR_COMMON_RD_FULL_BIT;
      break;
    case kDifFlashCtrlIrqRdLevel:
      offset = FLASH_CTRL_INTR_COMMON_RD_LVL_BIT;
      break;
    case kDifFlashCtrlIrqOpDone:
      offset = FLASH_CTRL_INTR_COMMON_OP_DONE_BIT;
      break;
    default:
      return false;
  }
  *offset_out = offset;

  return true;
}

/** Helper function to check if a transaction is in progress. */
DIF_WARN_UNUSED_RESULT
static bool is_busy(const dif_flash_ctrl_t *flash_ctrl) {
  return mmio_region_get_bit32(flash_ctrl->base_addr,
                               FLASH_CTRL_CTRL_REGWEN_REG_OFFSET,
                               FLASH_CTRL_CTRL_REGWEN_EN_BIT) == 0;
}

/** Helper function for starting erase flash operation. */
DIF_WARN_UNUSED_RESULT
static dif_flash_ctrl_start_result_t start_op(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t op,
    uint32_t word_count, dif_flash_ctrl_region_select_t region,
    dif_flash_ctrl_program_type_t program_type,
    dif_flash_ctrl_erase_type_t erase_type) {
  if (is_busy(flash_ctrl)) {
    return kDifFlashCtrlStartBusy;
  }

  // Set the address.
  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_ADDR_REG_OFFSET, addr);

  // Set the operation of the transaction: read, program, or erase.
  uint32_t control_reg_val =
      bitfield_field32_write(0, FLASH_CTRL_CONTROL_OP_FIELD, op);

  // Set the erase mode.
  switch (erase_type) {
    case kDifFlashCtrlEraseSelPage:
      break;
    case kDifFlashCtrlEraseSelBank:
      control_reg_val = bitfield_bit32_write(
          control_reg_val, FLASH_CTRL_CONTROL_ERASE_SEL_BIT, 1u);
      break;
    default:
      return kDifFlashCtrlStartError;
  }

  // Set the partition to info here, and set it back bellow if we're accessing a
  // data partition.
  control_reg_val = bitfield_bit32_write(
      control_reg_val, FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 1u);

  // Set the partition and info type.
  switch (region) {
    case kDifFlashCtrlRegionData:
      // 0 indicates data partition.
      control_reg_val = bitfield_bit32_write(
          control_reg_val, FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, 0u);
      break;
    case kDifFlashCtrlRegionInfo0:
      // The partition is already set to info, so just set the info type.
      control_reg_val = bitfield_field32_write(
          control_reg_val, FLASH_CTRL_CONTROL_INFO_SEL_FIELD, 0u);
      break;
    case kDifFlashCtrlRegionInfo1:
      control_reg_val = bitfield_field32_write(
          control_reg_val, FLASH_CTRL_CONTROL_INFO_SEL_FIELD, 1u);
      break;
    case kDifFlashCtrlRegionInfo2:
      control_reg_val = bitfield_field32_write(
          control_reg_val, FLASH_CTRL_CONTROL_INFO_SEL_FIELD, 2u);
      break;
    default:
      return kDifFlashCtrlStartError;
  }

  // Set the number of words.
  control_reg_val = bitfield_field32_write(
      control_reg_val, FLASH_CTRL_CONTROL_NUM_FIELD, word_count);

  // Write the configuration.
  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_CONTROL_REG_OFFSET,
                      control_reg_val);

  // Start the transaction.
  mmio_region_nonatomic_set_bit32(flash_ctrl->base_addr,
                                  FLASH_CTRL_CONTROL_REG_OFFSET,
                                  FLASH_CTRL_CONTROL_START_BIT);

  return kDifFlashCtrlStartOk;
}

/** Helper function for starting read/program flash operations. */
DIF_WARN_UNUSED_RESULT
static dif_flash_ctrl_start_result_t start_transfer_op(
    dif_flash_ctrl_t *flash_ctrl, uint32_t op, uint32_t addr,
    uint32_t word_count, dif_flash_ctrl_region_select_t region,
    dif_flash_ctrl_program_type_t program_type) {
  if (is_busy(flash_ctrl)) {
    return kDifFlashCtrlStartBusy;
  }

  // Reset tracked transaction state.
  flash_ctrl->words_transfered = 0;

  // Start the operation, the value of `erase_sel` isn't used for program/read
  // transactions.
  return start_op(flash_ctrl, addr, op, word_count, region, program_type,
                  kDifFlashCtrlEraseSelPage);
}

/** Helper function to get the offset for a data region's memory protection
 * configuration register. */
DIF_WARN_UNUSED_RESULT
static ptrdiff_t data_region_offset_get(uint32_t region) {
  return FLASH_CTRL_MP_REGION_CFG_0_REG_OFFSET +
         FLASH_CTRL_PARAM_REG_WIDTH * region;
}

/** Helper function to get the offset for a data region's memory protection
 * region lock register. */
DIF_WARN_UNUSED_RESULT
static ptrdiff_t data_region_lock_offset_get(uint32_t region) {
  return FLASH_CTRL_REGION_CFG_REGWEN_0_REG_OFFSET +
         FLASH_CTRL_PARAM_REG_WIDTH * region;
}

/** Helper function to get the offset for an info region's memory protection
 * configuration register. This function must be called with parameters that are
 * valid under calls to `region_is_valid()`.*/
DIF_WARN_UNUSED_RESULT
static ptrdiff_t info_region_offset_get(uint32_t bank, uint32_t info_type,
                                        uint32_t page) {
  switch (info_type) {
    case 0:
      return kInfo0ConfigOffsets[bank][page];
    case 1:
      return kInfo1ConfigOffsets[bank][page];
    case 2:
      return kInfo2ConfigOffsets[bank][page];
    default:
      return 0;
  }
}

/** Helper function to get the offset for an  info reigon's memory protection
 * region lock register. This function must be called with parameters that are
 * valid under calls to `region_is_valid()`.
 */
DIF_WARN_UNUSED_RESULT
static ptrdiff_t info_region_lock_offset_get(uint32_t bank, uint32_t info_type,
                                             uint32_t page) {
  switch (info_type) {
    case 0:
      return kInfo0LockOffsets[bank][page];
    case 1:
      return kInfo1LockOffsets[bank][page];
    case 2:
      return kInfo2LockOffsets[bank][page];
    default:
      return 0;
  }
}

/** Helper function to get the offset for a region's memory protection
 * configuration register. This is useful for resolving the register offset, but
 * not sufficient for poking information within the register, as they have
 * different layouts. This is especially the case for the default region
 * configuration where all fields in the register are offset by a single bit.*/
DIF_WARN_UNUSED_RESULT
static ptrdiff_t region_offset_get(dif_flash_ctrl_region_t region) {
  switch (region.type) {
    case kDifFlashCtrlRegionTypeData:
      return data_region_offset_get(region.region.data);
    case kDifFlashCtrlRegionTypeInfo:
      return info_region_offset_get(region.region.info.bank,
                                    region.region.info.type,
                                    region.region.info.page);
    default:
      return FLASH_CTRL_DEFAULT_REGION_REG_OFFSET;
  }
}

/** Helper function to get the ooffset for a reigon's memory protection region
 * lock register. Returns `false` in the case that the default region is
 * specified, as this region does not have a lock register, `true` otherwise.
 * The contents of `offset_out` are set if and only if this function returns
 * `true`. */
DIF_WARN_UNUSED_RESULT
static bool region_lock_offset_get(dif_flash_ctrl_region_t region,
                                   ptrdiff_t *offset_out) {
  switch (region.type) {
    case kDifFlashCtrlRegionTypeData:
      *offset_out = data_region_lock_offset_get(region.region.data);
      break;
    case kDifFlashCtrlRegionTypeInfo:
      *offset_out = info_region_lock_offset_get(region.region.info.bank,
                                                region.region.info.type,
                                                region.region.info.page);
      break;
    default:
      return false;
  }

  return true;
}

/** Helper function to get the bit offset for memory protection region lock
 * bits. Returns `false` in the case that the default region is specified, as
 * this region does not have a lock register, `true` otherwise.  The contents of
 * `offset_out` are set if and only if this function returns `true`. */
DIF_WARN_UNUSED_RESULT
static bool region_lock_bit_offset_get(dif_flash_ctrl_region_t region,
                                       uint8_t *offset_out) {
  switch (region.type) {
    case kDifFlashCtrlRegionTypeData:
      *offset_out = FLASH_CTRL_REGION_CFG_REGWEN_0_REGION_0_BIT;
      break;
    case kDifFlashCtrlRegionTypeInfo:
      *offset_out = FLASH_CTRL_BANK0_INFO0_REGWEN_0_REGION_0_BIT;
      break;
    default:
      return false;
  }

  return true;
}

/** DIF internal representation for bit offsets in memory protection
 * configuration registers. */
typedef enum config_bit {
  kEnable,
  kRead,
  kProg,
  kErase,
  kScramble,
  kErrorCorrection,
  kHighEndurance,
} config_bit_t;

/** Helper function to resolve bit offsets for memory protection configuration
 * registers. Returns `true` and populates `offset_out` with the bit index for
 * the region if there is a valid offset for the `bit`, and `false` if it is
 * invalid. */
DIF_WARN_UNUSED_RESULT
static bool region_config_bit_offset_get(dif_flash_ctrl_region_t region,
                                         config_bit_t bit,
                                         uint8_t *offset_out) {
  // This is basically a two dimensional lookup table for fetching register
  // offsets.
  switch (region.type) {
    case kDifFlashCtrlRegionTypeData:
      switch (bit) {
        case kEnable:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_RD_EN_0_BIT;
          break;
        case kRead:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_RD_EN_0_BIT;
          break;
        case kProg:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_PROG_EN_0_BIT;
          break;
        case kErase:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_ERASE_EN_0_BIT;
          break;
        case kScramble:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_SCRAMBLE_EN_0_BIT;
          break;
        case kErrorCorrection:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_ECC_EN_0_BIT;
          break;
        case kHighEndurance:
          *offset_out = FLASH_CTRL_MP_REGION_CFG_0_HE_EN_0_BIT;
          break;
        default:
          return false;
      }
      break;
    case kDifFlashCtrlRegionTypeInfo:
      switch (bit) {
        case kEnable:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_EN_0_BIT;
          break;
        case kRead:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_RD_EN_0_BIT;
          break;
        case kProg:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_PROG_EN_0_BIT;
          break;
        case kErase:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_ERASE_EN_0_BIT;
          break;
        case kScramble:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_SCRAMBLE_EN_0_BIT;
          break;
        case kErrorCorrection:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_ECC_EN_0_BIT;
          break;
        case kHighEndurance:
          *offset_out = FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_HE_EN_0_BIT;
          break;
        default:
          return false;
      }
      break;
    case kDifFlashCtrlRegionTypeDefault:
      switch (bit) {
        case kEnable:
          // The default region does not have an enable bit.
          return false;
        case kRead:
          *offset_out = FLASH_CTRL_DEFAULT_REGION_RD_EN_BIT;
          break;
        case kProg:
          *offset_out = FLASH_CTRL_DEFAULT_REGION_PROG_EN_BIT;
          break;
        case kErase:
          *offset_out = FLASH_CTRL_DEFAULT_REGION_ERASE_EN_BIT;
          break;
        case kScramble:
          *offset_out = FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_BIT;
          break;
        default:
          return false;
      }
      break;
    default:
      return false;
  }

  return true;
}

/** Helper function to check if a data region is valid. */
DIF_WARN_UNUSED_RESULT
static bool data_region_is_valid(uint32_t region) {
  return region < FLASH_CTRL_PARAM_NUMREGIONS;
}

/** Helper funciton to validate region perameters. Returns true if the given
 * region is valid, false otherwise. */
DIF_WARN_UNUSED_RESULT
static bool region_is_valid(dif_flash_ctrl_region_t region) {
  switch (region.type) {
    case kDifFlashCtrlRegionTypeData:
      return data_region_is_valid(region.region.data);
    case kDifFlashCtrlRegionTypeInfo:
      return region.region.info.bank < FLASH_CTRL_PARAM_REGNUMBANKS &&
             region.region.info.type < kNumInfoTypes &&
             region.region.info.page < FLASH_CTRL_PARAM_NUMINFOS0;
    case kDifFlashCtrlRegionTypeDefault:
      return true;
    default:
      return false;
  }
}

/** Helper function to check if region configuration is locked. */
DIF_WARN_UNUSED_RESULT
static bool region_is_locked(const dif_flash_ctrl_t *flash_ctrl,
                             dif_flash_ctrl_region_t region) {
  ptrdiff_t offset;
  uint8_t bit_offset;
  // If there is no lock register for this region then the region isn't locked.
  if (!region_lock_offset_get(region, &offset) ||
      !region_lock_bit_offset_get(region, &bit_offset)) {
    return false;
  }

  return !mmio_region_get_bit32(flash_ctrl->base_addr, offset, bit_offset);
}

/** Wrapper function for checking if a data region is locked. */
DIF_WARN_UNUSED_RESULT
static bool data_region_is_locked(const dif_flash_ctrl_t *flash_ctrl,
                                  uint32_t region) {
  return region_is_locked(
      flash_ctrl, (dif_flash_ctrl_region_t){.type = kDifFlashCtrlRegionTypeData,
                                            .region.data = region});
}

DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t region_config_bit_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    config_bit_t bit, dif_flash_ctrl_enable_t enable) {
  if (flash_ctrl == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlRegionBadArg;
  }

  uint8_t bit_offset;
  if (!region_config_bit_offset_get(region, bit, &bit_offset)) {
    return kDifFlashCtrlRegionBadArg;
  }
  ptrdiff_t reg_offset = region_offset_get(region);

  if (region_is_locked(flash_ctrl, region)) {
    return kDifFlashCtrlRegionBadAccess;
  }

  switch (enable) {
    case kDifFlashCtrlEnable:
      mmio_region_nonatomic_set_bit32(flash_ctrl->base_addr, reg_offset,
                                      bit_offset);
      break;
    case kDifFlashCtrlDisable:
      mmio_region_nonatomic_clear_bit32(flash_ctrl->base_addr, reg_offset,
                                        bit_offset);
      break;
    default:
      return kDifFlashCtrlRegionError;
  }

  return kDifFlashCtrlRegionOk;
}

DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t region_config_bit_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    config_bit_t bit, dif_flash_ctrl_enable_t *enable_out) {
  if (flash_ctrl == NULL || enable_out == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t bit_offset;
  if (!region_config_bit_offset_get(region, bit, &bit_offset)) {
    return kDifFlashCtrlBadArg;
  }
  ptrdiff_t reg_offset = region_offset_get(region);

  bool enable_read =
      mmio_region_get_bit32(flash_ctrl->base_addr, reg_offset, bit_offset);
  *enable_out = enable_read ? kDifFlashCtrlEnable : kDifFlashCtrlDisable;

  return kDifFlashCtrlOk;
}

/** Helper function to check if bank configuration is locked. */
DIF_WARN_UNUSED_RESULT
static bool bank_locked(const dif_flash_ctrl_t *flash_ctrl) {
  return !mmio_region_get_bit32(flash_ctrl->base_addr,
                                FLASH_CTRL_BANK_CFG_REGWEN_REG_OFFSET,
                                FLASH_CTRL_BANK_CFG_REGWEN_BANK_BIT);
}

/** Helper function to get the bit index for bank configuration. */
DIF_WARN_UNUSED_RESULT
static bool get_bank_config_bit_index(uint32_t bank, uint32_t *offset_out) {
  switch (bank) {
    case 0:
      *offset_out = FLASH_CTRL_MP_BANK_CFG_ERASE_EN_0_BIT;
      break;
    case 1:
      *offset_out = FLASH_CTRL_MP_BANK_CFG_ERASE_EN_1_BIT;
      break;
    default:
      return false;
  }

  return true;
}

/** Helper function to validate the number of words to transfer on FIFO
 * operations.
 *
 * Read/program transactions declare the number of words up front. When
 * transferring data over the FIFO this is used to ensure the number of words
 * read/written is consistent.
 */
DIF_WARN_UNUSED_RESULT
static bool check_word_count(const dif_flash_ctrl_t *flash_ctrl,
                             uint32_t word_count) {
  uint32_t bitfield =
      mmio_region_read32(flash_ctrl->base_addr, FLASH_CTRL_CONTROL_REG_OFFSET);
  uint32_t transaction_words =
      bitfield_field32_read(bitfield, FLASH_CTRL_CONTROL_NUM_FIELD);
  uint32_t remaining_words = transaction_words - flash_ctrl->words_transfered;

  return word_count <= remaining_words;
}

dif_flash_ctrl_result_t dif_flash_ctrl_init(
    const dif_flash_ctrl_config_t *config, dif_flash_ctrl_t *flash_ctrl_out) {
  if (config == NULL || flash_ctrl_out == NULL) {
    return kDifFlashCtrlBadArg;
  }

  flash_ctrl_out->base_addr = config->base_addr;
  flash_ctrl_out->words_transfered = 0;

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_irq_state_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type,
    dif_flash_ctrl_enable_t *state) {
  if (flash_ctrl == NULL || state == NULL) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t bit_index;
  if (!get_irq_bit_index(irq_type, &bit_index)) {
    return kDifFlashCtrlError;
  }

  bool enabled = mmio_region_get_bit32(
      flash_ctrl->base_addr, FLASH_CTRL_INTR_STATE_REG_OFFSET, bit_index);

  *state = enabled ? kDifFlashCtrlEnable : kDifFlashCtrlDisable;

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_irq_state_clear(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t bit_index;
  if (!get_irq_bit_index(irq_type, &bit_index)) {
    return kDifFlashCtrlError;
  }

  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_INTR_STATE_REG_OFFSET,
                      bitfield_bit32_write(0, bit_index, true));

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_irqs_disable(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *state) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  if (state != NULL) {
    *state = mmio_region_read32(flash_ctrl->base_addr,
                                FLASH_CTRL_INTR_ENABLE_REG_OFFSET);
  }

  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_INTR_ENABLE_REG_OFFSET,
                      0u);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_irqs_restore(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t state) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_INTR_ENABLE_REG_OFFSET,
                      state);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_irq_control(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type,
    dif_flash_ctrl_enable_t enable) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t bit_index;
  if (!get_irq_bit_index(irq_type, &bit_index)) {
    return kDifFlashCtrlError;
  }

  switch (enable) {
    case kDifFlashCtrlEnable:
      mmio_region_nonatomic_set_bit32(
          flash_ctrl->base_addr, FLASH_CTRL_INTR_ENABLE_REG_OFFSET, bit_index);
      break;
    case kDifFlashCtrlDisable:
      mmio_region_nonatomic_clear_bit32(
          flash_ctrl->base_addr, FLASH_CTRL_INTR_ENABLE_REG_OFFSET, bit_index);
      break;
    default:
      return kDifFlashCtrlError;
  }

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_irq_force(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t bit_index;
  if (!get_irq_bit_index(irq_type, &bit_index)) {
    return kDifFlashCtrlError;
  }

  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_INTR_TEST_REG_OFFSET,
                      bitfield_bit32_write(0, bit_index, true));

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_start_result_t dif_flash_ctrl_read_start(
    dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t word_count,
    dif_flash_ctrl_region_select_t region) {
  if (flash_ctrl == NULL || word_count > FLASH_CTRL_CONTROL_NUM_MASK) {
    return kDifFlashCtrlStartBadArg;
  }

  return start_transfer_op(flash_ctrl, FLASH_CTRL_CONTROL_OP_VALUE_READ, addr,
                           word_count, region, 0);
}

dif_flash_ctrl_start_result_t dif_flash_ctrl_prog_start(
    dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t word_count,
    dif_flash_ctrl_program_type_t program_type,
    dif_flash_ctrl_region_select_t region) {
  if (flash_ctrl == NULL || word_count > FLASH_CTRL_CONTROL_NUM_MASK) {
    return kDifFlashCtrlStartBadArg;
  }

  return start_transfer_op(flash_ctrl, FLASH_CTRL_CONTROL_OP_VALUE_PROG, addr,
                           word_count, region, program_type);
}

dif_flash_ctrl_start_result_t dif_flash_ctrl_erase_start(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t addr,
    dif_flash_ctrl_erase_type_t erase_type,
    dif_flash_ctrl_region_select_t region) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlStartBadArg;
  }

  return start_op(flash_ctrl, FLASH_CTRL_CONTROL_OP_VALUE_ERASE, addr, 0,
                  region, 0, erase_type);
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_region_enable_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable) {
  if (flash_ctrl == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlRegionBadArg;
  }

  if (region_is_locked(flash_ctrl, region)) {
    return kDifFlashCtrlRegionBadAccess;
  }

  ptrdiff_t offset = region_offset_get(region);
  switch (enable) {
    case kDifFlashCtrlEnable:
      mmio_region_nonatomic_set_bit32(flash_ctrl->base_addr, offset,
                                      FLASH_CTRL_MP_REGION_CFG_0_EN_0_BIT);
      break;
    case kDifFlashCtrlDisable:
      mmio_region_nonatomic_clear_bit32(flash_ctrl->base_addr, offset,
                                        FLASH_CTRL_MP_REGION_CFG_0_EN_0_BIT);
      break;
    default:
      return kDifFlashCtrlRegionError;
  }

  return kDifFlashCtrlRegionOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_region_enable_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out) {
  if (flash_ctrl == NULL || enable_out == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t bit_offset;
  if (!region_config_bit_offset_get(region, kEnable, &bit_offset)) {
    // This is a `BadArg` error since the `region` argument is either malformed
    // or references the default reigon, which doesn't have an enable offset.
    return kDifFlashCtrlBadArg;
  }
  ptrdiff_t reg_offset = region_offset_get(region);

  uint32_t enable = mmio_region_get_bit32(flash_ctrl->base_addr, reg_offset,
                                          FLASH_CTRL_MP_REGION_CFG_0_EN_0_BIT);
  *enable_out = enable ? kDifFlashCtrlEnable : kDifFlashCtrlDisable;

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_region_access_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_access_t access) {
  if (flash_ctrl == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlRegionBadArg;
  }

  uint8_t rd_bit, prog_bit, erase_bit;
  if (!region_config_bit_offset_get(region, kRead, &rd_bit) ||
      !region_config_bit_offset_get(region, kProg, &prog_bit) ||
      !region_config_bit_offset_get(region, kErase, &erase_bit)) {
    // The implication of these checks failing is the supplied region doesn't
    // have one or more of these fields. No MMIO accesses have been made so
    // notify caller of the bad arg.
    return kDifFlashCtrlRegionBadArg;
  }
  ptrdiff_t reg_offset = region_offset_get(region);

  if (region_is_locked(flash_ctrl, region)) {
    return kDifFlashCtrlRegionBadAccess;
  }

  // Read the access bits.
  uint32_t bitfield = mmio_region_read32(flash_ctrl->base_addr, reg_offset);
  bitfield = bitfield_bit32_write(bitfield, rd_bit, access.read);
  bitfield = bitfield_bit32_write(bitfield, prog_bit, access.program);
  bitfield = bitfield_bit32_write(bitfield, erase_bit, access.erase);
  mmio_region_write32(flash_ctrl->base_addr, reg_offset, bitfield);

  return kDifFlashCtrlRegionOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_region_access_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_access_t *access_out) {
  if (flash_ctrl == NULL || access_out == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlBadArg;
  }

  uint8_t rd_bit, prog_bit, erase_bit;
  if (!region_config_bit_offset_get(region, kRead, &rd_bit) ||
      !region_config_bit_offset_get(region, kProg, &prog_bit) ||
      !region_config_bit_offset_get(region, kErase, &erase_bit)) {
    return kDifFlashCtrlBadArg;
  }
  ptrdiff_t reg_offset = region_offset_get(region);

  // Read and extract access bits.
  uint32_t bitfield = mmio_region_read32(flash_ctrl->base_addr, reg_offset);
  access_out->read = bitfield_bit32_read(bitfield, rd_bit);
  access_out->program = bitfield_bit32_read(bitfield, prog_bit);
  access_out->erase = bitfield_bit32_read(bitfield, erase_bit);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_region_scramble_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable) {
  return region_config_bit_set(flash_ctrl, region, kScramble, enable);
}

dif_flash_ctrl_result_t dif_flash_ctrl_region_scramble_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out) {
  return region_config_bit_get(flash_ctrl, region, kScramble, enable_out);
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_region_ecc_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable) {
  return region_config_bit_set(flash_ctrl, region, kErrorCorrection, enable);
}

dif_flash_ctrl_result_t dif_flash_ctrl_region_ecc_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out) {
  return region_config_bit_get(flash_ctrl, region, kErrorCorrection,
      enable_out);
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_region_he_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable) {
  return region_config_bit_set(flash_ctrl, region, kHighEndurance, enable);
}

dif_flash_ctrl_result_t dif_flash_ctrl_region_he_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out) {
  return region_config_bit_get(flash_ctrl, region, kHighEndurance, enable_out);
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_data_region_base_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t page) {
  if (flash_ctrl == NULL || !data_region_is_valid(region) ||
      page >= FLASH_CTRL_MP_REGION_CFG_0_BASE_0_MASK) {
    return kDifFlashCtrlRegionBadArg;
  }

  if (data_region_is_locked(flash_ctrl, region)) {
    return kDifFlashCtrlRegionBadAccess;
  }

  ptrdiff_t offset = data_region_offset_get(region);
  uint32_t region_data = mmio_region_read32(flash_ctrl->base_addr, offset);
  mmio_region_write32(
      flash_ctrl->base_addr, offset,
      bitfield_field32_write(region_data,
                             FLASH_CTRL_MP_REGION_CFG_0_BASE_0_FIELD, page));

  return kDifFlashCtrlRegionOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_data_region_base_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t *page_out) {
  if (flash_ctrl == NULL || page_out == NULL || !data_region_is_valid(region)) {
    return kDifFlashCtrlBadArg;
  }

  ptrdiff_t offset = data_region_offset_get(region);
  uint32_t bitfield = mmio_region_read32(flash_ctrl->base_addr, offset);
  *page_out =
      bitfield_field32_read(bitfield, FLASH_CTRL_MP_REGION_CFG_0_BASE_0_FIELD);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_data_region_size_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t size) {
  if (flash_ctrl == NULL || !data_region_is_valid(region) ||
      size > FLASH_CTRL_MP_REGION_CFG_0_SIZE_0_MASK) {
    return kDifFlashCtrlRegionBadArg;
  }

  if (data_region_is_locked(flash_ctrl, region)) {
    return kDifFlashCtrlRegionBadAccess;
  }

  ptrdiff_t offset = data_region_offset_get(region);
  uint32_t region_data = mmio_region_read32(flash_ctrl->base_addr, offset);
  mmio_region_write32(
      flash_ctrl->base_addr, offset,
      bitfield_field32_write(region_data,
                             FLASH_CTRL_MP_REGION_CFG_0_SIZE_0_FIELD, size));

  return kDifFlashCtrlRegionOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_data_region_size_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t *size_out) {
  if (flash_ctrl == NULL || size_out == NULL || !data_region_is_valid(region)) {
    return kDifFlashCtrlBadArg;
  }

  ptrdiff_t offset = data_region_offset_get(region);
  uint32_t bitfield = mmio_region_read32(flash_ctrl->base_addr, offset);
  *size_out =
      bitfield_field32_read(bitfield, FLASH_CTRL_MP_REGION_CFG_0_SIZE_0_FIELD);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_region_result_t dif_flash_ctrl_region_config_lock(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region) {
  if (flash_ctrl == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlRegionBadArg;
  }

  ptrdiff_t offset;
  uint8_t bit_offset;
  // If there is no lock register for this region then the region isn't locked.
  if (!region_lock_offset_get(region, &offset) ||
      !region_lock_bit_offset_get(region, &bit_offset)) {
    return kDifFlashCtrlRegionBadArg;
  }

  if (region_is_locked(flash_ctrl, region)) {
    return kDifFlashCtrlRegionBadAccess;
  }

  mmio_region_nonatomic_clear_bit32(flash_ctrl->base_addr, offset, bit_offset);

  return kDifFlashCtrlRegionOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_region_config_check(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *access_out) {
  if (flash_ctrl == NULL || access_out == NULL || !region_is_valid(region)) {
    return kDifFlashCtrlBadArg;
  }

  if (region_is_locked(flash_ctrl, region)) {
    *access_out = kDifFlashCtrlDisable;
  } else {
    *access_out = kDifFlashCtrlEnable;
  }

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_bank_result_t dif_flash_ctrl_bank_erase_enable(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t bank,
    dif_flash_ctrl_enable_t erase_enable) {
  if (flash_ctrl == NULL || bank >= FLASH_CTRL_PARAM_REGNUMBANKS) {
    return kDifFlashCtrlBankBadArg;
  }

  if (bank_locked(flash_ctrl)) {
    return kDifFlashCtrlBankLocked;
  }

  uint32_t offset;
  if (get_bank_config_bit_index(bank, &offset)) {
    return kDifFlashCtrlBankError;
  }

  switch (erase_enable) {
    case kDifFlashCtrlEnable:
      mmio_region_nonatomic_set_bit32(
          flash_ctrl->base_addr, FLASH_CTRL_MP_BANK_CFG_REG_OFFSET, offset);
      break;
    case kDifFlashCtrlDisable:
      mmio_region_nonatomic_clear_bit32(
          flash_ctrl->base_addr, FLASH_CTRL_MP_BANK_CFG_REG_OFFSET, offset);
      break;
    default:
      return kDifFlashCtrlBankError;
  }

  return kDifFlashCtrlBankOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_bank_erase_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t bank,
    dif_flash_ctrl_enable_t *erase_enable_out) {
  if (flash_ctrl == NULL || erase_enable_out == NULL ||
      bank >= FLASH_CTRL_PARAM_REGNUMBANKS) {
    return kDifFlashCtrlBadArg;
  }

  uint32_t offset;
  if (get_bank_config_bit_index(bank, &offset)) {
    return kDifFlashCtrlError;
  }

  if (mmio_region_get_bit32(flash_ctrl->base_addr,
                            FLASH_CTRL_MP_BANK_CFG_REG_OFFSET, offset)) {
    *erase_enable_out = kDifFlashCtrlEnable;
  } else {
    *erase_enable_out = kDifFlashCtrlDisable;
  }

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_bank_config_disable(
    const dif_flash_ctrl_t *flash_ctrl) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  // Lock bank configuration.
  mmio_region_nonatomic_clear_bit32(flash_ctrl->base_addr,
                                    FLASH_CTRL_BANK_CFG_REGWEN_REG_OFFSET,
                                    FLASH_CTRL_BANK_CFG_REGWEN_BANK_BIT);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_bank_config_is_enabled(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_enable_t *access_out) {
  if (flash_ctrl == NULL || access_out == NULL) {
    return kDifFlashCtrlBadArg;
  }

  if (bank_locked(flash_ctrl)) {
    *access_out = kDifFlashCtrlDisable;
  } else {
    *access_out = kDifFlashCtrlEnable;
  }

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_status_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_status_t *status_out) {
  if (flash_ctrl == NULL || status_out == NULL) {
    return kDifFlashCtrlBadArg;
  }

  // Read flash operation status.
  uint32_t op_status = mmio_region_read32(flash_ctrl->base_addr,
                                          FLASH_CTRL_OP_STATUS_REG_OFFSET);
  // Read flash controller status.
  uint32_t fc_status =
      mmio_region_read32(flash_ctrl->base_addr, FLASH_CTRL_STATUS_REG_OFFSET);

  // Extract operation status bits.
  status_out->done =
      bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_DONE_BIT);
  status_out->err =
      bitfield_bit32_read(op_status, FLASH_CTRL_OP_STATUS_ERR_BIT);

  // Extract flash controller status bits.
  status_out->rd_full =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_RD_FULL_BIT);
  status_out->rd_empty =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_RD_EMPTY_BIT);
  status_out->prog_full =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_PROG_FULL_BIT);
  status_out->prog_empty =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_PROG_EMPTY_BIT);
  status_out->init_wip =
      bitfield_bit32_read(fc_status, FLASH_CTRL_STATUS_INIT_WIP_BIT);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_error_query_result_t dif_flash_ctrl_error_describe(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *address_out) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlErrorQueryBadArg;
  }

  // Ensure flash controller is in an error state.
  if (mmio_region_get_bit32(flash_ctrl->base_addr,
                            FLASH_CTRL_OP_STATUS_REG_OFFSET,
                            FLASH_CTRL_OP_STATUS_ERR_BIT)) {
    // Clear the error state.
    mmio_region_nonatomic_set_bit32(flash_ctrl->base_addr,
                                    FLASH_CTRL_OP_STATUS_REG_OFFSET,
                                    FLASH_CTRL_OP_STATUS_ERR_BIT);
  } else {
    return kDifFlashCtrlErrorQueryInvalid;
  }

  // Early return if caller is just clearing the err bit.
  if (address_out == NULL) {
    return kDifFlashCtrlErrorQueryOk;
  }

  uint32_t err_addr = mmio_region_read32(flash_ctrl->base_addr,
                                         FLASH_CTRL_ERR_ADDR_ERR_ADDR_OFFSET);
  *address_out =
      bitfield_field32_read(err_addr, FLASH_CTRL_ERR_ADDR_ERR_ADDR_FIELD);

  return kDifFlashCtrlErrorQueryOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_fifo_prog_lvl_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t prog) {
  if (flash_ctrl == NULL || prog >= FLASH_CTRL_FIFO_LVL_PROG_MASK) {
    return kDifFlashCtrlBadArg;
  }

  // Read FIFO_LVL register.
  uint32_t fifo_lvl =
      mmio_region_read32(flash_ctrl->base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET);
  // Modify PROG bits.
  fifo_lvl =
      bitfield_field32_write(fifo_lvl, FLASH_CTRL_FIFO_LVL_PROG_FIELD, prog);
  // Write back to FIFO_LVL register.
  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET,
                      fifo_lvl);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_fifo_rd_lvl_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t rd) {
  if (flash_ctrl == NULL || rd >= FLASH_CTRL_FIFO_LVL_RD_MASK) {
    return kDifFlashCtrlBadArg;
  }

  // Read FIFO_LVL register.
  uint32_t fifo_lvl =
      mmio_region_read32(flash_ctrl->base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET);
  // Modify RD bits.
  fifo_lvl = bitfield_field32_write(fifo_lvl, FLASH_CTRL_FIFO_LVL_RD_FIELD, rd);
  // Write back to FIFO_LVL register.
  mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET,
                      fifo_lvl);

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_fifo_lvl_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *prog_out, uint32_t *rd_out) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  // Read FIFO_LVL register.
  uint32_t fifo_lvl =
      mmio_region_read32(flash_ctrl->base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET);
  // Extract PROG bits.
  if (prog_out != NULL) {
    *prog_out = bitfield_field32_read(fifo_lvl, FLASH_CTRL_FIFO_LVL_PROG_FIELD);
  }
  // Extract RD bits.
  if (rd_out != NULL) {
    *rd_out = bitfield_field32_read(fifo_lvl, FLASH_CTRL_FIFO_LVL_RD_FIELD);
  }

  return kDifFlashCtrlOk;
}

dif_flash_ctrl_result_t dif_flash_ctrl_fifo_reset(
    const dif_flash_ctrl_t *flash_ctrl) {
  if (flash_ctrl == NULL) {
    return kDifFlashCtrlBadArg;
  }

  // Hold the FIFO in reset until this bit is cleared.
  mmio_region_nonatomic_set_bit32(flash_ctrl->base_addr,
                                  FLASH_CTRL_FIFO_RST_REG_OFFSET,
                                  FLASH_CTRL_FIFO_RST_EN_BIT);

  // No reason to hold FIFO in reset for any length of time.
  mmio_region_nonatomic_clear_bit32(flash_ctrl->base_addr,
                                    FLASH_CTRL_FIFO_RST_REG_OFFSET,
                                    FLASH_CTRL_FIFO_RST_EN_BIT);
  return kDifFlashCtrlOk;
}

dif_flash_ctrl_prog_result_t dif_flash_ctrl_prog_fifo_push(
    dif_flash_ctrl_t *flash_ctrl, const uint32_t *data, uint32_t word_count,
    uint32_t *words_sent_out) {
  if (flash_ctrl == NULL || data == NULL || words_sent_out == NULL ||
      !check_word_count(flash_ctrl, word_count)) {
    return kDifFlashCtrlProgBadArg;
  }

  // Read the CONTROL register and extract the current mode of operation.
  uint32_t op =
      mmio_region_read32(flash_ctrl->base_addr, FLASH_CTRL_CONTROL_REG_OFFSET);
  op = bitfield_field32_read(op, FLASH_CTRL_CONTROL_OP_FIELD);

  // Ensure flash controller is running and is in program mode.
  if (!is_busy(flash_ctrl) || op != FLASH_CTRL_CONTROL_OP_VALUE_PROG) {
    return kDifFlashCtrlProgInactive;
  }

  uint32_t words_sent = 0;
  // Keep writing until either the FIFO fills up or no words remain.
  while (words_sent < word_count &&
         !mmio_region_get_bit32(flash_ctrl->base_addr,
                                FLASH_CTRL_STATUS_REG_OFFSET,
                                FLASH_CTRL_STATUS_PROG_FULL_BIT)) {
    mmio_region_write32(flash_ctrl->base_addr, FLASH_CTRL_PROG_FIFO_REG_OFFSET,
                        data[words_sent]);
    ++words_sent;
  }

  // Update sw tracked transaction state.
  flash_ctrl->words_transfered += words_sent;
  // Set out-parameter in case this function must be called again.
  *words_sent_out = words_sent;

  if (words_sent < word_count) {
    return kDifFlashCtrlProgFull;
  }

  return kDifFlashCtrlProgOk;
}

dif_flash_ctrl_read_result_t dif_flash_ctrl_read_fifo_pull(
    dif_flash_ctrl_t *flash_ctrl, uint32_t word_count, uint32_t *data_out,
    size_t *words_read_out) {
  if (flash_ctrl == NULL || data_out == NULL || words_read_out == NULL ||
      !check_word_count(flash_ctrl, word_count)) {
    return kDifFlashCtrlReadBadArg;
  }

  uint32_t words_read = 0;
  // Keep reading until either the FIFO empties or no words remain (at which
  // point the FIFO should be empty anyway, but still be sure not to read more
  // than `word_count`).
  while (words_read < word_count &&
         !mmio_region_get_bit32(flash_ctrl->base_addr,
                                FLASH_CTRL_STATUS_REG_OFFSET,
                                FLASH_CTRL_STATUS_RD_EMPTY_BIT)) {
    data_out[words_read] = mmio_region_read32(flash_ctrl->base_addr,
                                              FLASH_CTRL_RD_FIFO_REG_OFFSET);
    ++words_read;
  }

  // Update sw tracked transaction state.
  flash_ctrl->words_transfered += words_read;
  // Set out-parameter in case this function must be called again.
  *words_read_out = words_read;

  if (words_read < word_count) {
    return kDifFlashCtrlReadEmpty;
  }

  return kDifFlashCtrlReadOk;
}
