// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pattgen.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/dif/dif_base.h"

#include "pattgen_regs.h"  // Generated.

dif_result_t dif_pattgen_configure_channel(
    const dif_pattgen_t *pattgen, dif_pattgen_channel_t channel,
    dif_pattgen_channel_config_t config) {
  if (pattgen == NULL || config.polarity >= kDifPattgenPolarityCount ||
      config.seed_pattern_length == 0 || config.seed_pattern_length > 64 ||
      config.num_pattern_repetitions == 0 ||
      config.num_pattern_repetitions > 1024) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t enable_bit_idx;
  bitfield_bit32_index_t polarity_bit_idx;
  ptrdiff_t clock_divisor_reg_offset;
  ptrdiff_t seed_lower_reg_offset;
  ptrdiff_t seed_upper_reg_offset;
  bitfield_field32_t seed_pattern_length_field;
  bitfield_field32_t num_pattern_repetitions_field;

#define DIF_PATTGEN_CHANNEL_CONFIG_CASE_(channel_)                          \
  case kDifPattgenChannel##channel_:                                        \
    enable_bit_idx = PATTGEN_CTRL_ENABLE_CH##channel_##_BIT;                \
    polarity_bit_idx = PATTGEN_CTRL_POLARITY_CH##channel_##_BIT;            \
    clock_divisor_reg_offset = PATTGEN_PREDIV_CH##channel_##_REG_OFFSET;    \
    seed_lower_reg_offset = PATTGEN_DATA_CH##channel_##_0_REG_OFFSET;       \
    seed_upper_reg_offset = PATTGEN_DATA_CH##channel_##_1_REG_OFFSET;       \
    seed_pattern_length_field = PATTGEN_SIZE_LEN_CH##channel_##_FIELD;      \
    num_pattern_repetitions_field = PATTGEN_SIZE_REPS_CH##channel_##_FIELD; \
    break;

  switch (channel) {
    DIF_PATTGEN_CHANNEL_LIST(DIF_PATTGEN_CHANNEL_CONFIG_CASE_)
    default:
      return kDifBadArg;
  }
#undef DIF_PATTGEN_CHANNEL_CONFIG_CASE_

  uint32_t ctrl_reg =
      mmio_region_read32(pattgen->base_addr, PATTGEN_CTRL_REG_OFFSET);

  // Check if channel is enabled. We cannot configure the channel if so.
  if (bitfield_bit32_read(ctrl_reg, enable_bit_idx)) {
    return kDifError;
  }

  // Set the polarity.
  ctrl_reg = bitfield_bit32_write(ctrl_reg, polarity_bit_idx, config.polarity);
  mmio_region_write32(pattgen->base_addr, PATTGEN_CTRL_REG_OFFSET, ctrl_reg);

  // Set the clock divisor.
  mmio_region_write32(pattgen->base_addr, clock_divisor_reg_offset,
                      config.clock_divisor);

  // Write the seed data.
  mmio_region_write32(pattgen->base_addr, seed_lower_reg_offset,
                      config.seed_pattern_lower_word);
  if (config.seed_pattern_length > 31) {
    mmio_region_write32(pattgen->base_addr, seed_upper_reg_offset,
                        config.seed_pattern_upper_word);
  }

  // Set the size and repetition values.
  uint32_t size_reg =
      mmio_region_read32(pattgen->base_addr, PATTGEN_SIZE_REG_OFFSET);
  size_reg = bitfield_field32_write(size_reg, seed_pattern_length_field,
                                    config.seed_pattern_length - 1);
  size_reg = bitfield_field32_write(size_reg, num_pattern_repetitions_field,
                                    config.num_pattern_repetitions - 1);
  mmio_region_write32(pattgen->base_addr, PATTGEN_SIZE_REG_OFFSET, size_reg);

  return kDifOk;
}

dif_result_t dif_pattgen_channel_set_enabled(const dif_pattgen_t *pattgen,
                                             dif_pattgen_channel_t channel,
                                             dif_toggle_t enabled) {
  if (pattgen == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t enable_bit_idx;

#define DIF_PATTGEN_CHANNEL_SET_ENABLED_CASE_(channel_)      \
  case kDifPattgenChannel##channel_:                         \
    enable_bit_idx = PATTGEN_CTRL_ENABLE_CH##channel_##_BIT; \
    break;

  switch (channel) {
    DIF_PATTGEN_CHANNEL_LIST(DIF_PATTGEN_CHANNEL_SET_ENABLED_CASE_)
    default:
      return kDifBadArg;
  }
#undef DIF_PATTGEN_CHANNEL_SET_ENABLED_CASE_

  uint32_t ctrl_reg =
      mmio_region_read32(pattgen->base_addr, PATTGEN_CTRL_REG_OFFSET);
  ctrl_reg = bitfield_bit32_write(ctrl_reg, enable_bit_idx,
                                  dif_toggle_to_bool(enabled));
  mmio_region_write32(pattgen->base_addr, PATTGEN_CTRL_REG_OFFSET, ctrl_reg);

  return kDifOk;
}

dif_result_t dif_pattgen_channel_get_enabled(const dif_pattgen_t *pattgen,
                                             dif_pattgen_channel_t channel,
                                             dif_toggle_t *is_enabled) {
  if (pattgen == NULL || is_enabled == NULL) {
    return kDifBadArg;
  }

  bitfield_bit32_index_t enable_bit_idx;

#define DIF_PATTGEN_CHANNEL_SET_ENABLED_CASE_(channel_)      \
  case kDifPattgenChannel##channel_:                         \
    enable_bit_idx = PATTGEN_CTRL_ENABLE_CH##channel_##_BIT; \
    break;

  switch (channel) {
    DIF_PATTGEN_CHANNEL_LIST(DIF_PATTGEN_CHANNEL_SET_ENABLED_CASE_)
    default:
      return kDifBadArg;
  }
#undef DIF_PATTGEN_CHANNEL_SET_ENABLED_CASE_

  uint32_t ctrl_reg =
      mmio_region_read32(pattgen->base_addr, PATTGEN_CTRL_REG_OFFSET);
  *is_enabled =
      dif_bool_to_toggle(bitfield_bit32_read(ctrl_reg, enable_bit_idx));

  return kDifOk;
}
