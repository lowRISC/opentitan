// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_entropy_src.h"

#include <stddef.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"

#include "entropy_src_regs.h"  // Generated.

dif_result_t dif_entropy_src_configure(const dif_entropy_src_t *entropy_src,
                                       dif_entropy_src_config_t config,
                                       dif_toggle_t enabled) {
  if (entropy_src == NULL ||
      config.single_bit_mode > kDifEntropySrcSingleBitModeDisabled ||
      !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(entropy_src->base_addr,
                          ENTROPY_SRC_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  // ENTROPY_CONTROL register configuration.

  // Conditioning bypass is hardcoded to disabled. Conditioning bypass is not
  // intended as a regular mode of operation. If, in the future, we want to
  // expose the ES_TYPE field in the future, we need to check the ES_ROUTE ==
  // true if ES_TYPE == true, and FIPS_ENABLE == false if ES_ROUTE and ES_TYPE
  // are both true.
  uint32_t es_route_val =
      config.route_to_firmware ? kMultiBitBool4True : kMultiBitBool4False;
  uint32_t entropy_ctrl_reg = bitfield_field32_write(
      0, ENTROPY_SRC_ENTROPY_CONTROL_ES_ROUTE_FIELD, es_route_val);
  entropy_ctrl_reg = bitfield_field32_write(
      entropy_ctrl_reg, ENTROPY_SRC_ENTROPY_CONTROL_ES_TYPE_FIELD,
      kMultiBitBool4False);
  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_ENTROPY_CONTROL_REG_OFFSET, entropy_ctrl_reg);

  // CONF register configuration.

  // Configure FIPS enable.
  // TODO: Add additional DIF to toggle this bit independently.
  uint32_t entropy_conf_reg = bitfield_field32_write(
      0, ENTROPY_SRC_CONF_FIPS_ENABLE_FIELD,
      config.fips_enable ? kMultiBitBool4True : kMultiBitBool4False);

  // Configure entropy data register enable (enables firmware to read entropy).
  entropy_conf_reg = bitfield_field32_write(
      entropy_conf_reg, ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_FIELD,
      config.route_to_firmware ? kMultiBitBool4True : kMultiBitBool4False);

  // Configure the health test threshold scope.
  entropy_conf_reg = bitfield_field32_write(
      entropy_conf_reg, ENTROPY_SRC_CONF_THRESHOLD_SCOPE_FIELD,
      config.health_test_threshold_scope ? kMultiBitBool4True
                                         : kMultiBitBool4False);

  // Configure single RNG bit mode.
  uint32_t rng_bit_en =
      (config.single_bit_mode == kDifEntropySrcSingleBitModeDisabled)
          ? kMultiBitBool4False
          : kMultiBitBool4True;
  entropy_conf_reg = bitfield_field32_write(
      entropy_conf_reg, ENTROPY_SRC_CONF_RNG_BIT_ENABLE_FIELD, rng_bit_en);
  uint32_t rng_bit_sel =
      (rng_bit_en == kMultiBitBool4True) ? config.single_bit_mode : 0;
  entropy_conf_reg = bitfield_field32_write(
      entropy_conf_reg, ENTROPY_SRC_CONF_RNG_BIT_SEL_FIELD, rng_bit_sel);

  uint32_t sw_rd_en =
      config.route_to_firmware ? kMultiBitBool4True : kMultiBitBool4False;
  entropy_conf_reg = bitfield_field32_write(
      entropy_conf_reg, ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_FIELD,
      sw_rd_en);

  mmio_region_write32(entropy_src->base_addr, ENTROPY_SRC_CONF_REG_OFFSET,
                      entropy_conf_reg);

  if (config.health_test_threshold_scope) {
    // Configure health test window.
    // Conditioning bypass is hardcoded to disabled (see above). If we want to
    // expose the ES_TYPE field in the future, we need to also configure the
    // health test window size for bypass mode.
    mmio_region_write32(entropy_src->base_addr,
                        ENTROPY_SRC_HEALTH_TEST_WINDOWS_REG_OFFSET,
                        config.health_test_window_size);
  }

  // MODULE_ENABLE register configuration.
  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET,
                      dif_toggle_to_multi_bit_bool4(enabled));

  return kDifOk;
}

dif_result_t dif_entropy_src_fw_override_configure(
    const dif_entropy_src_t *entropy_src,
    dif_entropy_src_fw_override_config_t config, dif_toggle_t enabled) {
  if (entropy_src == NULL ||
      config.buffer_threshold >
          ENTROPY_SRC_OBSERVE_FIFO_THRESH_OBSERVE_FIFO_THRESH_MASK ||
      config.buffer_threshold == 0 || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(entropy_src->base_addr,
                          ENTROPY_SRC_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET,
                      config.buffer_threshold);

  uint32_t reg =
      bitfield_field32_write(0, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_FIELD,
                             dif_toggle_to_multi_bit_bool4(enabled));
  reg = bitfield_field32_write(
      reg, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_FIELD,
      config.entropy_insert_enable ? kMultiBitBool4True : kMultiBitBool4False);
  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_entropy_src_health_test_configure(
    const dif_entropy_src_t *entropy_src,
    dif_entropy_src_health_test_config_t config) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(entropy_src->base_addr,
                          ENTROPY_SRC_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  ptrdiff_t high_thresholds_reg_offset = -1;
  ptrdiff_t low_thresholds_reg_offset = -1;
  switch (config.test_type) {
    case kDifEntropySrcTestRepetitionCount:
      high_thresholds_reg_offset = ENTROPY_SRC_REPCNT_THRESHOLDS_REG_OFFSET;
      // Ensure low threshold is zero. There is no low threshold for this test.
      if (config.low_threshold) {
        return kDifBadArg;
      }
      break;
    case kDifEntropySrcTestRepetitionCountSymbol:
      high_thresholds_reg_offset = ENTROPY_SRC_REPCNTS_THRESHOLDS_REG_OFFSET;
      // Ensure low threshold is zero. There is no low threshold for this test.
      if (config.low_threshold) {
        return kDifBadArg;
      }
      break;
    case kDifEntropySrcTestAdaptiveProportion:
      high_thresholds_reg_offset = ENTROPY_SRC_ADAPTP_HI_THRESHOLDS_REG_OFFSET;
      low_thresholds_reg_offset = ENTROPY_SRC_ADAPTP_LO_THRESHOLDS_REG_OFFSET;
      break;
    case kDifEntropySrcTestBucket:
      high_thresholds_reg_offset = ENTROPY_SRC_BUCKET_THRESHOLDS_REG_OFFSET;
      // Ensure low threshold is zero. There is no low threshold for this test.
      if (config.low_threshold) {
        return kDifBadArg;
      }
      break;
    case kDifEntropySrcTestMarkov:
      high_thresholds_reg_offset = ENTROPY_SRC_MARKOV_HI_THRESHOLDS_REG_OFFSET;
      low_thresholds_reg_offset = ENTROPY_SRC_MARKOV_LO_THRESHOLDS_REG_OFFSET;
      break;
    case kDifEntropySrcTestMailbox:
      high_thresholds_reg_offset = ENTROPY_SRC_EXTHT_HI_THRESHOLDS_REG_OFFSET;
      low_thresholds_reg_offset = ENTROPY_SRC_EXTHT_LO_THRESHOLDS_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }

  // Conditioning bypass is hardcoded to disabled (see above). Therefore we only
  // configure FIPS mode thresholds.
  mmio_region_write32(entropy_src->base_addr, high_thresholds_reg_offset,
                      config.high_threshold);
  if (low_thresholds_reg_offset != -1) {
    mmio_region_write32(entropy_src->base_addr, low_thresholds_reg_offset,
                        config.low_threshold);
  }

  return kDifOk;
}

dif_result_t dif_entropy_src_set_enabled(const dif_entropy_src_t *entropy_src,
                                         dif_toggle_t enabled) {
  if (entropy_src == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }

  if (!mmio_region_read32(entropy_src->base_addr,
                          ENTROPY_SRC_ME_REGWEN_REG_OFFSET)) {
    return kDifLocked;
  }

  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET,
                      dif_toggle_to_multi_bit_bool4(enabled));

  return kDifOk;
}

dif_result_t dif_entropy_src_lock(const dif_entropy_src_t *entropy_src) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(entropy_src->base_addr, ENTROPY_SRC_ME_REGWEN_REG_OFFSET,
                      0);
  mmio_region_write32(entropy_src->base_addr, ENTROPY_SRC_SW_REGUPD_REG_OFFSET,
                      0);

  return kDifOk;
}

dif_result_t dif_entropy_src_is_locked(const dif_entropy_src_t *entropy_src,
                                       bool *is_locked) {
  if (entropy_src == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  uint32_t module_enable_regwen = mmio_region_read32(
      entropy_src->base_addr, ENTROPY_SRC_ME_REGWEN_REG_OFFSET);
  uint32_t sw_regupd = mmio_region_read32(entropy_src->base_addr,
                                          ENTROPY_SRC_SW_REGUPD_REG_OFFSET);
  if (module_enable_regwen == sw_regupd) {
    *is_locked = sw_regupd == 0;
  } else {
    // Since we actuate these together, either both should be 0 (locked), or
    // both should be 1 (unlocked). If only one is locked, then we have
    // gotten into a bad state.
    return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_entropy_src_get_health_test_stats(
    const dif_entropy_src_t *entropy_src,
    dif_entropy_src_health_test_stats_t *stats) {
  if (entropy_src == NULL || stats == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t high_watermarks_reg_offset = -1;
  ptrdiff_t low_watermarks_reg_offset = -1;
  ptrdiff_t high_fails_reg_offset = -1;
  ptrdiff_t low_fails_reg_offset = -1;
  for (uint32_t i = 0; i < kDifEntropySrcTestNumVariants; ++i) {
    switch ((dif_entropy_src_test_t)i) {
      case kDifEntropySrcTestRepetitionCount:
        high_watermarks_reg_offset =
            ENTROPY_SRC_REPCNT_HI_WATERMARKS_REG_OFFSET;
        low_watermarks_reg_offset = -1;
        high_fails_reg_offset = ENTROPY_SRC_REPCNT_TOTAL_FAILS_REG_OFFSET;
        low_fails_reg_offset = -1;
        break;
      case kDifEntropySrcTestRepetitionCountSymbol:
        high_watermarks_reg_offset =
            ENTROPY_SRC_REPCNTS_HI_WATERMARKS_REG_OFFSET;
        low_watermarks_reg_offset = -1;
        high_fails_reg_offset = ENTROPY_SRC_REPCNTS_TOTAL_FAILS_REG_OFFSET;
        low_fails_reg_offset = -1;
        break;
      case kDifEntropySrcTestAdaptiveProportion:
        high_watermarks_reg_offset =
            ENTROPY_SRC_ADAPTP_HI_WATERMARKS_REG_OFFSET;
        low_watermarks_reg_offset = ENTROPY_SRC_ADAPTP_LO_WATERMARKS_REG_OFFSET;
        high_fails_reg_offset = ENTROPY_SRC_ADAPTP_HI_TOTAL_FAILS_REG_OFFSET;
        low_fails_reg_offset = ENTROPY_SRC_ADAPTP_LO_TOTAL_FAILS_REG_OFFSET;
        break;
      case kDifEntropySrcTestBucket:
        high_watermarks_reg_offset =
            ENTROPY_SRC_BUCKET_HI_WATERMARKS_REG_OFFSET;
        low_watermarks_reg_offset = -1;
        high_fails_reg_offset = ENTROPY_SRC_BUCKET_TOTAL_FAILS_REG_OFFSET;
        low_fails_reg_offset = -1;
        break;
      case kDifEntropySrcTestMarkov:
        high_watermarks_reg_offset =
            ENTROPY_SRC_MARKOV_HI_WATERMARKS_REG_OFFSET;
        low_watermarks_reg_offset = ENTROPY_SRC_MARKOV_LO_WATERMARKS_REG_OFFSET;
        high_fails_reg_offset = ENTROPY_SRC_MARKOV_HI_TOTAL_FAILS_REG_OFFSET;
        low_fails_reg_offset = ENTROPY_SRC_MARKOV_LO_TOTAL_FAILS_REG_OFFSET;
        break;
      case kDifEntropySrcTestMailbox:
        high_watermarks_reg_offset = ENTROPY_SRC_EXTHT_HI_WATERMARKS_REG_OFFSET;
        low_watermarks_reg_offset = ENTROPY_SRC_EXTHT_LO_WATERMARKS_REG_OFFSET;
        high_fails_reg_offset = ENTROPY_SRC_EXTHT_HI_TOTAL_FAILS_REG_OFFSET;
        low_fails_reg_offset = ENTROPY_SRC_EXTHT_LO_TOTAL_FAILS_REG_OFFSET;
        break;
      default:
        return kDifError;
    }

    // Conditioning bypass is hardcoded to disabled (see above). Therefore we
    // only read FIPS mode stats.
    stats->high_watermark[i] =
        mmio_region_read32(entropy_src->base_addr, high_watermarks_reg_offset);
    stats->low_watermark[i] =
        low_watermarks_reg_offset == -1
            ? 0
            : mmio_region_read32(entropy_src->base_addr,
                                 low_watermarks_reg_offset);

    stats->high_fails[i] =
        mmio_region_read32(entropy_src->base_addr, high_fails_reg_offset);
    stats->low_fails[i] =
        low_fails_reg_offset == -1
            ? 0
            : mmio_region_read32(entropy_src->base_addr, low_fails_reg_offset);
  }

  return kDifOk;
}

dif_result_t dif_entropy_src_get_alert_fail_counts(
    const dif_entropy_src_t *entropy_src,
    dif_entropy_src_alert_fail_counts_t *counts) {
  if (entropy_src == NULL || counts == NULL) {
    return kDifBadArg;
  }

  counts->total_fails = mmio_region_read32(
      entropy_src->base_addr, ENTROPY_SRC_ALERT_SUMMARY_FAIL_COUNTS_REG_OFFSET);

  uint32_t alert_fail_counts = mmio_region_read32(
      entropy_src->base_addr, ENTROPY_SRC_ALERT_FAIL_COUNTS_REG_OFFSET);
  uint32_t extht_alert_fail_counts = mmio_region_read32(
      entropy_src->base_addr, ENTROPY_SRC_EXTHT_FAIL_COUNTS_REG_OFFSET);

  // Unpack high threshold failure counts.
  counts->high_fails[kDifEntropySrcTestRepetitionCount] = bitfield_field32_read(
      alert_fail_counts, ENTROPY_SRC_ALERT_FAIL_COUNTS_REPCNT_FAIL_COUNT_FIELD);
  counts->high_fails[kDifEntropySrcTestRepetitionCountSymbol] =
      bitfield_field32_read(
          alert_fail_counts,
          ENTROPY_SRC_ALERT_FAIL_COUNTS_REPCNTS_FAIL_COUNT_FIELD);
  counts->high_fails[kDifEntropySrcTestAdaptiveProportion] =
      bitfield_field32_read(
          alert_fail_counts,
          ENTROPY_SRC_ALERT_FAIL_COUNTS_ADAPTP_HI_FAIL_COUNT_FIELD);
  counts->high_fails[kDifEntropySrcTestBucket] = bitfield_field32_read(
      alert_fail_counts, ENTROPY_SRC_ALERT_FAIL_COUNTS_BUCKET_FAIL_COUNT_FIELD);
  counts->high_fails[kDifEntropySrcTestMarkov] = bitfield_field32_read(
      alert_fail_counts,
      ENTROPY_SRC_ALERT_FAIL_COUNTS_MARKOV_HI_FAIL_COUNT_FIELD);
  counts->high_fails[kDifEntropySrcTestMailbox] = bitfield_field32_read(
      extht_alert_fail_counts,
      ENTROPY_SRC_EXTHT_FAIL_COUNTS_EXTHT_HI_FAIL_COUNT_FIELD);

  // Unpack low threshold failure counts.
  counts->low_fails[kDifEntropySrcTestRepetitionCount] = 0;
  counts->low_fails[kDifEntropySrcTestRepetitionCountSymbol] = 0;
  counts->low_fails[kDifEntropySrcTestAdaptiveProportion] =
      bitfield_field32_read(
          alert_fail_counts,
          ENTROPY_SRC_ALERT_FAIL_COUNTS_ADAPTP_LO_FAIL_COUNT_FIELD);
  counts->low_fails[kDifEntropySrcTestBucket] = 0;
  counts->low_fails[kDifEntropySrcTestMarkov] = bitfield_field32_read(
      alert_fail_counts,
      ENTROPY_SRC_ALERT_FAIL_COUNTS_MARKOV_LO_FAIL_COUNT_FIELD);
  counts->low_fails[kDifEntropySrcTestMailbox] = bitfield_field32_read(
      extht_alert_fail_counts,
      ENTROPY_SRC_EXTHT_FAIL_COUNTS_EXTHT_LO_FAIL_COUNT_FIELD);

  return kDifOk;
}

static bool get_entropy_avail(const dif_entropy_src_t *entropy_src) {
  return mmio_region_get_bit32(entropy_src->base_addr,
                               ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                               ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);
}

dif_result_t dif_entropy_src_avail(const dif_entropy_src_t *entropy_src) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }

  return get_entropy_avail(entropy_src) ? kDifOk : kDifUnavailable;
}

dif_result_t dif_entropy_src_read(const dif_entropy_src_t *entropy_src,
                                  uint32_t *word) {
  if (entropy_src == NULL || word == NULL) {
    return kDifBadArg;
  }

  // Check if entropy is available
  if (!get_entropy_avail(entropy_src)) {
    return kDifUnavailable;
  }

  *word = mmio_region_read32(entropy_src->base_addr,
                             ENTROPY_SRC_ENTROPY_DATA_REG_OFFSET);

  // clear interrupt state after fetching read
  // if there is still entropy available, the interrupt state will set again
  mmio_region_nonatomic_set_bit32(entropy_src->base_addr,
                                  ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                                  ENTROPY_SRC_INTR_STATE_ES_ENTROPY_VALID_BIT);

  return kDifOk;
}

dif_result_t dif_entropy_src_fifo_read(const dif_entropy_src_t *entropy_src,
                                       uint32_t *buf, size_t len) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(entropy_src->base_addr,
                                    ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET);
  if (bitfield_field32_read(reg, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_FIELD) !=
      kMultiBitBool4True) {
    return kDifError;
  }

  reg = mmio_region_read32(entropy_src->base_addr,
                           ENTROPY_SRC_OBSERVE_FIFO_THRESH_REG_OFFSET);
  if (reg < len) {
    return kDifBadArg;
  }

  do {
    reg = mmio_region_read32(entropy_src->base_addr,
                             ENTROPY_SRC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(
      reg, ENTROPY_SRC_INTR_STATE_ES_OBSERVE_FIFO_READY_BIT));

  for (size_t i = 0; i < len; ++i) {
    reg = mmio_region_read32(entropy_src->base_addr,
                             ENTROPY_SRC_FW_OV_RD_DATA_REG_OFFSET);
    if (buf != NULL) {
      buf[i] = reg;
    }
  }

  // Clear the status bit.
  reg = bitfield_bit32_write(
      0, ENTROPY_SRC_INTR_STATE_ES_OBSERVE_FIFO_READY_BIT, true);
  mmio_region_write32(entropy_src->base_addr, ENTROPY_SRC_INTR_STATE_REG_OFFSET,
                      reg);
  return kDifOk;
}

dif_result_t dif_entropy_src_fifo_write(const dif_entropy_src_t *entropy_src,
                                        const uint32_t *buf, size_t len) {
  if (entropy_src == NULL || buf == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(entropy_src->base_addr,
                                    ENTROPY_SRC_FW_OV_CONTROL_REG_OFFSET);
  if (bitfield_field32_read(reg, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_MODE_FIELD) !=
          kMultiBitBool4True ||
      bitfield_field32_read(
          reg, ENTROPY_SRC_FW_OV_CONTROL_FW_OV_ENTROPY_INSERT_FIELD) !=
          kMultiBitBool4True) {
    return kDifUnavailable;
  }

  for (size_t i = 0; i < len; ++i) {
    mmio_region_write32(entropy_src->base_addr,
                        ENTROPY_SRC_FW_OV_WR_DATA_REG_OFFSET, buf[i]);
  }
  return kDifOk;
}

dif_result_t dif_entropy_src_conditioner_start(
    const dif_entropy_src_t *entropy_src) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }

  // Check if SHA3 conditioner operation has already started.
  uint32_t current_val = mmio_region_read32(
      entropy_src->base_addr, ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET);
  if (current_val == kMultiBitBool4True) {
    return kDifUnavailable;
  }

  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET,
                      kMultiBitBool4True);

  return kDifOk;
}

dif_result_t dif_entropy_src_conditioner_end(
    const dif_entropy_src_t *entropy_src) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_FW_OV_SHA3_START_REG_OFFSET,
                      kMultiBitBool4False);
  return kDifOk;
}

dif_result_t dif_entropy_src_get_fifo_depth(
    const dif_entropy_src_t *entropy_src, uint32_t *fifo_depth) {
  if (entropy_src == NULL || fifo_depth == NULL) {
    return kDifBadArg;
  }

  *fifo_depth = mmio_region_read32(entropy_src->base_addr,
                                   ENTROPY_SRC_OBSERVE_FIFO_DEPTH_REG_OFFSET);

  return kDifOk;
}
