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

  // Configure health test window.
  // Conditioning bypass is hardcoded to disabled (see above). If we want to
  // expose the ES_TYPE field in the future, we need to also configure the
  // health test window size for bypass mode.
  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_HEALTH_TEST_WINDOWS_REG_OFFSET,
                      config.health_test_window_size);

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
    return kDifBadArg;
  }

  for (size_t i = 0; i < len; ++i) {
    mmio_region_write32(entropy_src->base_addr,
                        ENTROPY_SRC_FW_OV_WR_DATA_REG_OFFSET, buf[i]);
  }
  return kDifOk;
}

dif_result_t dif_entropy_src_disable(const dif_entropy_src_t *entropy_src) {
  if (entropy_src == NULL) {
    return kDifBadArg;
  }

  // TODO: should first check if entropy is locked and return error if it is.
  mmio_region_write32(entropy_src->base_addr,
                      ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET,
                      kMultiBitBool4False);

  return kDifOk;
}
