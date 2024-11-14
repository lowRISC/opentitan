// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#include "flash_ctrl_regs.h"

enum {
  kFlashPageBytes = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
  kFlashPageWords = kFlashPageBytes / sizeof(uint32_t),

  // The maximum number of product expressions is 256, which maps to 512 flash
  // words or 1024 bytes.
  kProductExprMaxCount = 256,

  // The maximum size of the product expressions in bytes.
  KProductExprMaxCountBytes = kProductExprMaxCount * sizeof(uint32_t),

  // The number of bits in the strike mask is fixed to 128. Each bit in the
  // strike mask corresponds to a flash word.
  kExpectedStrikeBitCount = 128,

  // The expected size of the strike region in bytes and words.
  kExpectedStrikeRegionBytesCount = kExpectedStrikeBitCount * sizeof(uint32_t),
  kExpectedStrikeRegionWordsCount =
      kExpectedStrikeRegionBytesCount / sizeof(uint32_t),

  // The layout of the ISFB info page is as follows:
  //
  // | byte start      | byte end | description
  // |-----------------|----------|------------
  // | 0               | 511      | Strike mask
  // | 512             | 1023     | Unused and available to owner firmware.
  // | 1024            | OnwerCfg | Product expression constraints.
  // | 1024 + OwnerCfg | 2047     | Unused and available to owner firmware.
  kIsfbWordOffsetStartStrikeRegion = 0,
  kIsfbWordOffsetStartProductExpr = 1024 / sizeof(uint32_t),
};
static_assert(kExpectedStrikeRegionWordsCount == kExpectedStrikeBitCount,
              "Unexpected strike region size");
static_assert(kIsfbWordOffsetStartProductExpr * sizeof(uint32_t) +
                      KProductExprMaxCountBytes ==
                  kFlashPageBytes,
              "Product expression total size overflows page size");

rom_error_t isfb_boot_request_process(const manifest_ext_isfb_t *ext,
                                      const owner_config_t *owner_config,
                                      uint32_t *checks_performed_count) {
  *checks_performed_count = UINT32_MAX;
  if (ext->header.name != kManifestExtIdIsfb ||
      (hardened_bool_t)owner_config->isfb == kHardenedBoolFalse) {
    return kErrorOwnershipISFBNotPresent;
  }
  const owner_isfb_config_t *isfb = owner_config->isfb;
  if (ext->product_expr_count * 2 > isfb->product_words ||
      ext->product_expr_count > kProductExprMaxCount) {
    return kErrorOwnershipISFBProductExpCnt;
  }

  flash_ctrl_perms_t perm = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4False,
  };
  flash_ctrl_cfg_t cfg = {
      .scrambling = kMultiBitBool4False,
      .ecc = kMultiBitBool4True,
      .he = kMultiBitBool4False,
  };

  flash_ctrl_info_page_t isfb_info_page;
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_type0_params_build(
      isfb->bank, isfb->page, &isfb_info_page));
  flash_ctrl_info_perms_set(&isfb_info_page, perm);
  flash_ctrl_info_cfg_set(&isfb_info_page, cfg);

  // There are in total 128 bits in the strike mask. Each bit corresponds to a
  // flash word. Each flash word is 64 bits.
  uint32_t data[kFlashPageWords];
  static_assert(sizeof(ext->strike_mask) * CHAR_BIT == kExpectedStrikeBitCount,
                "Strike mask size mismatch");
  static_assert(sizeof(data) >= kFlashPageBytes, "Unexpected data size");

  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(&isfb_info_page, /*offset=*/0,
                                                ARRAYSIZE(data), data));

  uint32_t strike_cnt_ok = 0;
  uint32_t strike_cnt_bad = 0;
  uint32_t *strike_word = &data[kIsfbWordOffsetStartStrikeRegion];
  size_t i;
  for (i = 0; i < kExpectedStrikeRegionWordsCount; ++i, ++strike_word) {
    uint32_t strike_bit = ext->strike_mask[i >> 5] & (1 << (i & 31));
    if (launder32(strike_bit) && *strike_word != UINT32_MAX) {
      strike_cnt_bad++;
    } else if (!launder32(strike_bit) || *strike_word == UINT32_MAX) {
      strike_cnt_ok++;
    } else {
      // This condition is equivalent to a potential fault in either the strike
      // mask or the ISFB info buffer.
      strike_cnt_bad++;
    }
  }
  // Check loop completion and count consistency.
  HARDENED_CHECK_EQ(strike_cnt_ok + strike_cnt_bad + i,
                    kExpectedStrikeBitCount * 2);

  if (launder32(strike_cnt_bad) > 0) {
    return kErrorOwnershipISFBStrikeMask;
  }

  uint32_t pexpr_cnt_ok = 0;
  uint32_t pexpr_cnt_bad = 0;

  // The `product_expr_count` boundary check is performed at the beginning of
  // the function.
  uint32_t *product_expr = &data[kIsfbWordOffsetStartProductExpr];
  for (i = 0; i < ext->product_expr_count; ++i, ++product_expr) {
    if ((*product_expr & ext->product_expr[i].mask) ==
        ext->product_expr[i].value) {
      pexpr_cnt_ok++;
    } else {
      pexpr_cnt_bad++;
    }
  }
  HARDENED_CHECK_EQ(pexpr_cnt_ok + pexpr_cnt_bad, ext->product_expr_count);
  HARDENED_CHECK_EQ(i, ext->product_expr_count);

  if (launder32(pexpr_cnt_bad) > 0) {
    return kErrorOwnershipISFBProductExp;
  }

  // Redundant checks to ensure there were no faults in any previous checks.
  if (launder32(strike_cnt_ok) == kExpectedStrikeBitCount &&
      launder32(strike_cnt_bad) == 0 &&
      launder32(pexpr_cnt_ok) == ext->product_expr_count &&
      launder32(pexpr_cnt_bad) == 0) {
    *checks_performed_count = kExpectedStrikeBitCount + ext->product_expr_count;
    return kErrorOk;
  }

  *checks_performed_count = UINT32_MAX;
  return kErrorOwnershipISFBFailed;
}
