// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/lib/ownership/isfb.h"

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

enum {
  kFlashWordSize = 64,

  // The maximum number of product expressions is 256, which maps to 512 flash
  // words or 1024 bytes.
  kProductExprMaxCount = 256,

  // The maximum size of the product expressions in bytes.
  KProductExprMaxCountBytes = kProductExprMaxCount * sizeof(uint32_t),

  // The expected size of the strike region in bytes and words.
  kExpectedStrikeRegionBytesCount =
      kIsfbExpectedStrikeBitCount * sizeof(uint32_t),
  kExpectedStrikeRegionWordsCount =
      kExpectedStrikeRegionBytesCount / sizeof(uint32_t),
};

rom_error_t isfb_boot_request_process(const manifest_ext_isfb_t *ext,
                                      const owner_config_t *owner_config,
                                      uint32_t *checks_performed_count) {
  *checks_performed_count = UINT32_MAX;
  if (ext->header.name != kManifestExtIdIsfb ||
      (hardened_bool_t)owner_config->isfb == kHardenedBoolFalse) {
    return kErrorOwnershipISFBNotPresent;
  }
  const owner_isfb_config_t *isfb = owner_config->isfb;
  if (ext->product_expr_count > isfb->product_words ||
      ext->product_expr_count > kProductExprMaxCount) {
    return kErrorOwnershipISFBProductExpCnt;
  }

  // The ISFB info page configuration is handled in the owner's
  // `FlashInfoConfig` settings.
  flash_ctrl_info_page_t isfb_info_page;
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_type0_params_build(
      isfb->bank, isfb->page, &isfb_info_page));

  // There are in total 128 bits in the strike mask. Each bit corresponds to a
  // `uint32_t` word.
  uint32_t strikes[kExpectedStrikeRegionWordsCount];
  static_assert(
      sizeof(ext->strike_mask) * CHAR_BIT == kIsfbExpectedStrikeBitCount,
      "Strike mask size mismatch");
  static_assert(sizeof(strikes) == kExpectedStrikeRegionBytesCount,
                "Data size mismatch");

  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(&isfb_info_page, /*offset=*/0,
                                                ARRAYSIZE(strikes), strikes));

  uint32_t strike_cnt_ok = 0;
  uint32_t strike_cnt_bad = 0;
  uint32_t *strike_word = (uint32_t *)strikes;
  size_t i;
  for (i = 0; i < ARRAYSIZE(strikes); ++i, ++strike_word) {
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
                    kIsfbExpectedStrikeBitCount * 2);

  if (launder32(strike_cnt_bad) > 0) {
    return kErrorOwnershipISFBStrikeMask;
  }

  uint32_t product_expr[kProductExprMaxCount];
  static_assert(sizeof(product_expr) == KProductExprMaxCountBytes,
                "Product expressions data size mismatch");

  // Read the product expressions from the ISFB info page.
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read(
      &isfb_info_page, /*offset=*/1024, ARRAYSIZE(product_expr), product_expr));

  uint32_t pe_cnt_ok = 0;
  uint32_t p_cnt_bad = 0;

  // The `product_expr_count` boundary check is performed at the beginning of
  // the function.
  for (i = 0; i < ext->product_expr_count; ++i) {
    if ((product_expr[i] & ext->product_expr[i].mask) ==
        ext->product_expr[i].value) {
      pe_cnt_ok++;
    } else {
      p_cnt_bad++;
    }
  }
  HARDENED_CHECK_EQ(pe_cnt_ok + p_cnt_bad + i, 2 * ext->product_expr_count);

  if (launder32(p_cnt_bad) > 0) {
    return kErrorOwnershipISFBProductExp;
  }

  // Redundant checks to ensure there were no faults in any previous checks.
  if (launder32(strike_cnt_ok) == kIsfbExpectedStrikeBitCount &&
      launder32(strike_cnt_bad) == 0 &&
      launder32(pe_cnt_ok) == ext->product_expr_count &&
      launder32(p_cnt_bad) == 0) {
    *checks_performed_count =
        kIsfbExpectedStrikeBitCount + ext->product_expr_count;
    return kErrorOk;
  }

  *checks_performed_count = UINT32_MAX;
  return kErrorOwnershipISFBFailed;
}

rom_error_t isfb_info_flash_erase_policy_get(
    owner_config_t *owner_config, uint32_t key_domain,
    hardened_bool_t manifest_is_node_locked,
    const manifest_ext_isfb_erase_t *ext_isfb_erase,
    hardened_bool_t *erase_en) {
  if ((hardened_bool_t)owner_config->isfb == kHardenedBoolFalse) {
    return kErrorOwnershipISFBNotPresent;
  }

  uint32_t check_cnt_exp = 0;
  uint32_t conditions = owner_config->isfb->erase_conditions;
  hardened_bool_t policies[3] = {0};
  static_assert(ARRAYSIZE(policies) <= sizeof(conditions) * 2,
                "Erase conditions count mismatch");

  // Only disable the expected check iff strictly set to `kMultiBitBool4False`
  // in the owner config. Any other value will require the check to be
  // performed.
  for (uint32_t i = 0; i < ARRAYSIZE(policies); ++i, conditions >>= 4) {
    if (launder32(conditions & 0xF) == kMultiBitBool4False) {
      policies[i] = kHardenedBoolTrue;
    } else {
      check_cnt_exp = launder32(check_cnt_exp) + 1;
    }
  }

  // Hardended counter used to detect any faults in the checks.
  uint32_t check_cnt_got = 0;

  // B0: Firmware must be signed with key specified by `key_domain` field.
  if (policies[0] != kHardenedBoolTrue && key_domain &&
      key_domain == owner_config->isfb->key_domain) {
    policies[0] = kHardenedBoolTrue;
    check_cnt_got = launder32(check_cnt_got) + 1;
  }

  // B1: Firmware must be node locked.
  if (policies[1] != kHardenedBoolTrue &&
      manifest_is_node_locked == kHardenedBoolTrue) {
    policies[1] = kHardenedBoolTrue;
    check_cnt_got = launder32(check_cnt_got) + 1;
  }

  // B3: `manifest_ext_isfb_erase_t` must be present and set to harden true in
  // the firmware manifest.
  if (policies[2] != kHardenedBoolTrue && ext_isfb_erase != NULL) {
    policies[2] = (hardened_bool_t)ext_isfb_erase->erase_allowed;
    check_cnt_got = launder32(check_cnt_got) + 1;
  }

  if (policies[0] == kHardenedBoolTrue && policies[1] == kHardenedBoolTrue &&
      policies[2] == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(check_cnt_got, check_cnt_exp);
    // The erase policy is satisfied. Update the info flash page configuration
    // with the new erase policy.
    *erase_en = kHardenedBoolTrue;
  }

  return kErrorOk;
}
