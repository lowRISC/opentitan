// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/isfb.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

rom_error_t isfb_boot_request_process(const manifest_ext_isfb_t *ext,
                                      const owner_config_t *owner_config,
                                      uint32_t *checks_performed_count) {
  (void)ext;
  (void)owner_config;
  *checks_performed_count = UINT32_MAX;
  return kErrorOwnershipISFBNotPresent;
}

rom_error_t isfb_info_flash_erase_policy_get(
    const owner_config_t *owner_config, uint32_t key_domain,
    hardened_bool_t manifest_is_node_locked,
    const manifest_ext_isfb_erase_t *ext_isfb_erase,
    hardened_bool_t *erase_en) {
  (void)owner_config;
  (void)key_domain;
  (void)manifest_is_node_locked;
  (void)ext_isfb_erase;
  *erase_en = kHardenedBoolFalse;
  return kErrorOk;
}

rom_error_t owner_block_info_isfb_erase_enable(
    boot_data_t *bootdata, const owner_config_t *owner_config) {
  (void)bootdata;
  (void)owner_config;
  return kErrorOk;
}

rom_error_t isfb_check_and_verify(const manifest_t *manifest,
                                  const owner_config_t *owner_config,
                                  uint32_t *isfb_check_count) {
  (void)manifest;
  (void)owner_config;
  *isfb_check_count = kHardenedBoolFalse;
  return kErrorOk;
}

rom_error_t isfb_boot_verify(const manifest_t *manifest,
                             const owner_config_t *owner_config,
                             const owner_application_keyring_t *keyring,
                             size_t verify_key, boot_data_t *boot_data,
                             uint32_t isfb_check_count) {
  (void)manifest;
  (void)owner_config;
  (void)keyring;
  (void)verify_key;
  (void)boot_data;
  (void)isfb_check_count;
  return kErrorOk;
}

hardened_bool_t isfb_is_present(void) { return kHardenedBoolFalse; }
