// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/nvm_testutils.h"

#include "sw/device/lib/testing/flash_ctrl_testutils.h"

// All functions here forward to flash_ctrl_testutils.
// When switching to a different NVM technology, replace the bodies with calls
// to the new testutils layer.

status_t nvm_testutils_wait_for_init(dif_nvm_ctrl_state_t *nvm) {
  return flash_ctrl_testutils_wait_for_init(nvm);
}

status_t nvm_testutils_wait_transaction_end(dif_nvm_ctrl_state_t *nvm) {
  return flash_ctrl_testutils_wait_transaction_end(nvm);
}

status_t nvm_testutils_data_region_setup_properties(
    dif_nvm_ctrl_state_t *nvm, uint32_t base_page_index, uint32_t data_region,
    uint32_t region_size, dif_nvm_ctrl_region_properties_t region_properties,
    uint32_t *offset) {
  return flash_ctrl_testutils_data_region_setup_properties(
      nvm, base_page_index, data_region, region_size, region_properties,
      offset);
}

status_t nvm_testutils_data_region_setup(dif_nvm_ctrl_state_t *nvm,
                                         uint32_t base_page_index,
                                         uint32_t data_region,
                                         uint32_t region_size,
                                         uint32_t *offset) {
  return flash_ctrl_testutils_data_region_setup(
      nvm, base_page_index, data_region, region_size, offset);
}

status_t nvm_testutils_data_region_scrambled_setup(dif_nvm_ctrl_state_t *nvm,
                                                   uint32_t base_page_index,
                                                   uint32_t data_region,
                                                   uint32_t region_size,
                                                   uint32_t *offset) {
  return flash_ctrl_testutils_data_region_scrambled_setup(
      nvm, base_page_index, data_region, region_size, offset);
}

status_t nvm_testutils_info_region_setup_properties(
    dif_nvm_ctrl_state_t *nvm, uint32_t page_id, uint32_t bank,
    uint32_t partition_id, dif_nvm_ctrl_region_properties_t region_properties,
    uint32_t *offset) {
  return flash_ctrl_testutils_info_region_setup_properties(
      nvm, page_id, bank, partition_id, region_properties, offset);
}

status_t nvm_testutils_info_region_setup(dif_nvm_ctrl_state_t *nvm,
                                         uint32_t page_id, uint32_t bank,
                                         uint32_t partition_id,
                                         uint32_t *offset) {
  return flash_ctrl_testutils_info_region_setup(nvm, page_id, bank,
                                                partition_id, offset);
}

status_t nvm_testutils_info_region_scrambled_setup(dif_nvm_ctrl_state_t *nvm,
                                                   uint32_t page_id,
                                                   uint32_t bank,
                                                   uint32_t partition_id,
                                                   uint32_t *offset) {
  return flash_ctrl_testutils_info_region_scrambled_setup(nvm, page_id, bank,
                                                          partition_id, offset);
}

status_t nvm_testutils_erase_page(
    dif_nvm_ctrl_state_t *nvm, uint32_t byte_address, uint32_t partition_id,
    dif_nvm_ctrl_partition_type_t partition_type) {
  return flash_ctrl_testutils_erase_page(nvm, byte_address, partition_id,
                                         partition_type);
}

status_t nvm_testutils_write(dif_nvm_ctrl_state_t *nvm, uint32_t byte_address,
                             uint32_t partition_id, const uint32_t *data,
                             dif_nvm_ctrl_partition_type_t partition_type,
                             uint32_t word_count) {
  return flash_ctrl_testutils_write(nvm, byte_address, partition_id, data,
                                    partition_type, word_count);
}

status_t nvm_testutils_erase_and_write_page(
    dif_nvm_ctrl_state_t *nvm, uint32_t byte_address, uint32_t partition_id,
    const uint32_t *data, dif_nvm_ctrl_partition_type_t partition_type,
    uint32_t word_count) {
  return flash_ctrl_testutils_erase_and_write_page(
      nvm, byte_address, partition_id, data, partition_type, word_count);
}

status_t nvm_testutils_read(dif_nvm_ctrl_state_t *nvm, uint32_t byte_address,
                            uint32_t partition_id, uint32_t *data_out,
                            dif_nvm_ctrl_partition_type_t partition_type,
                            uint32_t word_count, uint32_t delay) {
  return flash_ctrl_testutils_read(nvm, byte_address, partition_id, data_out,
                                   partition_type, word_count, delay);
}

status_t nvm_testutils_default_region_access(dif_nvm_ctrl_state_t *nvm,
                                             bool rd_en, bool prog_en,
                                             bool erase_en, bool scramble_en,
                                             bool ecc_en,
                                             bool high_endurance_en) {
  return flash_ctrl_testutils_default_region_access(
      nvm, rd_en, prog_en, erase_en, scramble_en, ecc_en, high_endurance_en);
}

status_t nvm_testutils_bank_erase(dif_nvm_ctrl_state_t *nvm, uint32_t bank,
                                  bool data_only) {
  return flash_ctrl_testutils_bank_erase(nvm, bank, data_only);
}

status_t nvm_testutils_show_faults(const dif_nvm_ctrl_state_t *nvm) {
  return flash_ctrl_testutils_show_faults(nvm);
}
