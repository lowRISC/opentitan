// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#ifdef WITH_OWNERSHIP_INFO
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

status_t ownership_print(void) {
  owner_block_t config;
  TRY(nvm_ctrl_info_read(kNvmInfoPageOwnerSlot0, 0,
                         sizeof(config) / sizeof(uint32_t), &config));

  LOG_INFO("owner_page0 tag = %C", config.header.tag);
  LOG_INFO("owner_page0 ownership_key_alg = %C", config.ownership_key_alg);
  LOG_INFO("owner_page0 config_version = %d", config.config_version);
  LOG_INFO("owner_page0 min_security_version_bl0 = %08x",
           config.min_security_version_bl0);
  LOG_INFO("owner_page0 update_mode = %C", config.update_mode);
  LOG_INFO("owner_page0 owner_key = %08x", config.owner_key.raw[0]);
  return OK_STATUS();
}
#else
status_t ownership_print(void) { return OK_STATUS(); }
#endif

#ifdef WITH_KEYMGR_DPE
#include "sw/device/lib/dif/dif_keymgr_dpe.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const char *keymgr_dpe_state(dif_keymgr_dpe_state_t s) {
  switch (s) {
    case kDifKeymgrDpeStateReset:
      return "Reset";
    case kDifKeymgrDpeStateAvailable:
      return "Available";
    case kDifKeymgrDpeStateDisabled:
      return "Disabled";
    case kDifKeymgrDpeStateInvalid:
      return "Invalid";
    default:
      return "Unknown";
  }
}

status_t keymgr_dpe_print(void) {
  dif_keymgr_dpe_t km;
  TRY(dif_keymgr_dpe_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR), &km));

  dif_keymgr_dpe_state_t state;
  TRY(dif_keymgr_dpe_get_state(&km, &state));
  LOG_INFO("keymgr dpe state = %s", keymgr_dpe_state(state));

  dif_keymgr_dpe_generate_params_t p = {
      .key_dest = kDifKeymgrDpeKeyDestNone,
      .sideload_key = false,
      .salt = {1, 2, 3, 4, 5, 6, 7, 8},
      .version = 0,
      .slot_src_sel = 0,
  };
  TRY(dif_keymgr_dpe_generate(&km, &p));

  // Wait for the generation to finish
  dif_keymgr_dpe_status_codes_t status;
  do {
    TRY(dif_keymgr_dpe_get_status_codes(&km, &status));
  } while (status == 0);
  // Ensure the operation is finished and no error was raised
  TRY_CHECK(status == kDifKeymgrDpeStatusCodeIdle, "keymgr_dpe generate: %x",
            status);

  dif_keymgr_dpe_output_t out;
  TRY(dif_keymgr_dpe_read_output(&km, &out));
  LOG_INFO("keymgr dpe sw_key = %08x%08x%08x%08x%08x%08x%08x%08x",
           out.value[0][0] ^ out.value[1][0], out.value[0][1] ^ out.value[1][1],
           out.value[0][2] ^ out.value[1][2], out.value[0][3] ^ out.value[1][3],
           out.value[0][4] ^ out.value[1][4], out.value[0][5] ^ out.value[1][5],
           out.value[0][6] ^ out.value[1][6],
           out.value[0][7] ^ out.value[1][7]);

  return OK_STATUS();
}
#else
status_t keymgr_dpe_print(void) { return OK_STATUS(); }
#endif

#ifdef WITH_MANIFEST
#include "sw/device/silicon_creator/lib/manifest.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

status_t manifest_print(void) {
  const manifest_t *a =
      (const manifest_t *)TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
  const manifest_t *b =
      (const manifest_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                           (TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2));
  LOG_INFO("slot_a rom_ext_id = %C", a->identifier);
  LOG_INFO("slot_a rom_ext_version = %u.%u", a->version_major,
           a->version_minor);
  LOG_INFO("slot_b rom_ext_id = %C", b->identifier);
  LOG_INFO("slot_b rom_ext_version = %u.%u", b->version_major,
           b->version_minor);
  return OK_STATUS();
}
#else
status_t manifest_print(void) { return OK_STATUS(); }
#endif

OTTF_DEFINE_TEST_CONFIG();

status_t boot_log_print(boot_log_t *boot_log) {
  TRY(boot_log_check(boot_log));
  LOG_INFO("boot_log identifier = %C", boot_log->identifier);
  LOG_INFO("boot_log chip_version = %08x%08x",
           boot_log->chip_version.scm_revision_high,
           boot_log->chip_version.scm_revision_low);

  LOG_INFO("boot_log rom_ext_slot = %C", boot_log->rom_ext_slot);
  LOG_INFO("boot_log rom_ext_version = %d.%d", boot_log->rom_ext_major,
           boot_log->rom_ext_minor);
  LOG_INFO("boot_log rom_ext_size = 0x%08x", boot_log->rom_ext_size);
  LOG_INFO("boot_log rom_ext_nonce = %08x%08x",
           boot_log->rom_ext_nonce.value[1], boot_log->rom_ext_nonce.value[0]);
  LOG_INFO("boot_log bl0_slot = %C", boot_log->bl0_slot);
  LOG_INFO("boot_log ownership_state = %C", boot_log->ownership_state);
  LOG_INFO("boot_log ownership_transfers = %u", boot_log->ownership_transfers);
  LOG_INFO("boot_log rom_ext_min_sec_ver = %u", boot_log->rom_ext_min_sec_ver);
  LOG_INFO("boot_log bl0_min_sec_ver = %u", boot_log->bl0_min_sec_ver);
  LOG_INFO("boot_log primary_bl0_slot = %C", boot_log->primary_bl0_slot);
  TRY(manifest_print());
  TRY(ownership_print());
  TRY(keymgr_dpe_print());
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = boot_log_print(&retention_sram_get()->creator.boot_log);
  if (status_err(sts)) {
    LOG_ERROR("boot_log_print: %r", sts);
  }
  return status_ok(sts);
}
