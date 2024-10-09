// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#ifdef WITH_OWNERSHIP_INFO
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

status_t ownership_print(void) {
  owner_block_t config;
  TRY(flash_ctrl_info_read(&kFlashCtrlInfoPageOwnerSlot0, 0,
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

#ifdef WITH_KEYMGR
#include "sw/device/lib/dif/dif_keymgr.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const char *keymgr_state(dif_keymgr_state_t s) {
  switch (s) {
    case kDifKeymgrStateReset:
      return "Reset";
    case kDifKeymgrStateInitialized:
      return "Initialized";
    case kDifKeymgrStateCreatorRootKey:
      return "CreatorRootKey";
    case kDifKeymgrStateOwnerIntermediateKey:
      return "OwnerIntermediateKey";
    case kDifKeymgrStateOwnerRootKey:
      return "OwnerRootKey";
    case kDifKeymgrStateDisabled:
      return "Disabled";
    case kDifKeymgrStateInvalid:
      return "Invalid";
    default:
      return "Unknown";
  }
}

status_t keymgr_print(void) {
  dif_keymgr_t km;
  TRY(dif_keymgr_init(mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR),
                      &km));

  dif_keymgr_state_t state;
  TRY(dif_keymgr_get_state(&km, &state));
  LOG_INFO("keymgr state = %s", keymgr_state(state));

  dif_keymgr_binding_value_t bind;
  TRY(dif_keymgr_read_binding(&km, &bind));
  LOG_INFO("keymgr bind_sealing = %08x%08x%08x%08x%08x%08x%08x%08x",
           bind.sealing[0], bind.sealing[1], bind.sealing[2], bind.sealing[3],
           bind.sealing[4], bind.sealing[5], bind.sealing[6], bind.sealing[7]);
  LOG_INFO("keymgr bind_attest = %08x%08x%08x%08x%08x%08x%08x%08x",
           bind.attestation[0], bind.attestation[1], bind.attestation[2],
           bind.attestation[3], bind.attestation[4], bind.attestation[5],
           bind.attestation[6], bind.attestation[7]);

  dif_keymgr_versioned_key_params_t p = {kDifKeymgrVersionedKeyDestSw};
  TRY(dif_keymgr_generate_versioned_key(&km, p));

  dif_keymgr_output_t out;
  TRY(dif_keymgr_read_output(&km, &out));
  LOG_INFO("keymgr sw_key = %08x%08x%08x%08x%08x%08x%08x%08x",
           out.value[0][0] ^ out.value[1][0], out.value[0][1] ^ out.value[1][1],
           out.value[0][2] ^ out.value[1][2], out.value[0][3] ^ out.value[1][3],
           out.value[0][4] ^ out.value[1][4], out.value[0][5] ^ out.value[1][5],
           out.value[0][6] ^ out.value[1][6],
           out.value[0][7] ^ out.value[1][7]);

  return OK_STATUS();
}
#else
status_t keymgr_print(void) { return OK_STATUS(); }
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
  TRY(ownership_print());
  TRY(keymgr_print());
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = boot_log_print(&retention_sram_get()->creator.boot_log);
  if (status_err(sts)) {
    LOG_ERROR("boot_log_print: %r", sts);
  }
  return status_ok(sts);
}
