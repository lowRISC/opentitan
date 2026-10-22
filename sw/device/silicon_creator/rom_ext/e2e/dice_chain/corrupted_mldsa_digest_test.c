// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/cert/ram_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

typedef struct test_scratchpad {
  uint64_t saved_cdi0_id;
  uint64_t saved_cdi1_id;
} test_scratchpad_t;

static status_t test_corrupted_mldsa_digest(void) {
  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;
  test_scratchpad_t *scratch = (test_scratchpad_t *)retram->owner.reserved;
  dice_storage_slot_v1_t cdi1_slot = {.bank_idx = 1};

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    LOG_INFO("Phase 1 (Cold boot): Verifying initial certificates are valid");
    TRY(msg->hdr.type == kDiceCertGenResponse ? OK_STATUS() : INTERNAL());

    dice_cert_gen_res_t *res = &msg->res;
    TRY(res->mldsa_cdi0_cert_len != 0 ? OK_STATUS() : INTERNAL());
    TRY(res->mldsa_cdi1_cert_len != 0 ? OK_STATUS() : INTERNAL());

    scratch->saved_cdi0_id = read_64(res->mldsa_cdi0_id);
    scratch->saved_cdi1_id = read_64(res->mldsa_cdi1_id);

    // Corrupt the CDI_1 data flash slot.
    uint32_t flash_offset = dice_storage_slot_v1_offset(&cdi1_slot);
    LOG_INFO("Corrupting CDI_1 data flash slot at 0x%08x", flash_offset);
    rom_error_t err =
        flash_ctrl_data_erase(flash_offset, kFlashCtrlEraseTypePage);
    if (err != kErrorOk) {
      LOG_ERROR("flash_ctrl_data_erase failed: 0x%08x", err);
      return INTERNAL();
    }
    uint32_t garbage[4] = {0xdeadbeef, 0xbaadf00d, 0x12345678, 0x87654321};
    err = flash_ctrl_data_write(flash_offset, ARRAYSIZE(garbage), garbage);
    if (err != kErrorOk) {
      LOG_ERROR("flash_ctrl_data_write failed: 0x%08x", err);
      return INTERNAL();
    }

    LOG_INFO("Resetting system to trigger ROM_EXT corruption detection...");
    rstmgr_reset();
    return INTERNAL();  // Should not reach here.
  }

  LOG_INFO("Phase 2 (Post-recovery): Verifying auto-regeneration");
  TRY(msg->hdr.type == kDiceCertGenResponse ? OK_STATUS() : INTERNAL());

  dice_cert_gen_res_t *res = &msg->res;
  TRY(res->mldsa_cdi0_cert_len != 0 ? OK_STATUS() : INTERNAL());
  TRY(res->mldsa_cdi1_cert_len != 0 ? OK_STATUS() : INTERNAL());

  uint64_t cdi0_id = read_64(res->mldsa_cdi0_id);
  uint64_t cdi1_id = read_64(res->mldsa_cdi1_id);
  CHECK(cdi0_id == scratch->saved_cdi0_id,
        "CDI_0 ID mismatch: 0x%08x%08x != 0x%08x%08x",
        (uint32_t)(cdi0_id >> 32), (uint32_t)cdi0_id,
        (uint32_t)(scratch->saved_cdi0_id >> 32),
        (uint32_t)scratch->saved_cdi0_id);
  CHECK(cdi1_id == scratch->saved_cdi1_id,
        "CDI_1 ID mismatch: 0x%08x%08x != 0x%08x%08x",
        (uint32_t)(cdi1_id >> 32), (uint32_t)cdi1_id,
        (uint32_t)(scratch->saved_cdi1_id >> 32),
        (uint32_t)scratch->saved_cdi1_id);

  // Verify that the CDI_1 data flash slot was rewritten with a valid TLV cert.
  perso_tlv_cert_obj_view_t cdi1_obj = {0};
  uint8_t *slot1_hdr = (uint8_t *)dice_storage_slot_v1_header(&cdi1_slot);
  size_t slot_max_len =
      (uintptr_t)_rom_ext_size - (uintptr_t)_rom_ext_protected_size;
  rom_error_t err =
      perso_tlv_get_cert_obj_view(slot1_hdr, slot_max_len, &cdi1_obj);
  if (err != kErrorOk) {
    LOG_ERROR("Failed to parse restored CDI_1 TLV from flash: 0x%08x", err);
    return INTERNAL();
  }
  CHECK(cdi1_obj.obj_type == kPersoObjectTypeX509Cert);
  CHECK(cdi1_obj.cert_body_p == (uint8_t *)res->mldsa_cdi1_cert);
  CHECK(cdi1_obj.cert_body_size == res->mldsa_cdi1_cert_len);

  LOG_INFO("Corrupted ML-DSA digest test passed!");
  return OK_STATUS();
}

bool test_main(void) {
  ottf_alerts_ignore_alert(kTopEarlgreyAlertIdFlashCtrlRecovErr);
  status_t sts = test_corrupted_mldsa_digest();
  if (status_err(sts)) {
    LOG_ERROR("test_corrupted_mldsa_digest: %r", sts);
  }
  return status_ok(sts);
}
