// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/cert/ram_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

// Define Test Scratchpad Layout in Owner Partition
typedef struct test_scratchpad {
  uint64_t saved_cdi0_id;
  uint64_t saved_cdi1_id;
  uint32_t magic;
} test_scratchpad_t;

enum {
  /* Values store to `test_scratchpad.magic` when the values are available. */
  kTestScratchPadOk = 0xa9e498cd,
};

OTTF_DEFINE_TEST_CONFIG();

static bool is_flash_page_empty(void) {
  uint32_t data[8];
  if (flash_ctrl_info_read(&kFlashCtrlInfoPageDiceCerts, 0,
                           sizeof(data) / sizeof(uint32_t), data) != kErrorOk) {
    LOG_ERROR("Failed to read flash info page");
    return false;
  }
  for (size_t i = 0; i < ARRAYSIZE(data); ++i) {
    if (data[i] != 0xFFFFFFFF) {
      return false;
    }
  }
  return true;
}

static status_t test_on_demand_refresh(void) {
  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;

  if (bitfield_bit32_read(retram->creator.reset_reasons,
                          kRstmgrReasonPowerOn)) {
    LOG_INFO("First boot (Cold): verifying certificates are NOT generated");

    // In On-Demand mode, flash page should be empty on first boot.
    TRY(is_flash_page_empty() ? OK_STATUS() : INTERNAL());

    // In Hybrid mode, msg type should be kDiceCertGenIds on cold boot.
    TRY(msg->hdr.type == kDiceCertGenIds ? OK_STATUS() : INTERNAL());

    uint64_t cdi0_id = read_64(msg->ids.mldsa_cdi0_id);
    uint64_t cdi1_id = read_64(msg->ids.mldsa_cdi1_id);

    LOG_INFO("CDI_0 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi0_id >> 32),
             (uint32_t)cdi0_id);
    LOG_INFO("CDI_1 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi1_id >> 32),
             (uint32_t)cdi1_id);

    // Save Key IDs to Retention SRAM Owner partition to verify constancy across
    // reset.
    test_scratchpad_t *scratch = (test_scratchpad_t *)retram->owner.reserved;
    scratch->saved_cdi0_id = cdi0_id;
    scratch->saved_cdi1_id = cdi1_id;
    scratch->magic = kTestScratchPadOk;

    LOG_INFO(
        "Saved Key IDs to scratchpad. Requesting cert generation and "
        "rebooting...");
    msg->hdr.type = kDiceCertGenRequest;
    msg->hdr.version = 0;
    rstmgr_reset();
    return INTERNAL();  // Should not reach here.
  }

  LOG_INFO("Second boot (Warm): verifying certificates ARE generated");

  // Flash page should NOT be empty now.
  TRY(!is_flash_page_empty() ? OK_STATUS() : INTERNAL());

  // Verify msg type is kDiceCertGenResponse.
  TRY(msg->hdr.type == kDiceCertGenResponse ? OK_STATUS() : INTERNAL());

  dice_cert_gen_res_t *res = &msg->res;

  // Verify CRC32.
  uint32_t expected_crc = res->crc32;
  uint32_t calculated_crc =
      crc32(res, sizeof(dice_cert_gen_res_t) - sizeof(uint32_t));
  if (calculated_crc != expected_crc) {
    LOG_ERROR("Handover CRC32 mismatch! Expected 0x%08x, got 0x%08x",
              expected_crc, calculated_crc);
    return INTERNAL();
  }
  LOG_INFO("Handover CRC32 verified successfully: 0x%08x", calculated_crc);

  uint64_t cdi0_id = read_64(res->mldsa_cdi0_id);
  uint64_t cdi1_id = read_64(res->mldsa_cdi1_id);

  LOG_INFO("CDI_0 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi0_id >> 32),
           (uint32_t)cdi0_id);
  LOG_INFO("CDI_1 ML-DSA Key ID: 0x%08x%08x", (uint32_t)(cdi1_id >> 32),
           (uint32_t)cdi1_id);

  // Verify Key IDs match saved ones from the cold boot.
  test_scratchpad_t *scratch = (test_scratchpad_t *)retram->owner.reserved;
  if (scratch->magic != kTestScratchPadOk) {
    LOG_ERROR("No saved Key IDs found in scratchpad (magic mismatch: 0x%08x)!",
              scratch->magic);
    return INTERNAL();
  }

  if (scratch->saved_cdi0_id != cdi0_id || scratch->saved_cdi1_id != cdi1_id) {
    LOG_ERROR(
        "Key ID mismatch across reboot! Saved CDI0: 0x%08x%08x, Got: "
        "0x%08x%08x",
        (uint32_t)(scratch->saved_cdi0_id >> 32),
        (uint32_t)scratch->saved_cdi0_id, (uint32_t)(cdi0_id >> 32),
        (uint32_t)cdi0_id);
    LOG_ERROR("Saved CDI1: 0x%08x%08x, Got: 0x%08x%08x",
              (uint32_t)(scratch->saved_cdi1_id >> 32),
              (uint32_t)scratch->saved_cdi1_id, (uint32_t)(cdi1_id >> 32),
              (uint32_t)cdi1_id);
    return INTERNAL();
  }
  LOG_INFO("Key IDs match successfully across reboot!");

  // Clear the request and magic.
  msg->hdr.type = 0;
  scratch->magic = 0;

  LOG_INFO("Certificates successfully generated on demand!");

  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_on_demand_refresh();
  if (status_err(sts)) {
    LOG_ERROR("test_on_demand_refresh: %r", sts);
  }
  return status_ok(sts);
}
