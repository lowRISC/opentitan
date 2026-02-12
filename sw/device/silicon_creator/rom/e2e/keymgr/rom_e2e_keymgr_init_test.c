// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_keymgr_t keymgr;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;
static uint32_t otp_state[kHmacDigestNumWords + 4] = {0};

static void print_otp_sw_cfg_digests(void) {
  uint64_t creator_digest, owner_digest = 0;
  CHECK_DIF_OK(dif_otp_ctrl_get_digest(
      &otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg, &creator_digest));
  CHECK_DIF_OK(dif_otp_ctrl_get_digest(
      &otp_ctrl, kDifOtpCtrlPartitionOwnerSwCfg, &owner_digest));
  LOG_INFO("CreatorSwCfg Digest: 0x%08x%08x", (uint32_t)(creator_digest >> 32),
           (uint32_t)creator_digest);
  LOG_INFO("OwnerSwCfg Digest:   0x%08x%08x", (uint32_t)(owner_digest >> 32),
           (uint32_t)owner_digest);
}

bool test_main(void) {
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Lock OTP *SwCfg partitions if this is the first boot and reset.
  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    LOG_INFO("Power on reset. Locking OTP *SwCfg partitions ...");
    const uint64_t kFakeOtpDigest = 0xaaaabbbbccccdddd;
    CHECK_STATUS_OK(otp_ctrl_testutils_lock_partition(
        &otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg,
        /*digest=*/kFakeOtpDigest));
    CHECK_STATUS_OK(otp_ctrl_testutils_lock_partition(
        &otp_ctrl, kDifOtpCtrlPartitionOwnerSwCfg,
        /*digest=*/kFakeOtpDigest));
    rstmgr_testutils_reason_clear();
    LOG_INFO("Issuing a software reset ...");
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
  } else {
    print_otp_sw_cfg_digests();
    LOG_INFO("SW reset. Executing test ...");
  }

  CHECK_STATUS_OK(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateReset));

  dif_keymgr_binding_value_t bindings;
  CHECK_DIF_OK(dif_keymgr_read_binding(&keymgr, &bindings));

  const manifest_t *manifest = manifest_def_get();

  if (otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN_OFFSET) ==
      kHardenedBoolTrue) {
    LOG_INFO("ROM OTP measurement feature ENABLED.");
    // Check that the attestation is equal to the digest of concatenations of:
    //   - the digest of the CreatorSwCfg partition,
    //   - the digest of the OwnerSwCfg partition,
    //   - the SHA256 integrity hash of the first stage boot keys.
    CHECK_DIF_OK(dif_otp_ctrl_get_digest(
        &otp_ctrl, kDifOtpCtrlPartitionCreatorSwCfg, (uint64_t *)otp_state));
    CHECK_DIF_OK(dif_otp_ctrl_get_digest(
        &otp_ctrl, kDifOtpCtrlPartitionOwnerSwCfg, (uint64_t *)&otp_state[2]));
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32_array(
        &otp_ctrl, kDifOtpCtrlPartitionRotCreatorAuthCodesign,
        OTP_CTRL_PARAM_ROTCREATORAUTHCODESIGNBLOCKSHA2_256HASHOFFSET -
            OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_OFFSET,
        &otp_state[4], /*num_words=*/kHmacDigestNumWords));
    hmac_digest_t otp_measurement;
    hmac_sha256(otp_state, sizeof(otp_state), &otp_measurement);
    LOG_INFO("OTP CreatorSwCfg Digest: 0x%08x%08x", otp_state[1], otp_state[0]);
    LOG_INFO("OTP OwnerSwCfg Digest:   0x%08x%08x", otp_state[3], otp_state[2]);
    LOG_INFO("OTP Root Keys Digest:    0x%08x%08x%08x%08x%08x%08x%08x%08x",
             otp_state[11], otp_state[10], otp_state[9], otp_state[8],
             otp_state[7], otp_state[6], otp_state[5], otp_state[4]);
    CHECK_ARRAYS_EQ(bindings.attestation, otp_measurement.digest,
                    ARRAYSIZE(bindings.attestation));
  } else {
    LOG_INFO("ROM OTP measurement feature DISABLED.");
    // Check that the attestation is equal to `binding_value` field of the
    // manifest.
    CHECK_ARRAYS_EQ(bindings.attestation, manifest->binding_value.data,
                    ARRAYSIZE(bindings.attestation));
  }

  // Check that the sealing is equal to `binding_value` field of the
  // manifest.
  CHECK_ARRAYS_EQ(bindings.sealing, manifest->binding_value.data,
                  ARRAYSIZE(bindings.sealing));

  // Check that the creator max version is equal to `max_key_version` field of
  // the manifest.
  dif_keymgr_max_key_version_t versions;
  CHECK_DIF_OK(dif_keymgr_read_max_key_version(&keymgr, &versions));
  CHECK(versions.creator_max_key_version == manifest->max_key_version);
  return true;
}
