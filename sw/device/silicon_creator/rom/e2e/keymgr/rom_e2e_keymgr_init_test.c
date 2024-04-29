// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated

OTTF_DEFINE_TEST_CONFIG();

static uint32_t otp_state[kHmacDigestNumWords + 4] = {0};

bool test_main(void) {
  dif_keymgr_t keymgr;
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));

  CHECK_STATUS_OK(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateReset));

  dif_keymgr_binding_value_t bindings;
  CHECK_DIF_OK(dif_keymgr_read_binding(&keymgr, &bindings));

  const manifest_t *manifest = manifest_def_get();

  if (otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN_OFFSET) ==
      kHardenedBoolTrue) {
    // Check that the attestation is equal to the digest of concatenations of:
    //   - the digest of the CreatorSwCfg partition,
    //   - the digest of the OwnerSwCfg partition,
    //   - the SHA256 integrity hash of the first stage boot keys.
    otp_dai_read(kOtpPartitionCreatorSwCfg,
                 /*relative_address=*/
                 kOtpPartitions[kOtpPartitionCreatorSwCfg].digest_addr -
                     OTP_CTRL_PARAM_CREATOR_SW_CFG_OFFSET,
                 otp_state,
                 /*num_words=*/2);
    otp_dai_read(kOtpPartitionOwnerSwCfg,
                 /*relative_address=*/
                 kOtpPartitions[kOtpPartitionOwnerSwCfg].digest_addr -
                     OTP_CTRL_PARAM_OWNER_SW_CFG_OFFSET,
                 &otp_state[2],
                 /*num_words=*/2);
    otp_dai_read(kOtpPartitionRotCreatorAuthCodesign,
                 /*relative_address=*/
                 OTP_CTRL_PARAM_ROTCREATORAUTHCODESIGNBLOCKSHA2_256HASHOFFSET -
                     OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_OFFSET,
                 &otp_state[4],
                 /*num_words=*/kHmacDigestNumWords);
    hmac_digest_t otp_measurement;
    hmac_sha256(otp_state, (kHmacDigestNumWords + 4) * sizeof(uint32_t),
                &otp_measurement);
    CHECK_ARRAYS_EQ(bindings.attestation, otp_measurement.digest,
                    ARRAYSIZE(bindings.attestation));
  } else {
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
