// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_keymgr_dpe_t keymgr_dpe;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * Keymgr dpe constant
 */
// TODO(#30777): Replace the hard-coded slot number
// Slot Number must match with the ones defined in dice_chain.c!
// Pre-defined slot id for the attestation / sealing key chain
const uint32_t kKeymgrDPESealSlot = 0;
const uint32_t kKeymgrDPEAttestSlot = 1;

static void print_otp_sw_cfg_digests(void) {
  uint64_t creator_digest = 0, owner_digest = 0;
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
  CHECK_DIF_OK(dif_keymgr_dpe_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR), &keymgr_dpe));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_BASE_ADDR), &rstmgr));

  LOG_INFO("Reset info: 0x%08x", rstmgr_testutils_reason_get());

  // Lock OTP *SwCfg partitions if this is the first boot and reset.
  // Note: the POR bit must be tested in isolation rather than compared against
  // the whole RESET_INFO value: in chip-level DV the reset reason reads back as
  // `kDifRstmgrResetInfoPor | kDifRstmgrResetInfoWatchdog` (0x11).
  if (UNWRAP(
          rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoPor))) {
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

  // TODO(#30830): Gracefully handle what happens if the keymgr_dpe is not
  // enabled by the lc controller.

  // TODO(#30811): Integrate DISABLE_KEYMGR_DPE field in this test

  // The ROM derives the sealing and attestation CreatorRootKeys itself (in
  // slots `kKeymgrDPESealSlot`/`kKeymgrDPEAttestSlot`) and advances keymgr_dpe
  // to `Available` before jumping to ROM_EXT.
  LOG_INFO("Keymgr dpe: Check available state");
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));

  // TODO(#30759): Verify the kKeymgrDPESealSlot / kKeymgrDPEAttestSlot hold
  // keys with boot stage set to BootStageOwnerInt (1). (Note: Current bootstage
  // + 1)

  const manifest_t *manifest = manifest_def_get();

  if (otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN_OFFSET) ==
      kHardenedBoolTrue) {
    LOG_INFO("ROM OTP measurement feature ENABLED.");
  } else {
    LOG_INFO("ROM OTP measurement feature DISABLED.");
  }

  // Generation parameters used to derive a SW key from a CreatorRootKey slot.
  // The same salt/version is used for both slots so that any difference in the
  // generated output can only come from the slots' distinct DPE contexts.
  dif_keymgr_dpe_generate_params_t gen_param = {
      .key_dest = kDifKeymgrDpeKeyDestNone,
      .sideload_key = false,
      .salt = {0xb6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf, 0x9f89bc56,
               0x4bd127c7, 0x322288d8, 0xde919d54},
      .version = manifest->max_key_version,
      .slot_src_sel = 0,  // Overridden per call below.
  };

  dif_keymgr_dpe_output_t sealing_key;
  dif_keymgr_dpe_output_t attestation_key;

  gen_param.slot_src_sel = kKeymgrDPESealSlot;
  CHECK_STATUS_OK(keymgr_dpe_testutils_generate_key(&keymgr_dpe, &gen_param));
  CHECK_DIF_OK(dif_keymgr_dpe_read_output(&keymgr_dpe, &sealing_key));

  gen_param.slot_src_sel = kKeymgrDPEAttestSlot;
  CHECK_STATUS_OK(keymgr_dpe_testutils_generate_key(&keymgr_dpe, &gen_param));
  CHECK_DIF_OK(dif_keymgr_dpe_read_output(&keymgr_dpe, &attestation_key));

  // Check if both key matches
  bool matching_key = true;
  for (size_t i = 0; i < ARRAYSIZE(sealing_key.value[0]); ++i) {
    if ((sealing_key.value[0][i] ^ sealing_key.value[1][i]) !=
        (attestation_key.value[0][i] ^ attestation_key.value[1][i])) {
      matching_key = false;
      break;
    }
  }

  // If the OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN_OFFSET is true
  // then the sealing binding value is provided separately, otherwise the
  // attestation binding value is reused for the sealing binding value.
  if (otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN_OFFSET) ==
      kHardenedBoolTrue) {
    CHECK(!matching_key,
          "Sealing and attestation CreatorRootKeys produced matching keys.");
  } else {
    CHECK(matching_key,
          "Sealing and attestation CreatorRootKeys should produce matching "
          "keys.");
  }

  // TODO(#30878): Improve this test

  return true;
}
