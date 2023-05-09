// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_flash_ctrl_state_t flash;

OTTF_DEFINE_TEST_CONFIG();

enum {
  kFlashInfoPageIdCreatorSecret = 1,
  kFlashInfoPageIdOwnerSecret = 2,
  kFlashInfoPageIdIsoPart = 3,
  kPartSize = 16,
  kBankId = 0,
  kPartitionId = 0,
};

// Random data to read/write to flash partitions.

const uint32_t kCreatorSecret[kPartSize] = {
    0xb295d21b, 0xecdfbdcd, 0x67e7ab2d, 0x6f660b08, 0x273bf65c, 0xe80f1695,
    0x586b80db, 0xc3dba27e, 0xdc124c5d, 0xb01ccd52, 0x815713e1, 0x31a141b2,
    0x2124be3b, 0x299a6f2a, 0x1f2a4741, 0x1a073cc0,
};

const uint32_t kOwnerSecret[kPartSize] = {
    0x69e705a0, 0x65c2ec6b, 0x04b0b634, 0x59313526, 0x1858aee1, 0xd49f3ba9,
    0x230bcd38, 0xc1eb6b3e, 0x68c15e3b, 0x024d02a9, 0x0b062ae4, 0x334dd155,
    0x53fdbf8a, 0x3792f1e2, 0xee317161, 0x33b19bf3,
};

const uint32_t kIsoPartData[kPartSize] = {
    0x2b78dbf5, 0x3e6e5a00, 0xbf82c6d5, 0x68d8e33f, 0x9c524bbc, 0xac5beeef,
    0x1287ca5a, 0x12b61419, 0x872e709f, 0xf91b7c0c, 0x18312a1f, 0x325cef9a,
    0x19fefa95, 0x4ceb421b, 0xa57d74c4, 0xaf1d723d,
};

// For Dev LC state before personalization the
// expected enabled values should be as follows :
// 0 - seed hw read = 0
// 1 - iso partition read = 0
// 2 - iso partition write = 1
// 3 - owner seed  = 1
// 4 - creator seed = 1
const bool kDevExpectedAccess[5] = {false, false, true, true, true};

// For Prod LC state (after personalization) the
// expected enabled values should be as follows :
// 0 - seed hw read = 1
// 1 - iso partition read = 1
// 2 - iso partition write = 1
// 3 - owner seed = 1
// 4 - creator seed = 0
const bool kProdExpectedAccess[5] = {true, true, true, true, false};

static bool access_partitions(bool do_write, bool do_read, uint32_t page_id,
                              const uint32_t *data, uint32_t size) {
  uint32_t address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash, page_id, kBankId, kPartitionId, &address));

  bool retval = true;

  if (do_write == true) {
    // Erase and write page.
    retval &= status_ok(flash_ctrl_testutils_erase_and_write_page(
        &flash, address, kPartitionId, data, kDifFlashCtrlPartitionTypeInfo,
        size));
  }

  if (do_read == true) {
    // Read page.
    uint32_t readback_data[size];
    retval &= status_ok(
        flash_ctrl_testutils_read(&flash, address, kPartitionId, readback_data,
                                  kDifFlashCtrlPartitionTypeInfo, size, 0));
    if (retval) {
      CHECK_ARRAYS_EQ(data, readback_data, size);
    }
  }
  return retval;
}

static bool keymgr_advance_state(dif_keymgr_t *keymgr,
                                 dif_keymgr_state_params_t *params,
                                 dif_keymgr_state_t expected_state) {
  CHECK_DIF_OK(dif_keymgr_advance_state(keymgr, params));
  dif_keymgr_status_codes_t keymgr_status_codes;
  do {
    CHECK_DIF_OK(dif_keymgr_get_status_codes(keymgr, &keymgr_status_codes));
  } while (!(keymgr_status_codes & kDifKeymgrStatusCodeIdle));

  dif_keymgr_state_t keymgr_state;
  CHECK_DIF_OK(dif_keymgr_get_state(keymgr, &keymgr_state));
  return (keymgr_state == expected_state);
}

bool test_main(void) {
  dif_otp_ctrl_t otp;
  dif_kmac_t kmac;
  dif_lc_ctrl_t lc;
  dif_keymgr_t keymgr;

  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc));
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));

  dif_keymgr_config_t keymgr_config = {.entropy_reseed_interval = 0xFFFF};
  CHECK_DIF_OK(dif_keymgr_configure(&keymgr, keymgr_config));

  dif_keymgr_state_params_t keymgr_params = {
      .binding_value = {0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF},
      .max_key_version = 0xFFFFFFFF};

  dif_kmac_config_t kmac_config = (dif_kmac_config_t){
      .sideload = true,
      .entropy_mode = kDifKmacEntropyModeSoftware,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, kmac_config));

  bool access_checks[5];

  access_checks[4] = access_partitions(
      true, true, kFlashInfoPageIdCreatorSecret, kCreatorSecret, kPartSize);
  access_checks[3] = access_partitions(true, true, kFlashInfoPageIdOwnerSecret,
                                       kOwnerSecret, kPartSize);
  access_checks[2] = access_partitions(true, false, kFlashInfoPageIdIsoPart,
                                       kIsoPartData, kPartSize);
  access_checks[1] = access_partitions(false, true, kFlashInfoPageIdIsoPart,
                                       kIsoPartData, kPartSize);
  access_checks[0] =
      keymgr_advance_state(&keymgr, NULL, kDifKeymgrStateInitialized);
  access_checks[0] &= keymgr_advance_state(&keymgr, &keymgr_params,
                                           kDifKeymgrStateCreatorRootKey);

  if (curr_state == kDifLcCtrlStateDev) {
    CHECK_ARRAYS_EQ(access_checks, kDevExpectedAccess,
                    ARRAYSIZE(access_checks));

    CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionSecret2, 0));
    dif_otp_ctrl_status_t otp_status;
    do {
      CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &otp_status));
    } while (
        !(bitfield_bit32_read(otp_status.codes, kDifOtpCtrlStatusCodeDaiIdle)));
  } else if (curr_state == kDifLcCtrlStateProd) {
    CHECK_ARRAYS_EQ(access_checks, kProdExpectedAccess,
                    ARRAYSIZE(access_checks));
  }

  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();

  return true;
}
