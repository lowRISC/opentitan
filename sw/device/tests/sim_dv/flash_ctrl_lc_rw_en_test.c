// Copyright lowRISC contributors (OpenTitan project).
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
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_lc_ctrl_t lc;
static dif_otp_ctrl_t otp;

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

typedef enum check_id {
  // Unprovisioned state checks.
  kCheckIdUnprovisionedCreatorSeed = 0,
  kCheckIdUnprovisonedOwnerSeed,
  kCheckIdLcDevIsoPartAccess,

  // Provisioned state checks.
  kCheckIdProvisionedCreatorSeed,
  kCheckIdProvisionedOwnerSeed,
  kCheckIdLcProdIsoPartAccess,
} check_id_t;

typedef struct partition_check_cfg {
  // Test identifier.
  check_id_t check_id;

  // Page ID of the partition to check.
  uint32_t page_id;

  // Data to write to the partition.
  const uint32_t *data;

  // Size of the data to write.
  uint32_t size;

  // Whether to write to the partition.
  bool do_write;

  // Whether to expect the read operation to succeed.
  bool expect_read_ok;

  // Whether to read from the partition.
  bool do_read;

  // Whether to expect the write operation to succeed.
  bool expect_write_ok;
} partition_check_cfg_t;

static const partition_check_cfg_t kTest[] = {
    [kCheckIdUnprovisionedCreatorSeed] =
        {
            .check_id = kCheckIdUnprovisionedCreatorSeed,
            .page_id = kFlashInfoPageIdCreatorSecret,
            .data = kCreatorSecret,
            .size = kPartSize,
            .do_write = true,
            .expect_write_ok = true,
            .do_read = true,
            .expect_read_ok = true,
        },
    [kCheckIdUnprovisonedOwnerSeed] =
        {
            .check_id = kCheckIdUnprovisonedOwnerSeed,
            .page_id = kFlashInfoPageIdOwnerSecret,
            .data = kOwnerSecret,
            .size = kPartSize,
            .do_write = true,
            .expect_write_ok = true,
            .do_read = true,
            .expect_read_ok = true,
        },
    [kCheckIdLcDevIsoPartAccess] =
        {
            .check_id = kCheckIdLcDevIsoPartAccess,
            .page_id = kFlashInfoPageIdIsoPart,
            .data = kIsoPartData,
            .size = kPartSize,
            .do_write = true,
            .expect_write_ok = true,
            .do_read = true,
            .expect_read_ok = false,
        },
    [kCheckIdProvisionedCreatorSeed] =
        {
            .check_id = kCheckIdProvisionedCreatorSeed,
            .page_id = kFlashInfoPageIdCreatorSecret,
            .data = kCreatorSecret,
            .size = kPartSize,
            .do_write = true,
            .expect_write_ok = false,
            .do_read = false,
            .expect_read_ok = false,
        },
    [kCheckIdProvisionedOwnerSeed] =
        {
            .check_id = kCheckIdProvisionedOwnerSeed,
            .page_id = kFlashInfoPageIdOwnerSecret,
            .data = kOwnerSecret,
            .size = kPartSize,
            .do_write = true,
            .expect_write_ok = true,
            .do_read = true,
            .expect_read_ok = true,
        },
    [kCheckIdLcProdIsoPartAccess] =
        {
            .check_id = kCheckIdLcProdIsoPartAccess,
            .page_id = kFlashInfoPageIdIsoPart,
            .data = kIsoPartData,
            .size = kPartSize,
            .do_write = false,
            .expect_write_ok = false,
            .do_read = true,
            .expect_read_ok = true,
        },
};

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles(void) {
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc));
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
}

static void partition_check(const partition_check_cfg_t cfg) {
  uint32_t address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash, cfg.page_id, kBankId, kPartitionId, &address));

  if (cfg.do_write) {
    status_t result = flash_ctrl_testutils_erase_and_write_page(
        &flash, address, kPartitionId, cfg.data, kDifFlashCtrlPartitionTypeInfo,
        cfg.size);

    if (cfg.expect_write_ok) {
      CHECK_STATUS_OK(result);
    } else {
      CHECK_STATUS_NOT_OK(result);
    }
  }

  if (cfg.do_read) {
    uint32_t readback_data[cfg.size];
    status_t result =
        flash_ctrl_testutils_read(&flash, address, kPartitionId, readback_data,
                                  kDifFlashCtrlPartitionTypeInfo, cfg.size, 0);

    if (cfg.expect_read_ok) {
      CHECK_STATUS_OK(result);
      CHECK_ARRAYS_EQ(cfg.data, readback_data, cfg.size);
    } else {
      CHECK_STATUS_NOT_OK(result);
      CHECK_ARRAYS_NE(cfg.data, readback_data, cfg.size);
    }
  }
}

// Advance the keymgr state to the expected state.
static void keymgr_advance_state(dif_keymgr_t *keymgr,
                                 dif_keymgr_state_params_t *params,
                                 dif_keymgr_state_t expected_state) {
  CHECK_DIF_OK(dif_keymgr_advance_state(keymgr, params));
  dif_keymgr_status_codes_t keymgr_status_codes;
  do {
    CHECK_DIF_OK(dif_keymgr_get_status_codes(keymgr, &keymgr_status_codes));
  } while (!(keymgr_status_codes & kDifKeymgrStatusCodeIdle));

  dif_keymgr_state_t keymgr_state;
  CHECK_DIF_OK(dif_keymgr_get_state(keymgr, &keymgr_state));
  LOG_INFO("Keymgr state: 0x%x", keymgr_state);
  CHECK(keymgr_state == expected_state,
        "Expected keymgr state not reached. got: %d, expected: %d",
        keymgr_state, expected_state);
}

// Provision the creator secrets in the OTP. This signals the DUT that the
// creator secrets are provisioned and the DUT will not allow further writes to
// the creator secrets.
static void dut_provision_creator_secrets(void) {
  CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionSecret2, 0));
  dif_otp_ctrl_status_t otp_status;
  do {
    CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &otp_status));
  } while (
      !(bitfield_bit32_read(otp_status.codes, kDifOtpCtrlStatusCodeDaiIdle)));
}

bool test_main(void) {
  init_peripheral_handles();

  CHECK_DIF_OK(
      dif_keymgr_configure(&keymgr, (dif_keymgr_config_t){
                                        .entropy_reseed_interval = 0xFFFF,
                                    }));

  CHECK_DIF_OK(
      dif_kmac_configure(&kmac, (dif_kmac_config_t){
                                    .sideload = true,
                                    .entropy_mode = kDifKmacEntropyModeSoftware,
                                }));

  // chip_sw_flash_ctrl_lc_rw_en_vseq steps through DEV and PROD LC states.
  // DEV LC state:
  //  - Initial state: Unprovisioned.
  //  - Final state: Provisioned.
  // PROD LC state:
  //  - Initial state: Provisioned.
  //
  // Even though the DUT does not support transitions from DEV to PROD, the
  // test does this to check the expected behavior of the Isolation Partition.
  // In practice, the DUT will go from TEST_UNLOCKED to either DEV or PROD.
  dif_lc_ctrl_state_t curr_state;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &curr_state));
  if (curr_state == kDifLcCtrlStateDev) {
    partition_check(kTest[kCheckIdUnprovisionedCreatorSeed]);
    partition_check(kTest[kCheckIdUnprovisonedOwnerSeed]);
    partition_check(kTest[kCheckIdLcDevIsoPartAccess]);

    // The DUT has not been personalized, so we expect this to fail.
    keymgr_advance_state(&keymgr, NULL, kDifKeymgrStateInvalid);
    dut_provision_creator_secrets();
  } else if (curr_state == kDifLcCtrlStateProd) {
    partition_check(kTest[kCheckIdProvisionedCreatorSeed]);
    partition_check(kTest[kCheckIdProvisionedOwnerSeed]);
    partition_check(kTest[kCheckIdLcProdIsoPartAccess]);
    keymgr_advance_state(&keymgr, NULL, kDifKeymgrStateInitialized);

    dif_keymgr_state_params_t params = {
        .binding_value = {0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF},
        .max_key_version = 0xFFFFFFFF};
    keymgr_advance_state(&keymgr, &params, kDifKeymgrStateCreatorRootKey);
  }

  test_status_set(kTestStatusInWfi);
  wait_for_interrupt();

  return true;
}
