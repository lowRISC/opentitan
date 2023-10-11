// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr.h"

#include <array>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.

namespace keymgr_unittest {
namespace {

struct SwBindingCfg {
  uint32_t max_key_ver;
  keymgr_binding_value_t binding_value_sealing;
  keymgr_binding_value_t binding_value_attestation;
};

class KeymgrTest : public rom_test::RomTest {
 protected:
  void ExpectStatusCheck(uint32_t op_status, uint32_t km_state,
                         uint32_t err_code) {
    EXPECT_ABS_READ32(base_ + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_OP_STATUS_REG_OFFSET, op_status);

    EXPECT_ABS_READ32(base_ + KEYMGR_ERR_CODE_REG_OFFSET, err_code);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_ERR_CODE_REG_OFFSET, err_code);

    EXPECT_SEC_READ32(base_ + KEYMGR_WORKING_STATE_REG_OFFSET, km_state);
  }
  void ExpectIdleCheck(uint32_t op_status) {
    EXPECT_ABS_READ32(base_ + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
  }
  void ExpectDiversificationWrite(keymgr_diversification_t diversification) {
    EXPECT_ABS_WRITE32(base_ + KEYMGR_KEY_VERSION_REG_OFFSET,
                       diversification.version);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_0_REG_OFFSET,
                       diversification.salt[0]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_1_REG_OFFSET,
                       diversification.salt[1]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_2_REG_OFFSET,
                       diversification.salt[2]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_3_REG_OFFSET,
                       diversification.salt[3]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_4_REG_OFFSET,
                       diversification.salt[4]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_5_REG_OFFSET,
                       diversification.salt[5]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_6_REG_OFFSET,
                       diversification.salt[6]);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_SALT_7_REG_OFFSET,
                       diversification.salt[7]);
  }
  void ExpectWaitUntilDone(size_t busy_cycles, uint32_t end_status) {
    for (size_t i = 0; i < busy_cycles; i++) {
      EXPECT_ABS_READ32(base_ + KEYMGR_OP_STATUS_REG_OFFSET,
                        KEYMGR_OP_STATUS_STATUS_VALUE_WIP);
      EXPECT_ABS_WRITE32(base_ + KEYMGR_OP_STATUS_REG_OFFSET,
                         KEYMGR_OP_STATUS_STATUS_VALUE_WIP);
    }
    EXPECT_ABS_READ32(base_ + KEYMGR_OP_STATUS_REG_OFFSET, end_status);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_OP_STATUS_REG_OFFSET, end_status);
  }
  uint32_t base_ = TOP_EARLGREY_KEYMGR_BASE_ADDR;
  SwBindingCfg cfg_ = {
      .max_key_ver = 0xA5A5A5A5,
      .binding_value_sealing = {0, 1, 2, 3, 4, 6, 7, 8},
      .binding_value_attestation = {9, 10, 11, 12, 13, 14, 15},
  };
  rom_test::MockAbsMmio mmio_;
  rom_test::MockSecMmio sec_mmio_;
};

TEST_F(KeymgrTest, EntropyReseedIntervalSet) {
  EXPECT_SEC_WRITE32_SHADOWED(
      base_ + KEYMGR_RESEED_INTERVAL_SHADOWED_REG_OFFSET, 0u);

  keymgr_entropy_reseed_interval_set(0u);
}

TEST_F(KeymgrTest, SwBindingValuesSet) {
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_0_REG_OFFSET,
                     cfg_.binding_value_sealing.data[0]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_1_REG_OFFSET,
                     cfg_.binding_value_sealing.data[1]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_2_REG_OFFSET,
                     cfg_.binding_value_sealing.data[2]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_3_REG_OFFSET,
                     cfg_.binding_value_sealing.data[3]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_4_REG_OFFSET,
                     cfg_.binding_value_sealing.data[4]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_5_REG_OFFSET,
                     cfg_.binding_value_sealing.data[5]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_6_REG_OFFSET,
                     cfg_.binding_value_sealing.data[6]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_SEALING_SW_BINDING_7_REG_OFFSET,
                     cfg_.binding_value_sealing.data[7]);

  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_0_REG_OFFSET,
                     cfg_.binding_value_attestation.data[0]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_1_REG_OFFSET,
                     cfg_.binding_value_attestation.data[1]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_2_REG_OFFSET,
                     cfg_.binding_value_attestation.data[2]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_3_REG_OFFSET,
                     cfg_.binding_value_attestation.data[3]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_4_REG_OFFSET,
                     cfg_.binding_value_attestation.data[4]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_5_REG_OFFSET,
                     cfg_.binding_value_attestation.data[5]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_6_REG_OFFSET,
                     cfg_.binding_value_attestation.data[6]);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_ATTEST_SW_BINDING_7_REG_OFFSET,
                     cfg_.binding_value_attestation.data[7]);

  EXPECT_SEC_WRITE32(base_ + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);
  keymgr_sw_binding_set(&cfg_.binding_value_sealing,
                        &cfg_.binding_value_attestation);
}

TEST_F(KeymgrTest, SwBindingUnlockWait) {
  EXPECT_ABS_READ32(base_ + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 1);
  EXPECT_SEC_READ32(base_ + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 1);
  keymgr_sw_binding_unlock_wait();
}

TEST_F(KeymgrTest, SetCreatorMaxVerKey) {
  EXPECT_SEC_WRITE32_SHADOWED(
      base_ + KEYMGR_MAX_CREATOR_KEY_VER_SHADOWED_REG_OFFSET, cfg_.max_key_ver);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET, 0);
  keymgr_creator_max_ver_set(cfg_.max_key_ver);
}

TEST_F(KeymgrTest, SetOwnerIntMaxVerKey) {
  EXPECT_SEC_WRITE32_SHADOWED(
      base_ + KEYMGR_MAX_OWNER_INT_KEY_VER_SHADOWED_REG_OFFSET,
      cfg_.max_key_ver);
  EXPECT_SEC_WRITE32(base_ + KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_REG_OFFSET, 0);
  keymgr_owner_int_max_ver_set(cfg_.max_key_ver);
}

TEST_F(KeymgrTest, AdvanceState) {
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + KEYMGR_CONTROL_SHADOWED_REG_OFFSET,
      {
          {KEYMGR_CONTROL_SHADOWED_DEST_SEL_OFFSET,
           KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE},
          {KEYMGR_CONTROL_SHADOWED_OPERATION_OFFSET,
           KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE},
      });
  EXPECT_ABS_WRITE32(base_ + KEYMGR_START_REG_OFFSET,
                     {
                         {KEYMGR_START_EN_BIT, true},
                     });
  keymgr_advance_state();
}

TEST_F(KeymgrTest, CheckState) {
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                    /*err_code=*/0u);
  EXPECT_EQ(keymgr_state_check(kKeymgrStateCreatorRootKey), kErrorOk);
}

TEST_F(KeymgrTest, CheckStateInvalidResponse) {
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_WORKING_STATE_STATE_VALUE_INVALID,
                    /*err_code=*/0u);
  EXPECT_EQ(keymgr_state_check(kKeymgrStateCreatorRootKey),
            kErrorKeymgrInternal);

  // Any non-idle status is expected to fail.
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR,
                    KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                    /*err_code=*/0u);
  EXPECT_EQ(keymgr_state_check(kKeymgrStateCreatorRootKey),
            kErrorKeymgrInternal);

  // Any non-zero error code is expected to fail.
  ExpectStatusCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY,
                    /*err_code=*/1u);
  EXPECT_EQ(keymgr_state_check(kKeymgrStateCreatorRootKey),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrTest, GenAttestationKey) {
  keymgr_diversification_t test_diversification = {
      .salt = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0xd0d1d2d3,
               0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf},
      .version = cfg_.max_key_ver - 1,
  };

  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + KEYMGR_CONTROL_SHADOWED_REG_OFFSET,
      {
          {KEYMGR_CONTROL_SHADOWED_DEST_SEL_OFFSET,
           KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN},
          {KEYMGR_CONTROL_SHADOWED_CDI_SEL_BIT, true},
          {KEYMGR_CONTROL_SHADOWED_OPERATION_OFFSET,
           KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT},
      });
  ExpectDiversificationWrite(test_diversification);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_START_REG_OFFSET,
                     {
                         {KEYMGR_START_EN_BIT, true},
                     });
  ExpectWaitUntilDone(/*busy_cycles=*/2,
                      KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(keymgr_generate_attestation_key_otbn(test_diversification),
            kErrorOk);
}

TEST_F(KeymgrTest, GenAttestationKeyNotIdle) {
  keymgr_diversification_t test_diversification = {
      .salt = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0xd0d1d2d3,
               0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf},
      .version = cfg_.max_key_ver - 1,
  };

  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_WIP);
  EXPECT_EQ(keymgr_generate_attestation_key_otbn(test_diversification),
            kErrorKeymgrInternal);
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_EQ(keymgr_generate_attestation_key_otbn(test_diversification),
            kErrorKeymgrInternal);
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  EXPECT_EQ(keymgr_generate_attestation_key_otbn(test_diversification),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrTest, GenAttestationKeyError) {
  keymgr_diversification_t test_diversification = {
      .salt = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0xd0d1d2d3,
               0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf},
      .version = cfg_.max_key_ver - 1,
  };
  uint32_t err_code = 0x1;

  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_ABS_WRITE32_SHADOWED(
      base_ + KEYMGR_CONTROL_SHADOWED_REG_OFFSET,
      {
          {KEYMGR_CONTROL_SHADOWED_DEST_SEL_OFFSET,
           KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN},
          {KEYMGR_CONTROL_SHADOWED_CDI_SEL_BIT, true},
          {KEYMGR_CONTROL_SHADOWED_OPERATION_OFFSET,
           KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT},
      });
  ExpectDiversificationWrite(test_diversification);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_START_REG_OFFSET,
                     {
                         {KEYMGR_START_EN_BIT, true},
                     });
  ExpectWaitUntilDone(/*busy_cycles=*/2,
                      KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_ABS_READ32(base_ + KEYMGR_ERR_CODE_REG_OFFSET, err_code);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_ERR_CODE_REG_OFFSET, err_code);

  EXPECT_EQ(keymgr_generate_attestation_key_otbn(test_diversification),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrTest, SideloadClearOtbn) {
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                     {
                         {KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET,
                          KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN},
                     });
  EXPECT_ABS_READ32(base_ + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                    {
                        {KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET,
                         KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN},
                    });
  EXPECT_ABS_WRITE32(base_ + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                     {
                         {KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET,
                          KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_NONE},
                     });

  EXPECT_EQ(keymgr_sideload_clear_otbn(), kErrorOk);
}

TEST_F(KeymgrTest, SideloadClearOtbnNotIdle) {
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_WIP);
  EXPECT_EQ(keymgr_sideload_clear_otbn(), kErrorKeymgrInternal);
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  EXPECT_EQ(keymgr_sideload_clear_otbn(), kErrorKeymgrInternal);
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  EXPECT_EQ(keymgr_sideload_clear_otbn(), kErrorKeymgrInternal);
}

TEST_F(KeymgrTest, SideloadClearOtbnReadbackMismatch) {
  ExpectIdleCheck(KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                     {
                         {KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET,
                          KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN},
                     });

  // Readback does not match the value written.
  EXPECT_ABS_READ32(base_ + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
                    {
                        {KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET,
                         KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_AES},
                    });

  EXPECT_EQ(keymgr_sideload_clear_otbn(), kErrorKeymgrInternal);
}

}  // namespace
}  // namespace keymgr_unittest
