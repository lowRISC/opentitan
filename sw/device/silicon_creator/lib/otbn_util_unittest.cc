// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/otbn_util.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

namespace otbn_util_unittest {
namespace {

using ::testing::ElementsAre;
using ::testing::Return;

TEST(OtbnTest, OtbnInit) {
  otbn_t otbn;
  otbn_init(&otbn);
  EXPECT_EQ(otbn.app_is_loaded, kHardenedBoolFalse);
  EXPECT_EQ(otbn.error_bits, kOtbnErrBitsNoError);
}

class OtbnTest : public rom_test::RomTest {
 protected:
  /**
   * Sets expectations for running an OTBN command.
   *
   * @param cmd      Command expected to be run.
   * @param err_bits Error bits to be returned.
   * @param status   Status of OTBN to be returned after the command is done.
   */
  void ExpectCmdRun(otbn_cmd_t cmd, otbn_err_bits_t err_bits,
                    otbn_status_t status) {
    EXPECT_ABS_WRITE32(base_ + OTBN_INTR_STATE_REG_OFFSET,
                       {
                           {OTBN_INTR_COMMON_DONE_BIT, 1},
                       });
    EXPECT_ABS_WRITE32(base_ + OTBN_CMD_REG_OFFSET, cmd);

    EXPECT_ABS_READ32(base_ + OTBN_INTR_STATE_REG_OFFSET, 0);
    EXPECT_ABS_READ32(base_ + OTBN_INTR_STATE_REG_OFFSET,
                      {
                          {OTBN_INTR_COMMON_DONE_BIT, 1},
                      });
    EXPECT_ABS_WRITE32(base_ + OTBN_INTR_STATE_REG_OFFSET,
                       {
                           {OTBN_INTR_COMMON_DONE_BIT, 1},
                       });

    EXPECT_ABS_READ32(base_ + OTBN_ERR_BITS_REG_OFFSET, err_bits);
    EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, status);

    if (err_bits == kOtbnErrBitsNoError && status == kOtbnStatusIdle) {
      EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, status);
    }
  }

  uint32_t base_ = TOP_EARLGREY_OTBN_BASE_ADDR;
  rom_test::MockAbsMmio abs_mmio_;
  rom_test::MockRnd rnd_;
  rom_test::MockSecMmio sec_mmio_;
};

class OtbnAppTest : public OtbnTest {};

TEST_F(OtbnAppTest, OtbnLoadAppSuccess) {
  std::array<uint32_t, 2> imem_data = {0x01234567, 0x89abcdef};
  std::array<uint32_t, 2> dmem_data = {0x456789ab, 0xcdef0123};
  otbn_app_t app = {
      .imem_start = imem_data.data(),
      .imem_end = imem_data.data() + imem_data.size(),
      .dmem_data_start = dmem_data.data(),
      .dmem_data_end = dmem_data.data() + imem_data.size(),
  };

  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= sizeof(uint32_t) * dmem_data.size(),
                "OTBN DMEM size too small");
  static_assert(OTBN_IMEM_SIZE_BYTES >= sizeof(uint32_t) * imem_data.size(),
                "OTBN IMEM size too small");

  // `otbn_busy_wait_for_done` - begin with busy to ensure we wait until idle.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusySecWipeDmem);
  // Read twice for hardening.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  // `otbn_imem_sec_wipe`
  ExpectCmdRun(kOtbnCmdSecWipeImem, kOtbnErrBitsNoError, kOtbnStatusIdle);
  // `otbn_imem_write`
  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET, imem_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + sizeof(uint32_t),
                     imem_data[1]);
  // `otbn_dmem_sec_wipe`
  ExpectCmdRun(kOtbnCmdSecWipeDmem, kOtbnErrBitsNoError, kOtbnStatusIdle);
  // `otbn_dmem_write`
  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET, dmem_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + sizeof(uint32_t),
                     dmem_data[1]);

  otbn_t otbn;
  otbn_init(&otbn);

  EXPECT_EQ(otbn_load_app(&otbn, app), kErrorOk);
}

TEST_F(OtbnAppTest, OtbnLoadInvalidApp) {
  // Create an invalid app with an empty IMEM range.
  std::array<uint32_t, 0> imem_data = {};
  std::array<uint32_t, 2> dmem_data = {0x456789ab, 0xcdef0123};
  otbn_app_t app = {
      .imem_start = imem_data.data(),
      .imem_end = imem_data.data() + imem_data.size(),
      .dmem_data_start = dmem_data.data(),
      .dmem_data_end = dmem_data.data() + dmem_data.size(),
  };

  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= sizeof(uint32_t) * dmem_data.size(),
                "OTBN DMEM size too small");
  static_assert(OTBN_IMEM_SIZE_BYTES >= sizeof(uint32_t) * imem_data.size(),
                "OTBN IMEM size too small");

  otbn_t otbn;
  otbn_init(&otbn);

  EXPECT_EQ(otbn_load_app(&otbn, app), kErrorOtbnInvalidArgument);
}

TEST_F(OtbnAppTest, OtbnExecuteApp) {
  EXPECT_SEC_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x01);
  ExpectCmdRun(kOtbnCmdExecute, kOtbnErrBitsNoError, kOtbnStatusIdle);

  otbn_t otbn;
  otbn_init(&otbn);
  // Pretend an app has already been loaded.
  otbn.app_is_loaded = kHardenedBoolTrue;

  EXPECT_EQ(otbn_execute_app(&otbn), kErrorOk);
}

TEST_F(OtbnAppTest, OtbnExecuteBusy) {
  EXPECT_SEC_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x01);
  ExpectCmdRun(kOtbnCmdExecute, kOtbnErrBitsNoError, kOtbnStatusBusyExecute);

  otbn_t otbn;
  otbn_init(&otbn);
  // Pretend an app has already been loaded.
  otbn.app_is_loaded = kHardenedBoolTrue;

  EXPECT_EQ(otbn_execute_app(&otbn), kErrorOtbnExecutionFailed);
}

TEST_F(OtbnAppTest, OtbnExecuteNotLoaded) {
  otbn_t otbn;
  otbn_init(&otbn);

  // No app has been loaded yet.
  EXPECT_EQ(otbn_execute_app(&otbn), kErrorOtbnInvalidArgument);
}

class OtbnWriteTest : public OtbnTest {};

TEST_F(OtbnWriteTest, Success) {
  constexpr uint32_t kDestAddr = 6;
  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  // Test assumption.
  static_assert(
      OTBN_DMEM_SIZE_BYTES >= sizeof(uint32_t) * test_data.size() + kDestAddr,
      "OTBN DMEM size too small.");

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + kDestAddr, test_data[0]);
  EXPECT_ABS_WRITE32(
      base_ + OTBN_DMEM_REG_OFFSET + kDestAddr + sizeof(uint32_t),
      test_data[1]);

  otbn_t otbn;
  otbn_init(&otbn);

  EXPECT_EQ(otbn_copy_data_to_otbn(&otbn, 2, test_data.data(), kDestAddr),
            kErrorOk);
}

class OtbnReadTest : public OtbnTest {};

TEST_F(OtbnReadTest, Success) {
  constexpr uint32_t kSrcAddr = 6;
  std::array<uint32_t, 2> test_data = {0};

  // Test assumption.
  static_assert(
      OTBN_DMEM_SIZE_BYTES >= sizeof(uint32_t) * test_data.size() + kSrcAddr,
      "OTBN DMEM size too small.");

  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + kSrcAddr, 0x12345678);
  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + kSrcAddr + sizeof(uint32_t),
                    0xabcdef01);

  otbn_t otbn;
  otbn_init(&otbn);

  EXPECT_EQ(otbn_copy_data_from_otbn(&otbn, 2, kSrcAddr, test_data.data()),
            kErrorOk);
  EXPECT_THAT(test_data, ElementsAre(0x12345678, 0xabcdef01));
}

}  // namespace
}  // namespace otbn_util_unittest
