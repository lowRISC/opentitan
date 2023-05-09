// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include <array>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

namespace otbn_unittest {
namespace {
using ::testing::ElementsAre;
using ::testing::Return;

class OtbnTest : public rom_test::RomTest {
 protected:
  /**
   * Sets expectations for running an OTBN command.
   *
   * @param cmd      Command expected to be run.
   * @param err_bits Error bits to be returned.
   * @param status   Status of OTBN to be returned after the command is done.
   */
  void ExpectCmdRun(otbn_cmd_t cmd, uint32_t err_bits, otbn_status_t status) {
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

    if (err_bits == err_bits_ok_ && status == kOtbnStatusIdle) {
      EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, status);
    }
  }

  uint32_t base_ = TOP_EARLGREY_OTBN_BASE_ADDR;
  uint32_t err_bits_ok_ = 0;
  rom_test::MockAbsMmio abs_mmio_;
  rom_test::MockRnd rnd_;
  rom_test::MockSecMmio sec_mmio_;
};

class ExecuteTest : public OtbnTest {};

TEST_F(ExecuteTest, ExecuteSuccess) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 8, "OTBN IMEM size too small.");

  // Read twice for hardening.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);

  EXPECT_SEC_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x1);

  ExpectCmdRun(kOtbnCmdExecute, err_bits_ok_, kOtbnStatusIdle);

  EXPECT_EQ(otbn_execute(), kErrorOk);
}

TEST_F(ExecuteTest, ExecuteError) {
  // Read twice for hardening.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);

  EXPECT_SEC_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x1);

  // Nonzero error bits.
  ExpectCmdRun(kOtbnCmdExecute, 1 << OTBN_ERR_BITS_FATAL_SOFTWARE_BIT,
               kOtbnStatusIdle);

  EXPECT_EQ(otbn_execute(), kErrorOtbnExecutionFailed);
}

TEST_F(ExecuteTest, ExecuteBusy) {
  // Read twice for hardening.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);

  EXPECT_SEC_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x01);

  // Return a busy status after the `done` interrupt.
  ExpectCmdRun(kOtbnCmdExecute, err_bits_ok_, kOtbnStatusBusyExecute);

  EXPECT_EQ(otbn_execute(), kErrorOtbnExecutionFailed);
}

TEST_F(ExecuteTest, ExecuteBlockUntilIdle) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 8, "OTBN IMEM size too small.");

  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusySecWipeDmem);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusySecWipeDmem);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusySecWipeDmem);

  // Read twice for hardening.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);

  EXPECT_SEC_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x1);

  ExpectCmdRun(kOtbnCmdExecute, err_bits_ok_, kOtbnStatusIdle);

  EXPECT_EQ(otbn_execute(), kErrorOk);
}

class IsBusyTest : public OtbnTest {};

TEST_F(IsBusyTest, Success) {
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);

  EXPECT_EQ(otbn_busy_wait_for_done(), kErrorOk);
}

class ImemSecWipeTest : public OtbnTest {};

TEST_F(ImemSecWipeTest, Success) {
  ExpectCmdRun(kOtbnCmdSecWipeImem, err_bits_ok_, kOtbnStatusIdle);

  EXPECT_EQ(otbn_imem_sec_wipe(), kErrorOk);
}

TEST_F(ImemSecWipeTest, Failure) {
  ExpectCmdRun(kOtbnCmdSecWipeImem, 1 << OTBN_ERR_BITS_FATAL_SOFTWARE_BIT,
               kOtbnStatusIdle);

  EXPECT_EQ(otbn_imem_sec_wipe(), kErrorOtbnSecWipeImemFailed);
}

class DmemSecWipeTest : public OtbnTest {};

TEST_F(DmemSecWipeTest, Success) {
  ExpectCmdRun(kOtbnCmdSecWipeDmem, err_bits_ok_, kOtbnStatusIdle);

  EXPECT_EQ(otbn_dmem_sec_wipe(), kErrorOk);
}

TEST_F(DmemSecWipeTest, Failure) {
  ExpectCmdRun(kOtbnCmdSecWipeDmem, 1 << OTBN_ERR_BITS_FATAL_SOFTWARE_BIT,
               kOtbnStatusIdle);

  EXPECT_EQ(otbn_dmem_sec_wipe(), kErrorOtbnSecWipeDmemFailed);
}

class DmemWriteTest : public OtbnTest {};

TEST_F(DmemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 8, "OTBN DMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};
  otbn_addr_t dest_addr = 0;

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + dest_addr, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + dest_addr + 4,
                     test_data[1]);

  EXPECT_EQ(otbn_dmem_write(2, test_data.data(), dest_addr), kErrorOk);
}

TEST_F(DmemWriteTest, SuccessWithOffset) {
  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 12, "OTBN DMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};
  otbn_addr_t dest_addr = 4;

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + dest_addr, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + dest_addr + 4,
                     test_data[1]);

  EXPECT_EQ(otbn_dmem_write(2, test_data.data(), dest_addr), kErrorOk);
}

TEST_F(DmemWriteTest, FailureOutOfRange) {
  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};
  otbn_addr_t dest_addr = OTBN_DMEM_SIZE_BYTES;

  EXPECT_EQ(otbn_dmem_write(2, test_data.data(), dest_addr),
            kErrorOtbnBadOffsetLen);
}

TEST_F(DmemWriteTest, FailureOverflowNumWords) {
  // Try to trigger an integer overflow with `num_words`.
  size_t num_words =
      (std::numeric_limits<size_t>::max() / sizeof(uint32_t)) + 1;
  otbn_addr_t dest_addr = 0;

  EXPECT_EQ(otbn_dmem_write(num_words, NULL, dest_addr),
            kErrorOtbnBadOffsetLen);
}

TEST_F(DmemWriteTest, FailureOverflowOffset) {
  // Try to trigger an integer overflow with `dest_addr`.
  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};
  otbn_addr_t dest_addr = std::numeric_limits<uint32_t>::max();

  EXPECT_EQ(otbn_dmem_write(test_data.size(), test_data.data(), dest_addr),
            kErrorOtbnBadOffsetLen);
}

class DmemReadTest : public OtbnTest {};

TEST_F(DmemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);
  static_assert(OTBN_DMEM_SIZE_BYTES >= 8, "OTBN DMEM size too small.");

  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET, 0x12345678);
  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + 4, 0xabcdef01);

  std::array<uint32_t, 2> test_data = {0};

  otbn_addr_t src_addr = 0;
  EXPECT_EQ(otbn_dmem_read(2, src_addr, test_data.data()), kErrorOk);
  EXPECT_THAT(test_data, ElementsAre(0x12345678, 0xabcdef01));
}

TEST_F(DmemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 12, "OTBN DMEM size too small.");

  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + 8, 0xabcdef01);

  std::array<uint32_t, 2> test_data = {0};

  otbn_addr_t src_addr = 4;
  EXPECT_EQ(otbn_dmem_read(2, src_addr, test_data.data()), kErrorOk);
  EXPECT_THAT(test_data, ElementsAre(0x12345678, 0xabcdef01));
}

class OtbnAppTest : public OtbnTest {};

TEST_F(OtbnAppTest, OtbnLoadAppSuccess) {
  std::array<uint32_t, 2> imem_data = {0x01234567, 0x89abcdef};
  std::array<uint32_t, 2> dmem_data = {0x456789ab, 0xcdef0123};
  otbn_addr_t dmem_data_offset = 0x12;
  otbn_app_t app = {
      .imem_start = imem_data.data(),
      .imem_end = imem_data.data() + imem_data.size(),
      .dmem_data_start = dmem_data.data(),
      .dmem_data_end = dmem_data.data() + imem_data.size(),
      .dmem_data_start_addr = dmem_data_offset,
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
  // `otbn_dmem_sec_wipe`
  ExpectCmdRun(kOtbnCmdSecWipeDmem, err_bits_ok_, kOtbnStatusIdle);
  // `otbn_imem_sec_wipe`
  ExpectCmdRun(kOtbnCmdSecWipeImem, err_bits_ok_, kOtbnStatusIdle);
  // `otbn_imem_write`
  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET, imem_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + sizeof(uint32_t),
                     imem_data[1]);
  // `otbn_dmem_write`
  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + dmem_data_offset,
                     dmem_data[0]);
  EXPECT_ABS_WRITE32(
      base_ + OTBN_DMEM_REG_OFFSET + dmem_data_offset + sizeof(uint32_t),
      dmem_data[1]);

  EXPECT_EQ(otbn_load_app(app), kErrorOk);
}

TEST_F(OtbnAppTest, OtbnLoadInvalidAppEmptyImem) {
  // Create an invalid app with an empty IMEM range.
  std::array<uint32_t, 0> imem_data = {};
  std::array<uint32_t, 2> dmem_data = {0x456789ab, 0xcdef0123};
  otbn_addr_t dmem_data_offset = 0x12;
  otbn_app_t app = {
      .imem_start = imem_data.data(),
      .imem_end = imem_data.data() + imem_data.size(),
      .dmem_data_start = dmem_data.data(),
      .dmem_data_end = dmem_data.data() + dmem_data.size(),
      .dmem_data_start_addr = dmem_data_offset,
  };

  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= sizeof(uint32_t) * dmem_data.size(),
                "OTBN DMEM size too small");
  static_assert(OTBN_IMEM_SIZE_BYTES >= sizeof(uint32_t) * imem_data.size(),
                "OTBN IMEM size too small");

  EXPECT_EQ(otbn_load_app(app), kErrorOtbnInvalidArgument);
}

TEST_F(OtbnAppTest, OtbnLoadInvalidAppImemOutOfRange) {
  // Create an invalid app with a too-large IMEM range.
  std::array<uint32_t, (OTBN_IMEM_SIZE_BYTES / sizeof(uint32_t)) + 1>
      imem_data = {0};
  std::array<uint32_t, 2> dmem_data = {0x456789ab, 0xcdef0123};
  otbn_addr_t dmem_data_offset = 0x12;
  otbn_app_t app = {
      .imem_start = imem_data.data(),
      .imem_end = imem_data.data() + imem_data.size(),
      .dmem_data_start = dmem_data.data(),
      .dmem_data_end = dmem_data.data() + dmem_data.size(),
      .dmem_data_start_addr = dmem_data_offset,
  };

  // Read twice for hardening.
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusIdle);
  // `otbn_dmem_sec_wipe`
  ExpectCmdRun(kOtbnCmdSecWipeDmem, err_bits_ok_, kOtbnStatusIdle);
  // `otbn_imem_sec_wipe`
  ExpectCmdRun(kOtbnCmdSecWipeImem, err_bits_ok_, kOtbnStatusIdle);

  EXPECT_EQ(otbn_load_app(app), kErrorOtbnBadOffsetLen);
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

  EXPECT_EQ(otbn_dmem_write(2, test_data.data(), kDestAddr), kErrorOk);
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

  EXPECT_EQ(otbn_dmem_read(2, kSrcAddr, test_data.data()), kErrorOk);
  EXPECT_THAT(test_data, ElementsAre(0x12345678, 0xabcdef01));
}
}  // namespace
}  // namespace otbn_unittest
