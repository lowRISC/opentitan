// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/lib/base/testing/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

namespace otbn_unittest {
namespace {
using ::testing::ElementsAre;
using ::testing::Return;

class OtbnTest : public mask_rom_test::MaskRomTest {
 protected:
  /**
   * Sets expectations for running an OTBN command.
   *
   * @param cmd Command.
   * @param err_bits Error bits.
   */
  void ExpectCmdRun(otbn_cmd_t cmd, otbn_err_bits_t err_bits) {
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
  }

  uint32_t base_ = TOP_EARLGREY_OTBN_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
  mask_rom_test::MockRnd rnd_;
};

class ExecuteTest : public OtbnTest {};

TEST_F(ExecuteTest, Success) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 8, "OTBN IMEM size too small.");

  ExpectCmdRun(kOtbnCmdExecute, kOtbnErrBitsNoError);

  EXPECT_EQ(otbn_execute(), kErrorOk);
}

TEST_F(ExecuteTest, Failure) {
  ExpectCmdRun(kOtbnCmdExecute, kOtbnErrBitsFatalSoftware);

  EXPECT_EQ(otbn_execute(), kErrorOtbnExecutionFailed);
}

class IsBusyTest : public OtbnTest {};

TEST_F(IsBusyTest, Success) {
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);

  EXPECT_EQ(otbn_is_busy(), true);
}

class GetErrBitsTest : public OtbnTest {};

TEST_F(GetErrBitsTest, Success) {
  EXPECT_ABS_READ32(base_ + OTBN_ERR_BITS_REG_OFFSET,
                    kOtbnErrBitsIllegalInsn | kOtbnErrBitsRegIntgViolation);

  otbn_err_bits_t err_bits;
  otbn_get_err_bits(&err_bits);
  EXPECT_EQ(err_bits, kOtbnErrBitsIllegalInsn | kOtbnErrBitsRegIntgViolation);
}

class ImemSecWipeTest : public OtbnTest {};

TEST_F(ImemSecWipeTest, Success) {
  ExpectCmdRun(kOtbnCmdSecWipeImem, kOtbnErrBitsNoError);

  EXPECT_EQ(otbn_imem_sec_wipe(), kErrorOk);
}

TEST_F(ImemSecWipeTest, Failure) {
  ExpectCmdRun(kOtbnCmdSecWipeImem, kOtbnErrBitsFatalSoftware);

  EXPECT_EQ(otbn_imem_sec_wipe(), kErrorOtbnSecWipeImemFailed);
}

class ImemWriteTest : public OtbnTest {};

TEST_F(ImemWriteTest, BadAddressBeyondMemorySize) {
  std::array<uint32_t, 2> test_data = {0};

  EXPECT_EQ(otbn_imem_write(OTBN_IMEM_SIZE_BYTES, test_data.data(), 1),
            kErrorOtbnBadOffsetLen);
}

TEST_F(ImemWriteTest, BadAddressIntegerOverflow) {
  std::array<uint32_t, 4> test_data = {0};

  EXPECT_EQ(otbn_imem_write(0xFFFFFFFC, test_data.data(), 1),
            kErrorOtbnBadOffsetLen);
}

TEST_F(ImemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 8, "OTBN IMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_EQ(otbn_imem_write(0, test_data.data(), 2), kErrorOk);
}

TEST_F(ImemWriteTest, SuccessWithOffset) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 12, "OTBN IMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_EQ(otbn_imem_write(4, test_data.data(), 2), kErrorOk);
}

class DmemSecWipeTest : public OtbnTest {};

TEST_F(DmemSecWipeTest, Success) {
  ExpectCmdRun(kOtbnCmdSecWipeDmem, kOtbnErrBitsNoError);

  EXPECT_EQ(otbn_dmem_sec_wipe(), kErrorOk);
}

TEST_F(DmemSecWipeTest, Failure) {
  ExpectCmdRun(kOtbnCmdSecWipeDmem, kOtbnErrBitsFatalSoftware);

  EXPECT_EQ(otbn_dmem_sec_wipe(), kErrorOtbnSecWipeDmemFailed);
}

class DmemWriteTest : public OtbnTest {};

TEST_F(DmemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 8, "OTBN DMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_EQ(otbn_dmem_write(0, test_data.data(), 2), kErrorOk);
}

TEST_F(DmemWriteTest, SuccessWithOffset) {
  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 12, "OTBN DMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_CALL(rnd_, Uint32()).WillOnce(Return(0));
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_EQ(otbn_dmem_write(4, test_data.data(), 2), kErrorOk);
}

class DmemReadTest : public OtbnTest {};

TEST_F(DmemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);
  static_assert(OTBN_DMEM_SIZE_BYTES >= 8, "OTBN DMEM size too small.");

  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET, 0x12345678);
  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + 4, 0xabcdef01);

  std::array<uint32_t, 2> test_data = {0};

  EXPECT_EQ(otbn_dmem_read(0, test_data.data(), 2), kErrorOk);
  EXPECT_THAT(test_data, ElementsAre(0x12345678, 0xabcdef01));
}

TEST_F(DmemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 12, "OTBN DMEM size too small.");

  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_ABS_READ32(base_ + OTBN_DMEM_REG_OFFSET + 8, 0xabcdef01);

  std::array<uint32_t, 2> test_data = {0};

  EXPECT_EQ(otbn_dmem_read(4, test_data.data(), 2), kErrorOk);
  EXPECT_THAT(test_data, ElementsAre(0x12345678, 0xabcdef01));
}

class ControlSoftwareErrorsFatalTest : public OtbnTest {};

TEST_F(ControlSoftwareErrorsFatalTest, Success) {
  EXPECT_ABS_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x1);
  EXPECT_ABS_READ32(base_ + OTBN_CTRL_REG_OFFSET, 0x1);

  EXPECT_EQ(otbn_set_ctrl_software_errs_fatal(true), kErrorOk);
}  // namespace

TEST_F(ControlSoftwareErrorsFatalTest, Failure) {
  EXPECT_ABS_WRITE32(base_ + OTBN_CTRL_REG_OFFSET, 0x0);
  EXPECT_ABS_READ32(base_ + OTBN_CTRL_REG_OFFSET, 0x1);

  EXPECT_EQ(otbn_set_ctrl_software_errs_fatal(false), kErrorOtbnUnavailable);
}

}  // namespace
}  // namespace otbn_unittest
