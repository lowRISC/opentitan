// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

namespace otbn_unittest {
namespace {
using ::testing::ElementsAre;

class OtbnTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_OTBN_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

class StartTest : public OtbnTest {};

TEST_F(StartTest, BadStartAddress) {
  // Must be 4-byte aligned.
  EXPECT_EQ(otbn_start(1), kErrorOtbnInvalidArgument);
  EXPECT_EQ(otbn_start(2), kErrorOtbnInvalidArgument);

  // Valid addresses (ignoring alignment): 0 .. (OTBN_IMEM_SIZE_BYTES - 1)
  EXPECT_EQ(otbn_start(OTBN_IMEM_SIZE_BYTES), kErrorOtbnInvalidArgument);

  EXPECT_EQ(otbn_start(OTBN_IMEM_SIZE_BYTES + 32), kErrorOtbnInvalidArgument);
}

TEST_F(StartTest, Success) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 8, "OTBN IMEM size too small.");

  // Write start address.
  EXPECT_ABS_WRITE32(base_ + OTBN_START_ADDR_REG_OFFSET, 4);

  // Set EXECUTE command.
  EXPECT_ABS_WRITE32(base_ + OTBN_CMD_REG_OFFSET, kOtbnCmdExecute);

  EXPECT_EQ(otbn_start(4), kErrorOk);
}

class IsBusyTest : public OtbnTest {};

TEST_F(IsBusyTest, Success) {
  EXPECT_ABS_READ32(base_ + OTBN_STATUS_REG_OFFSET, kOtbnStatusBusyExecute);

  EXPECT_EQ(otbn_is_busy(), true);
}

class GetErrBitsTest : public OtbnTest {};

TEST_F(GetErrBitsTest, Success) {
  EXPECT_ABS_READ32(base_ + OTBN_ERR_BITS_REG_OFFSET,
                    kOtbnErrBitsIllegalInsn | kOtbnErrBitsFatalReg);

  otbn_err_bits_t err_bits;
  otbn_get_err_bits(&err_bits);
  EXPECT_EQ(err_bits, kOtbnErrBitsIllegalInsn | kOtbnErrBitsFatalReg);
}

class ImemWriteTest : public OtbnTest {};

TEST_F(ImemWriteTest, BadOffset) {
  std::array<uint32_t, 2> test_data = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(otbn_imem_write(1, test_data.data(), 1), kErrorOtbnBadOffset);
  EXPECT_EQ(otbn_imem_write(2, test_data.data(), 1), kErrorOtbnBadOffset);
}

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

  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_EQ(otbn_imem_write(0, test_data.data(), 2), kErrorOk);
}

TEST_F(ImemWriteTest, SuccessWithOffset) {
  // Test assumption.
  static_assert(OTBN_IMEM_SIZE_BYTES >= 12, "OTBN IMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_IMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_EQ(otbn_imem_write(4, test_data.data(), 2), kErrorOk);
}

class DmemWriteTest : public OtbnTest {};

TEST_F(DmemWriteTest, BadOffset) {
  std::array<uint32_t, 1> test_data = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(otbn_dmem_write(1, test_data.data(), 1), kErrorOtbnBadOffset);
  EXPECT_EQ(otbn_dmem_write(2, test_data.data(), 1), kErrorOtbnBadOffset);
}

TEST_F(DmemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 8, "OTBN DMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_EQ(otbn_dmem_write(0, test_data.data(), 2), kErrorOk);
}

TEST_F(DmemWriteTest, SuccessWithOffset) {
  // Test assumption.
  static_assert(OTBN_DMEM_SIZE_BYTES >= 12, "OTBN DMEM size too small.");

  std::array<uint32_t, 2> test_data = {0x12345678, 0xabcdef01};

  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_ABS_WRITE32(base_ + OTBN_DMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_EQ(otbn_dmem_write(4, test_data.data(), 2), kErrorOk);
}

class DmemReadTest : public OtbnTest {};

TEST_F(DmemReadTest, BadOffset) {
  std::array<uint32_t, 2> test_data = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(otbn_dmem_read(1, test_data.data(), 2), kErrorOtbnBadOffset);
  EXPECT_EQ(otbn_dmem_read(2, test_data.data(), 2), kErrorOtbnBadOffset);
}

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

}  // namespace
}  // namespace otbn_unittest
