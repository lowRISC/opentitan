// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "otbn_regs.h"  // Generated.

namespace dif_otbn_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::Eq;
using testing::Test;

class OtbnTest : public Test, public MmioTest {
 protected:
  void ExpectDeviceReset() {
    EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET,
                   std::numeric_limits<uint32_t>::max());
  }

  dif_otbn_t dif_otbn_ = {.base_addr = dev().region()};
};

class ResetTest : public OtbnTest {};

TEST_F(ResetTest, NullArgs) { EXPECT_DIF_BADARG(dif_otbn_reset(nullptr)); }

TEST_F(ResetTest, Default) {
  ExpectDeviceReset();

  EXPECT_DIF_OK(dif_otbn_reset(&dif_otbn_));
}

class WriteCmdTest : public OtbnTest {};

TEST_F(WriteCmdTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_write_cmd(nullptr, kDifOtbnCmdExecute));
}

TEST_F(WriteCmdTest, Success) {
  // Set EXECUTE command.
  EXPECT_WRITE32(OTBN_CMD_REG_OFFSET, kDifOtbnCmdExecute);

  EXPECT_DIF_OK(dif_otbn_write_cmd(&dif_otbn_, kDifOtbnCmdExecute));
}

class GetStatusTest : public OtbnTest {};

TEST_F(GetStatusTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_get_status(nullptr, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_get_status(&dif_otbn_, nullptr));

  dif_otbn_status_t status = kDifOtbnStatusBusySecWipeDmem;
  EXPECT_DIF_BADARG(dif_otbn_get_status(nullptr, &status));
  EXPECT_EQ(status, kDifOtbnStatusBusySecWipeDmem);
}

TEST_F(GetStatusTest, Success) {
  EXPECT_READ32(OTBN_STATUS_REG_OFFSET, kDifOtbnStatusBusyExecute);

  dif_otbn_status_t status;
  EXPECT_DIF_OK(dif_otbn_get_status(&dif_otbn_, &status));
  EXPECT_EQ(status, kDifOtbnStatusBusyExecute);
}

class GetErrBitsTest : public OtbnTest {};

TEST_F(GetErrBitsTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_get_err_bits(nullptr, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_get_err_bits(&dif_otbn_, nullptr));

  dif_otbn_err_bits_t err_bits = kDifOtbnErrBitsBadDataAddr;
  EXPECT_DIF_BADARG(dif_otbn_get_err_bits(nullptr, &err_bits));
  EXPECT_EQ(err_bits, kDifOtbnErrBitsBadDataAddr);
}

TEST_F(GetErrBitsTest, Success) {
  EXPECT_READ32(OTBN_ERR_BITS_REG_OFFSET,
                kDifOtbnErrBitsIllegalInsn | kDifOtbnErrBitsRegIntgViolation);

  dif_otbn_err_bits_t err_bits;
  EXPECT_DIF_OK(dif_otbn_get_err_bits(&dif_otbn_, &err_bits));
  EXPECT_EQ(err_bits,
            kDifOtbnErrBitsIllegalInsn | kDifOtbnErrBitsRegIntgViolation);
}

class GetInsnCntTest : public OtbnTest {};

TEST_F(GetInsnCntTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_get_insn_cnt(nullptr, nullptr));

  EXPECT_DIF_BADARG(dif_otbn_get_insn_cnt(&dif_otbn_, nullptr));

  uint32_t insn_cnt = 55;
  EXPECT_DIF_BADARG(dif_otbn_get_insn_cnt(nullptr, &insn_cnt));
  EXPECT_EQ(insn_cnt, 55);
}

TEST_F(GetInsnCntTest, Success) {
  EXPECT_READ32(OTBN_INSN_CNT_REG_OFFSET, 55);

  uint32_t insn_cnt;
  EXPECT_DIF_OK(dif_otbn_get_insn_cnt(&dif_otbn_, &insn_cnt));
  EXPECT_EQ(insn_cnt, 55);
}

class ImemWriteTest : public OtbnTest {};

TEST_F(ImemWriteTest, NullArgs) {
  uint32_t test_data[] = {0};

  EXPECT_DIF_BADARG(dif_otbn_imem_write(nullptr, 0, nullptr, 4));

  EXPECT_DIF_BADARG(dif_otbn_imem_write(nullptr, 0, test_data, 4));

  EXPECT_DIF_BADARG(dif_otbn_imem_write(&dif_otbn_, 0, nullptr, 4));
}

TEST_F(ImemWriteTest, BadLenBytes) {
  uint32_t test_data[] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_DIF_BADARG(dif_otbn_imem_write(&dif_otbn_, 0, test_data, 1));

  EXPECT_DIF_BADARG(dif_otbn_imem_write(&dif_otbn_, 0, test_data, 2));
}

TEST_F(ImemWriteTest, BadOffset) {
  uint32_t test_data[] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_DIF_BADARG(dif_otbn_imem_write(&dif_otbn_, 1, test_data, 4));

  EXPECT_DIF_BADARG(dif_otbn_imem_write(&dif_otbn_, 2, test_data, 4));
}

TEST_F(ImemWriteTest, BadAddressBeyondMemorySize) {
  uint32_t test_data[] = {0};

  EXPECT_DIF_BADARG(
      dif_otbn_imem_write(&dif_otbn_, OTBN_IMEM_SIZE_BYTES, test_data, 4));
}

TEST_F(ImemWriteTest, BadAddressIntegerOverflow) {
  uint32_t test_data[4] = {0};

  EXPECT_DIF_BADARG(dif_otbn_imem_write(&dif_otbn_, 0xFFFFFFFC, test_data, 16));
}

TEST_F(ImemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET, test_data[0]);
  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_DIF_OK(dif_otbn_imem_write(&dif_otbn_, 0, test_data, 8));
}

TEST_F(ImemWriteTest, SuccessWithOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_DIF_OK(dif_otbn_imem_write(&dif_otbn_, 4, test_data, 8));
}

class ImemReadTest : public OtbnTest {};

TEST_F(ImemReadTest, NullArgs) {
  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_DIF_BADARG(dif_otbn_imem_read(nullptr, 0, nullptr, sizeof(test_data)));

  EXPECT_DIF_BADARG(
      dif_otbn_imem_read(nullptr, 0, test_data, sizeof(test_data)));

  EXPECT_DIF_BADARG(
      dif_otbn_imem_read(&dif_otbn_, 0, nullptr, sizeof(test_data)));

  // No side effects are expected.
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(ImemReadTest, BadLenBytes) {
  uint32_t test_data[2] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_DIF_BADARG(dif_otbn_imem_read(&dif_otbn_, 0, test_data, 1));

  EXPECT_DIF_BADARG(dif_otbn_imem_read(&dif_otbn_, 0, test_data, 2));
}

TEST_F(ImemReadTest, BadOffset) {
  uint32_t test_data[2] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_DIF_BADARG(
      dif_otbn_imem_read(&dif_otbn_, 1, test_data, sizeof(test_data)));

  EXPECT_DIF_BADARG(
      dif_otbn_imem_read(&dif_otbn_, 2, test_data, sizeof(test_data)));
}

TEST_F(ImemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_IMEM_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 4, 0xabcdef01);

  EXPECT_DIF_OK(dif_otbn_imem_read(&dif_otbn_, 0, test_data, 8));
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(ImemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 8, 0xabcdef01);

  EXPECT_DIF_OK(dif_otbn_imem_read(&dif_otbn_, 4, test_data, 8));
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

class DmemWriteTest : public OtbnTest {};

TEST_F(DmemWriteTest, NullArgs) {
  uint32_t test_data[1] = {0};

  EXPECT_DIF_BADARG(dif_otbn_dmem_write(nullptr, 0, nullptr, 4));

  EXPECT_DIF_BADARG(dif_otbn_dmem_write(nullptr, 0, test_data, 4));

  EXPECT_DIF_BADARG(dif_otbn_dmem_write(&dif_otbn_, 0, nullptr, 4));
}

TEST_F(DmemWriteTest, BadLenBytes) {
  uint32_t test_data[1] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_DIF_BADARG(dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 1));

  EXPECT_DIF_BADARG(dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 2));
}

TEST_F(DmemWriteTest, BadOffset) {
  uint32_t test_data[1] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_DIF_BADARG(dif_otbn_dmem_write(&dif_otbn_, 1, test_data, 4));

  EXPECT_DIF_BADARG(dif_otbn_dmem_write(&dif_otbn_, 2, test_data, 4));
}

TEST_F(DmemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET, test_data[0]);
  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_DIF_OK(dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 8));
}

TEST_F(DmemWriteTest, SuccessWithOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_DIF_OK(dif_otbn_dmem_write(&dif_otbn_, 4, test_data, 8));
}

class DmemReadTest : public OtbnTest {};

TEST_F(DmemReadTest, NullArgs) {
  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_DIF_BADARG(dif_otbn_dmem_read(nullptr, 0, nullptr, sizeof(test_data)));

  EXPECT_DIF_BADARG(
      dif_otbn_dmem_read(nullptr, 0, test_data, sizeof(test_data)));

  EXPECT_DIF_BADARG(
      dif_otbn_dmem_read(&dif_otbn_, 0, nullptr, sizeof(test_data)));

  // No side effects are expected.
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(DmemReadTest, BadLenBytes) {
  uint32_t test_data[2] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_DIF_BADARG(dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 1));

  EXPECT_DIF_BADARG(dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 2));
}

TEST_F(DmemReadTest, BadOffset) {
  uint32_t test_data[2] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_DIF_BADARG(
      dif_otbn_dmem_read(&dif_otbn_, 1, test_data, sizeof(test_data)));

  EXPECT_DIF_BADARG(
      dif_otbn_dmem_read(&dif_otbn_, 2, test_data, sizeof(test_data)));
}

TEST_F(DmemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_DMEM_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 4, 0xabcdef01);

  EXPECT_DIF_OK(dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 8));
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(DmemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 8, 0xabcdef01);

  EXPECT_DIF_OK(dif_otbn_dmem_read(&dif_otbn_, 4, test_data, 8));
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

class ControlSoftwareErrorsFatalTest : public OtbnTest {};

TEST_F(ControlSoftwareErrorsFatalTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_otbn_set_ctrl_software_errs_fatal(nullptr, false));
}

TEST_F(ControlSoftwareErrorsFatalTest, Success) {
  EXPECT_WRITE32(OTBN_CTRL_REG_OFFSET, 0x1);
  EXPECT_READ32(OTBN_CTRL_REG_OFFSET, 0x1);

  EXPECT_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(&dif_otbn_, true));
}

TEST_F(ControlSoftwareErrorsFatalTest, Failure) {
  EXPECT_WRITE32(OTBN_CTRL_REG_OFFSET, 0x0);
  EXPECT_READ32(OTBN_CTRL_REG_OFFSET, 0x1);

  EXPECT_EQ(dif_otbn_set_ctrl_software_errs_fatal(&dif_otbn_, false),
            kDifUnavailable);
}

}  // namespace
}  // namespace dif_otbn_unittest
