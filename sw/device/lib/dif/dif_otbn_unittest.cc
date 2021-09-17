// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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

  mmio_region_t base_addr_ = dev().region();
  dif_otbn_t dif_otbn_ = {
      /* base_addr = */ base_addr_,
  };

  // This is the default configuration, which will be used unless the values
  // are overriden.
  dif_otbn_config_t dif_otbn_config_ = {
      /* base_addr = */ base_addr_,
  };
};

class InitTest : public OtbnTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_otbn_init(nullptr, nullptr), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_init(nullptr, &dif_otbn_), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_init(&dif_otbn_config_, nullptr), kDifOtbnBadArg);
}

TEST_F(InitTest, Default) {
  ExpectDeviceReset();

  EXPECT_EQ(dif_otbn_init(&dif_otbn_config_, &dif_otbn_), kDifOtbnOk);
}

class ResetTest : public OtbnTest {};

TEST_F(ResetTest, NullArgs) {
  EXPECT_EQ(dif_otbn_reset(nullptr), kDifOtbnBadArg);
}

TEST_F(ResetTest, Default) {
  ExpectDeviceReset();

  EXPECT_EQ(dif_otbn_reset(&dif_otbn_), kDifOtbnOk);
}

class IrqStateGetTest : public OtbnTest {};

TEST_F(IrqStateGetTest, NullArgs) {
  dif_otbn_enable_t state;

  EXPECT_EQ(dif_otbn_irq_state_get(nullptr, kDifOtbnInterruptDone, nullptr),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_irq_state_get(nullptr, kDifOtbnInterruptDone, &state),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_irq_state_get(&dif_otbn_, kDifOtbnInterruptDone, nullptr),
            kDifOtbnBadArg);
}

TEST_F(IrqStateGetTest, Success) {
  // Get the (only) IRQ state.
  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, {{OTBN_INTR_STATE_DONE_BIT, true}});

  dif_otbn_enable_t done_state = kDifOtbnDisable;

  EXPECT_EQ(
      dif_otbn_irq_state_get(&dif_otbn_, kDifOtbnInterruptDone, &done_state),
      kDifOtbnOk);
  EXPECT_EQ(done_state, kDifOtbnEnable);
}

class IrqStateClearTest : public OtbnTest {};

TEST_F(IrqStateClearTest, NullArgs) {
  EXPECT_EQ(dif_otbn_irq_state_clear(nullptr, kDifOtbnInterruptDone),
            kDifOtbnBadArg);
}

TEST_F(IrqStateClearTest, Success) {
  // Clear the (only) IRQ state.
  EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET, {{OTBN_INTR_STATE_DONE_BIT, 1}});

  EXPECT_EQ(dif_otbn_irq_state_clear(&dif_otbn_, kDifOtbnInterruptDone),
            kDifOtbnOk);
}

class IrqsDisableTest : public OtbnTest {};

TEST_F(IrqsDisableTest, NullArgs) {
  uint32_t state;

  EXPECT_EQ(dif_otbn_irqs_disable(nullptr, nullptr), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_irqs_disable(nullptr, &state), kDifOtbnBadArg);
}

TEST_F(IrqsDisableTest, SuccessNoStateReturned) {
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_otbn_irqs_disable(&dif_otbn_, nullptr), kDifOtbnOk);
}

TEST_F(IrqsDisableTest, AllDisabled) {
  // IRQs disabled
  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);

  uint32_t state = std::numeric_limits<uint32_t>::max();
  EXPECT_EQ(dif_otbn_irqs_disable(&dif_otbn_, &state), kDifOtbnOk);
  EXPECT_EQ(state, 0);
}

TEST_F(IrqsDisableTest, AllEnabled) {
  // IRQs enabled
  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);

  uint32_t state = 0;
  EXPECT_EQ(dif_otbn_irqs_disable(&dif_otbn_, &state), kDifOtbnOk);
  EXPECT_EQ(state, std::numeric_limits<uint32_t>::max());
}

class IrqsRestoreTest : public OtbnTest {};

TEST_F(IrqsRestoreTest, NullArgs) {
  EXPECT_EQ(
      dif_otbn_irqs_restore(nullptr, std::numeric_limits<uint32_t>::max()),
      kDifOtbnBadArg);
}

TEST_F(IrqsRestoreTest, AllEnabled) {
  uint32_t state = std::numeric_limits<uint32_t>::max();
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, state);

  EXPECT_EQ(dif_otbn_irqs_restore(&dif_otbn_, state), kDifOtbnOk);
}

TEST_F(IrqsRestoreTest, NoneEnabled) {
  uint32_t state = 0;
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, state);

  EXPECT_EQ(dif_otbn_irqs_restore(&dif_otbn_, state), kDifOtbnOk);
}

class IrqControlTest : public OtbnTest {};

TEST_F(IrqControlTest, NullArgs) {
  EXPECT_EQ(
      dif_otbn_irq_control(nullptr, kDifOtbnInterruptDone, kDifOtbnEnable),
      kDifOtbnBadArg);
}

TEST_F(IrqControlTest, Success) {
  // Enable (only) IRQ.
  EXPECT_MASK32(OTBN_INTR_ENABLE_REG_OFFSET,
                {{OTBN_INTR_ENABLE_DONE_BIT, 0x1, true}});

  EXPECT_EQ(
      dif_otbn_irq_control(&dif_otbn_, kDifOtbnInterruptDone, kDifOtbnEnable),
      kDifOtbnOk);
}

class IrqForceTest : public OtbnTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_otbn_irq_force(nullptr, kDifOtbnInterruptDone), kDifOtbnBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force (only) IRQ.
  EXPECT_MASK32(OTBN_INTR_TEST_REG_OFFSET,
                {{OTBN_INTR_TEST_DONE_BIT, 0x1, true}});

  EXPECT_EQ(dif_otbn_irq_force(&dif_otbn_, kDifOtbnInterruptDone), kDifOtbnOk);
}

class SetStartAddrTest : public OtbnTest {};

TEST_F(SetStartAddrTest, NullArgs) {
  EXPECT_EQ(dif_otbn_set_start_addr(nullptr, 0), kDifOtbnBadArg);
}

TEST_F(SetStartAddrTest, BadStartAddress) {
  // Must be 4-byte aligned.
  EXPECT_EQ(dif_otbn_set_start_addr(&dif_otbn_, 1), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_set_start_addr(&dif_otbn_, 2), kDifOtbnBadArg);

  // Valid addresses (ignoring alignment): 0 .. (OTBN_IMEM_SIZE_BYTES - 1)
  EXPECT_EQ(dif_otbn_set_start_addr(&dif_otbn_, OTBN_IMEM_SIZE_BYTES),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_set_start_addr(&dif_otbn_, OTBN_IMEM_SIZE_BYTES + 32),
            kDifOtbnBadArg);
}

TEST_F(SetStartAddrTest, Success) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  // Write start address.
  EXPECT_WRITE32(OTBN_START_ADDR_REG_OFFSET, 4);

  EXPECT_EQ(dif_otbn_set_start_addr(&dif_otbn_, 4), kDifOtbnOk);
}

class WriteCmdTest : public OtbnTest {};

TEST_F(WriteCmdTest, NullArgs) {
  EXPECT_EQ(dif_otbn_write_cmd(nullptr, kDifOtbnCmdExecute), kDifOtbnBadArg);
}

TEST_F(WriteCmdTest, Success) {
  // Set EXECUTE command.
  EXPECT_WRITE32(OTBN_CMD_REG_OFFSET, kDifOtbnCmdExecute);

  EXPECT_EQ(dif_otbn_write_cmd(&dif_otbn_, kDifOtbnCmdExecute), kDifOtbnOk);
}

class GetStatusTest : public OtbnTest {};

TEST_F(GetStatusTest, NullArgs) {
  EXPECT_EQ(dif_otbn_get_status(nullptr, nullptr), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_get_status(&dif_otbn_, nullptr), kDifOtbnBadArg);

  dif_otbn_status_t status = kDifOtbnStatusBusySecWipeDmem;
  EXPECT_EQ(dif_otbn_get_status(nullptr, &status), kDifOtbnBadArg);
  EXPECT_EQ(status, kDifOtbnStatusBusySecWipeDmem);
}

TEST_F(GetStatusTest, Success) {
  EXPECT_READ32(OTBN_STATUS_REG_OFFSET, kDifOtbnStatusBusyExecute);

  dif_otbn_status_t status;
  EXPECT_EQ(dif_otbn_get_status(&dif_otbn_, &status), kDifOtbnOk);
  EXPECT_EQ(status, kDifOtbnStatusBusyExecute);
}

class GetErrBitsTest : public OtbnTest {};

TEST_F(GetErrBitsTest, NullArgs) {
  EXPECT_EQ(dif_otbn_get_err_bits(nullptr, nullptr), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_get_err_bits(&dif_otbn_, nullptr), kDifOtbnBadArg);

  dif_otbn_err_bits_t err_bits = kDifOtbnErrBitsBadDataAddr;
  EXPECT_EQ(dif_otbn_get_err_bits(nullptr, &err_bits), kDifOtbnBadArg);
  EXPECT_EQ(err_bits, kDifOtbnErrBitsBadDataAddr);
}

TEST_F(GetErrBitsTest, Success) {
  EXPECT_READ32(OTBN_ERR_BITS_REG_OFFSET,
                kDifOtbnErrBitsIllegalInsn | kDifOtbnErrBitsRegIntgViolation);

  dif_otbn_err_bits_t err_bits;
  EXPECT_EQ(dif_otbn_get_err_bits(&dif_otbn_, &err_bits), kDifOtbnOk);
  EXPECT_EQ(err_bits,
            kDifOtbnErrBitsIllegalInsn | kDifOtbnErrBitsRegIntgViolation);
}

class GetInsnCntTest : public OtbnTest {};

TEST_F(GetInsnCntTest, NullArgs) {
  EXPECT_EQ(dif_otbn_get_insn_cnt(nullptr, nullptr), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_get_insn_cnt(&dif_otbn_, nullptr), kDifOtbnBadArg);

  uint32_t insn_cnt = 55;
  EXPECT_EQ(dif_otbn_get_insn_cnt(nullptr, &insn_cnt), kDifOtbnBadArg);
  EXPECT_EQ(insn_cnt, 55);
}

TEST_F(GetInsnCntTest, Success) {
  EXPECT_READ32(OTBN_INSN_CNT_REG_OFFSET, 55);

  uint32_t insn_cnt;
  EXPECT_EQ(dif_otbn_get_insn_cnt(&dif_otbn_, &insn_cnt), kDifOtbnOk);
  EXPECT_EQ(insn_cnt, 55);
}

class ImemWriteTest : public OtbnTest {};

TEST_F(ImemWriteTest, NullArgs) {
  uint32_t test_data[] = {0};

  EXPECT_EQ(dif_otbn_imem_write(nullptr, 0, nullptr, 4), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_write(nullptr, 0, test_data, 4), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 0, nullptr, 4), kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadLenBytes) {
  uint32_t test_data[] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 0, test_data, 1), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 0, test_data, 2), kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadOffset) {
  uint32_t test_data[] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 1, test_data, 4), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 2, test_data, 4), kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadAddressBeyondMemorySize) {
  uint32_t test_data[] = {0};

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, OTBN_IMEM_SIZE_BYTES, test_data, 4),
            kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadAddressIntegerOverflow) {
  uint32_t test_data[4] = {0};

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 0xFFFFFFFC, test_data, 16),
            kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET, test_data[0]);
  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 0, test_data, 8), kDifOtbnOk);
}

TEST_F(ImemWriteTest, SuccessWithOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_EQ(dif_otbn_imem_write(&dif_otbn_, 4, test_data, 8), kDifOtbnOk);
}

class ImemReadTest : public OtbnTest {};

TEST_F(ImemReadTest, NullArgs) {
  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_EQ(dif_otbn_imem_read(nullptr, 0, nullptr, sizeof(test_data)),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_read(nullptr, 0, test_data, sizeof(test_data)),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 0, nullptr, sizeof(test_data)),
            kDifOtbnBadArg);

  // No side effects are expected.
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(ImemReadTest, BadLenBytes) {
  uint32_t test_data[2] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 0, test_data, 1), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 0, test_data, 2), kDifOtbnBadArg);
}

TEST_F(ImemReadTest, BadOffset) {
  uint32_t test_data[2] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 1, test_data, sizeof(test_data)),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 2, test_data, sizeof(test_data)),
            kDifOtbnBadArg);
}

TEST_F(ImemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_IMEM_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 4, 0xabcdef01);

  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 0, test_data, 8), kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(ImemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 8, 0xabcdef01);

  EXPECT_EQ(dif_otbn_imem_read(&dif_otbn_, 4, test_data, 8), kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

class DmemWriteTest : public OtbnTest {};

TEST_F(DmemWriteTest, NullArgs) {
  uint32_t test_data[1] = {0};

  EXPECT_EQ(dif_otbn_dmem_write(nullptr, 0, nullptr, 4), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_write(nullptr, 0, test_data, 4), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 0, nullptr, 4), kDifOtbnBadArg);
}

TEST_F(DmemWriteTest, BadLenBytes) {
  uint32_t test_data[1] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 1), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 2), kDifOtbnBadArg);
}

TEST_F(DmemWriteTest, BadOffset) {
  uint32_t test_data[1] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 1, test_data, 4), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 2, test_data, 4), kDifOtbnBadArg);
}

TEST_F(DmemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET, test_data[0]);
  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 4, test_data[1]);

  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 8), kDifOtbnOk);
}

TEST_F(DmemWriteTest, SuccessWithOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 8, test_data[1]);

  EXPECT_EQ(dif_otbn_dmem_write(&dif_otbn_, 4, test_data, 8), kDifOtbnOk);
}

class DmemReadTest : public OtbnTest {};

TEST_F(DmemReadTest, NullArgs) {
  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_EQ(dif_otbn_dmem_read(nullptr, 0, nullptr, sizeof(test_data)),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_read(nullptr, 0, test_data, sizeof(test_data)),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 0, nullptr, sizeof(test_data)),
            kDifOtbnBadArg);

  // No side effects are expected.
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(DmemReadTest, BadLenBytes) {
  uint32_t test_data[2] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 1), kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 2), kDifOtbnBadArg);
}

TEST_F(DmemReadTest, BadOffset) {
  uint32_t test_data[2] = {0};

  // `offset` must be 32b-aligned.
  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 1, test_data, sizeof(test_data)),
            kDifOtbnBadArg);

  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 2, test_data, sizeof(test_data)),
            kDifOtbnBadArg);
}

TEST_F(DmemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_DMEM_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 4, 0xabcdef01);

  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 8), kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(DmemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 8, 0xabcdef01);

  EXPECT_EQ(dif_otbn_dmem_read(&dif_otbn_, 4, test_data, 8), kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

}  // namespace
}  // namespace dif_otbn_unittest
