// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

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
  dif_otbn_result_t result;

  result = dif_otbn_init(nullptr, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_init(nullptr, &dif_otbn_);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_init(&dif_otbn_config_, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(InitTest, Default) {
  ExpectDeviceReset();

  dif_otbn_result_t result = dif_otbn_init(&dif_otbn_config_, &dif_otbn_);
  EXPECT_EQ(result, kDifOtbnOk);
}

class ResetTest : public OtbnTest {};

TEST_F(ResetTest, NullArgs) {
  dif_otbn_result_t result;
  result = dif_otbn_reset(nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ResetTest, Default) {
  ExpectDeviceReset();

  dif_otbn_result_t result = dif_otbn_reset(&dif_otbn_);
  EXPECT_EQ(result, kDifOtbnOk);
}

class IrqStateGetTest : public OtbnTest {};

TEST_F(IrqStateGetTest, NullArgs) {
  dif_otbn_result_t result;
  dif_otbn_enable_t state;

  result = dif_otbn_irq_state_get(nullptr, kDifOtbnInterruptDone, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_irq_state_get(nullptr, kDifOtbnInterruptDone, &state);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_irq_state_get(&dif_otbn_, kDifOtbnInterruptDone, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(IrqStateGetTest, Success) {
  // Get the (only) IRQ state.
  EXPECT_READ32(OTBN_INTR_STATE_REG_OFFSET, {{OTBN_INTR_STATE_DONE_BIT, true}});

  dif_otbn_enable_t done_state = kDifOtbnDisable;
  dif_otbn_result_t result =
      dif_otbn_irq_state_get(&dif_otbn_, kDifOtbnInterruptDone, &done_state);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(done_state, kDifOtbnEnable);
}

class IrqStateClearTest : public OtbnTest {};

TEST_F(IrqStateClearTest, NullArgs) {
  dif_otbn_result_t result =
      dif_otbn_irq_state_clear(nullptr, kDifOtbnInterruptDone);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(IrqStateClearTest, Success) {
  // Clear the (only) IRQ state.
  EXPECT_WRITE32(OTBN_INTR_STATE_REG_OFFSET, {{OTBN_INTR_STATE_DONE_BIT, 1}});

  dif_otbn_result_t result =
      dif_otbn_irq_state_clear(&dif_otbn_, kDifOtbnInterruptDone);
  EXPECT_EQ(result, kDifOtbnOk);
}

class IrqsDisableTest : public OtbnTest {};

TEST_F(IrqsDisableTest, NullArgs) {
  uint32_t state;
  dif_otbn_result_t result;

  result = dif_otbn_irqs_disable(nullptr, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_irqs_disable(nullptr, &state);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(IrqsDisableTest, SuccessNoStateReturned) {
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);

  dif_otbn_result_t result = dif_otbn_irqs_disable(&dif_otbn_, nullptr);
  EXPECT_EQ(result, kDifOtbnOk);
}

TEST_F(IrqsDisableTest, AllDisabled) {
  // IRQs disabled
  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);

  uint32_t state = std::numeric_limits<uint32_t>::max();
  dif_otbn_result_t result = dif_otbn_irqs_disable(&dif_otbn_, &state);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(state, 0);
}

TEST_F(IrqsDisableTest, AllEnabled) {
  // IRQs enabled
  EXPECT_READ32(OTBN_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, 0);

  uint32_t state = 0;
  dif_otbn_result_t result = dif_otbn_irqs_disable(&dif_otbn_, &state);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(state, std::numeric_limits<uint32_t>::max());
}

class IrqsRestoreTest : public OtbnTest {};

TEST_F(IrqsRestoreTest, NullArgs) {
  dif_otbn_result_t result =
      dif_otbn_irqs_restore(nullptr, std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(IrqsRestoreTest, AllEnabled) {
  uint32_t state = std::numeric_limits<uint32_t>::max();
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, state);

  dif_otbn_result_t result = dif_otbn_irqs_restore(&dif_otbn_, state);
  EXPECT_EQ(result, kDifOtbnOk);
}

TEST_F(IrqsRestoreTest, NoneEnabled) {
  uint32_t state = 0;
  EXPECT_WRITE32(OTBN_INTR_ENABLE_REG_OFFSET, state);

  dif_otbn_result_t result = dif_otbn_irqs_restore(&dif_otbn_, state);
  EXPECT_EQ(result, kDifOtbnOk);
}

class IrqControlTest : public OtbnTest {};

TEST_F(IrqControlTest, NullArgs) {
  dif_otbn_result_t result =
      dif_otbn_irq_control(nullptr, kDifOtbnInterruptDone, kDifOtbnEnable);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(IrqControlTest, Success) {
  // Enable (only) IRQ.
  EXPECT_MASK32(OTBN_INTR_ENABLE_REG_OFFSET,
                {{OTBN_INTR_ENABLE_DONE_BIT, 0x1, true}});

  dif_otbn_result_t result =
      dif_otbn_irq_control(&dif_otbn_, kDifOtbnInterruptDone, kDifOtbnEnable);
  EXPECT_EQ(result, kDifOtbnOk);
}

class IrqForceTest : public OtbnTest {};

TEST_F(IrqForceTest, NullArgs) {
  dif_otbn_result_t result = dif_otbn_irq_force(nullptr, kDifOtbnInterruptDone);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force (only) IRQ.
  EXPECT_MASK32(OTBN_INTR_TEST_REG_OFFSET,
                {{OTBN_INTR_TEST_DONE_BIT, 0x1, true}});

  dif_otbn_result_t result =
      dif_otbn_irq_force(&dif_otbn_, kDifOtbnInterruptDone);
  EXPECT_EQ(result, kDifOtbnOk);
}

class StartTest : public OtbnTest {};

TEST_F(StartTest, NullArgs) {
  dif_otbn_result_t result = dif_otbn_start(nullptr, 0);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(StartTest, BadStartAddress) {
  dif_otbn_result_t result;

  // Must be 4-byte aligned.
  result = dif_otbn_start(&dif_otbn_, 1);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_start(&dif_otbn_, 2);
  EXPECT_EQ(result, kDifOtbnBadArg);

  // Valid addresses (ignoring alignment): 0 .. (OTBN_IMEM_SIZE_BYTES - 1)
  result = dif_otbn_start(&dif_otbn_, OTBN_IMEM_SIZE_BYTES);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_start(&dif_otbn_, OTBN_IMEM_SIZE_BYTES + 32);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(StartTest, Success) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  // Write start address.
  EXPECT_WRITE32(OTBN_START_ADDR_REG_OFFSET, 4);

  // Set start command bit.
  EXPECT_WRITE32(OTBN_CMD_REG_OFFSET, {{OTBN_CMD_START_BIT, 1}});

  dif_otbn_result_t result = dif_otbn_start(&dif_otbn_, 4);
  EXPECT_EQ(result, kDifOtbnOk);
}

class IsBusyTest : public OtbnTest {};

TEST_F(IsBusyTest, NullArgs) {
  dif_otbn_result_t result;
  bool busy;

  result = dif_otbn_is_busy(nullptr, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_is_busy(&dif_otbn_, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  // Also check for freedom from side effects in `busy`.
  busy = false;
  result = dif_otbn_is_busy(nullptr, &busy);
  EXPECT_EQ(result, kDifOtbnBadArg);
  EXPECT_EQ(busy, false);

  busy = true;
  result = dif_otbn_is_busy(nullptr, &busy);
  EXPECT_EQ(result, kDifOtbnBadArg);
  EXPECT_EQ(busy, true);
}

TEST_F(IsBusyTest, Success) {
  EXPECT_READ32(OTBN_STATUS_REG_OFFSET, {{OTBN_STATUS_BUSY_BIT, true}});

  bool busy = false;
  dif_otbn_result_t result = dif_otbn_is_busy(&dif_otbn_, &busy);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(busy, true);
}

class GetErrBitsTest : public OtbnTest {};

TEST_F(GetErrBitsTest, NullArgs) {
  dif_otbn_result_t result;
  dif_otbn_err_bits_t err_bits;

  result = dif_otbn_get_err_bits(nullptr, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_get_err_bits(&dif_otbn_, nullptr);
  EXPECT_EQ(result, kDifOtbnBadArg);

  err_bits = kDifOtbnErrBitsBadDataAddr;
  result = dif_otbn_get_err_bits(nullptr, &err_bits);
  EXPECT_EQ(result, kDifOtbnBadArg);
  EXPECT_EQ(err_bits, kDifOtbnErrBitsBadDataAddr);
}

TEST_F(GetErrBitsTest, Success) {
  EXPECT_READ32(OTBN_ERR_BITS_REG_OFFSET,
                kDifOtbnErrBitsIllegalInsn | kDifOtbnErrBitsFatalReg);

  dif_otbn_err_bits_t err_bits;
  dif_otbn_result_t result = dif_otbn_get_err_bits(&dif_otbn_, &err_bits);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(err_bits, kDifOtbnErrBitsIllegalInsn | kDifOtbnErrBitsFatalReg);
}

class ImemWriteTest : public OtbnTest {};

TEST_F(ImemWriteTest, NullArgs) {
  dif_otbn_result_t result;
  uint32_t test_data[] = {0};

  result = dif_otbn_imem_write(nullptr, 0, nullptr, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_write(nullptr, 0, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_write(&dif_otbn_, 0, nullptr, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadLenBytes) {
  dif_otbn_result_t result;
  uint32_t test_data[] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  result = dif_otbn_imem_write(&dif_otbn_, 0, test_data, 1);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_write(&dif_otbn_, 0, test_data, 2);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadOffset) {
  dif_otbn_result_t result;
  uint32_t test_data[] = {0};

  // `offset` must be 32b-aligned.
  result = dif_otbn_imem_write(&dif_otbn_, 1, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_write(&dif_otbn_, 2, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadAddressBeyondMemorySize) {
  dif_otbn_result_t result;
  uint32_t test_data[] = {0};

  result = dif_otbn_imem_write(&dif_otbn_, OTBN_IMEM_SIZE_BYTES, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, BadAddressIntegerOverflow) {
  dif_otbn_result_t result;
  uint32_t test_data[4] = {0};

  result = dif_otbn_imem_write(&dif_otbn_, 0xFFFFFFFC, test_data, 16);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET, test_data[0]);
  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 4, test_data[1]);

  dif_otbn_result_t result = dif_otbn_imem_write(&dif_otbn_, 0, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
}

TEST_F(ImemWriteTest, SuccessWithOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_WRITE32(OTBN_IMEM_REG_OFFSET + 8, test_data[1]);

  dif_otbn_result_t result = dif_otbn_imem_write(&dif_otbn_, 4, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
}

class ImemReadTest : public OtbnTest {};

TEST_F(ImemReadTest, NullArgs) {
  dif_otbn_result_t result;
  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  result = dif_otbn_imem_read(nullptr, 0, nullptr, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_read(nullptr, 0, test_data, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_read(&dif_otbn_, 0, nullptr, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  // No side effects are expected.
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(ImemReadTest, BadLenBytes) {
  dif_otbn_result_t result;
  uint32_t test_data[2] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  result = dif_otbn_imem_read(&dif_otbn_, 0, test_data, 1);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_read(&dif_otbn_, 0, test_data, 2);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemReadTest, BadOffset) {
  dif_otbn_result_t result;
  uint32_t test_data[2] = {0};

  // `offset` must be 32b-aligned.
  result = dif_otbn_imem_read(&dif_otbn_, 1, test_data, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_imem_read(&dif_otbn_, 2, test_data, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(ImemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_IMEM_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 4, 0xabcdef01);

  dif_otbn_result_t result = dif_otbn_imem_read(&dif_otbn_, 0, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(ImemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_IMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_READ32(OTBN_IMEM_REG_OFFSET + 8, 0xabcdef01);

  dif_otbn_result_t result = dif_otbn_imem_read(&dif_otbn_, 4, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

class DmemWriteTest : public OtbnTest {};

TEST_F(DmemWriteTest, NullArgs) {
  dif_otbn_result_t result;
  uint32_t test_data[1] = {0};

  result = dif_otbn_dmem_write(nullptr, 0, nullptr, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_write(nullptr, 0, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_write(&dif_otbn_, 0, nullptr, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(DmemWriteTest, BadLenBytes) {
  dif_otbn_result_t result;
  uint32_t test_data[1] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  result = dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 1);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 2);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(DmemWriteTest, BadOffset) {
  dif_otbn_result_t result;
  uint32_t test_data[1] = {0};

  // `offset` must be 32b-aligned.
  result = dif_otbn_dmem_write(&dif_otbn_, 1, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_write(&dif_otbn_, 2, test_data, 4);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(DmemWriteTest, SuccessWithoutOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET, test_data[0]);
  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 4, test_data[1]);

  dif_otbn_result_t result = dif_otbn_dmem_write(&dif_otbn_, 0, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
}

TEST_F(DmemWriteTest, SuccessWithOffset) {
  // Test assumption.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 4, test_data[0]);
  EXPECT_WRITE32(OTBN_DMEM_REG_OFFSET + 8, test_data[1]);

  dif_otbn_result_t result = dif_otbn_dmem_write(&dif_otbn_, 4, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
}

class DmemReadTest : public OtbnTest {};

TEST_F(DmemReadTest, NullArgs) {
  dif_otbn_result_t result;
  uint32_t test_data[2] = {0x12345678, 0xabcdef01};

  result = dif_otbn_dmem_read(nullptr, 0, nullptr, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_read(nullptr, 0, test_data, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_read(&dif_otbn_, 0, nullptr, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  // No side effects are expected.
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(DmemReadTest, BadLenBytes) {
  dif_otbn_result_t result;
  uint32_t test_data[2] = {0};

  // `len_bytes` must be a multiple of 4 bytes.
  result = dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 1);
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 2);
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(DmemReadTest, BadOffset) {
  dif_otbn_result_t result;
  uint32_t test_data[2] = {0};

  // `offset` must be 32b-aligned.
  result = dif_otbn_dmem_read(&dif_otbn_, 1, test_data, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);

  result = dif_otbn_dmem_read(&dif_otbn_, 2, test_data, sizeof(test_data));
  EXPECT_EQ(result, kDifOtbnBadArg);
}

TEST_F(DmemReadTest, SuccessWithoutOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 8);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_DMEM_REG_OFFSET, 0x12345678);
  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 4, 0xabcdef01);

  dif_otbn_result_t result = dif_otbn_dmem_read(&dif_otbn_, 0, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

TEST_F(DmemReadTest, SuccessWithOffset) {
  // Assumption in the test.
  ASSERT_GE(OTBN_DMEM_SIZE_BYTES, 12);

  uint32_t test_data[2] = {0};

  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 4, 0x12345678);
  EXPECT_READ32(OTBN_DMEM_REG_OFFSET + 8, 0xabcdef01);

  dif_otbn_result_t result = dif_otbn_dmem_read(&dif_otbn_, 4, test_data, 8);
  EXPECT_EQ(result, kDifOtbnOk);
  EXPECT_EQ(test_data[0], 0x12345678);
  EXPECT_EQ(test_data[1], 0xabcdef01);
}

}  // namespace
}  // namespace dif_otbn_unittest
