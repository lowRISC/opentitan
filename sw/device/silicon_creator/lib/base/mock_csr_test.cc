// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/mock_csr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/csr.h"

namespace mock_csr_test {
class MockCsrTest : public testing::Test {
 protected:
  mock_csr::MockCsr csr_;
};

TEST_F(MockCsrTest, Read) {
  EXPECT_CSR_READ(CSR_REG_PMPCFG0, 1);
  uint32_t value;
  CSR_READ(CSR_REG_PMPCFG0, &value);
  EXPECT_EQ(value, 1);
}

TEST_F(MockCsrTest, Write) {
  EXPECT_CSR_WRITE(CSR_REG_PMPADDR0, 0x100);
  CSR_WRITE(CSR_REG_PMPADDR0, 0x100);
}

TEST_F(MockCsrTest, Set) {
  EXPECT_CSR_SET_BITS(CSR_REG_PMPCFG0, 0x1);
  CSR_SET_BITS(CSR_REG_PMPCFG0, 0x1);
}

TEST_F(MockCsrTest, Clear) {
  EXPECT_CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0x1);
  CSR_CLEAR_BITS(CSR_REG_PMPCFG0, 0x1);
}

}  // namespace mock_csr_test
