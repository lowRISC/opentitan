// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_CSR_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_CSR_H_

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/testing/mask_rom_test.h"

namespace mock_csr {

namespace internal {

class MockCsr {
 public:
  MOCK_METHOD(uint32_t, Read, (uint32_t csr));
  MOCK_METHOD(void, Write, (uint32_t csr, uint32_t value));
  MOCK_METHOD(void, SetBits, (uint32_t csr, uint32_t mask));
  MOCK_METHOD(void, ClearBits, (uint32_t csr, uint32_t mask));
  virtual ~MockCsr() {}
};
}  // namespace internal

using MockCsr =
    ::mask_rom_test::GlobalMock<testing::StrictMock<internal::MockCsr>>;

/**
 * Conveninence fixture for creating CSR tests.
 *
 * This class should be derived by a test fixture (along with `testing::Test`)
 * and used in a `TEST_F` block. Doing so will make the `EXPECT_CSR_*`
 * convenience macros useable.
 *
 * TODO: should this be composable with MmioTest and/or MaskRomTest?
 */
class CsrTest {
 private:
  MockCsr csr_;
  testing::InSequence seq_;
};

}  // namespace mock_csr

/**
 * Expect a read of the provided CSR.
 *
 * The tested code must use `CSR_READ(csr, dest)`.
 *
 * @param csr The CSR that will be read. Note: does
 * not need to be constant.
 * @param value The value to return from the read operation.
 */
#define EXPECT_CSR_READ(csr, value)                       \
  EXPECT_CALL(::mock_csr::MockCsr::Instance(), Read(csr)) \
      .WillOnce(::testing::Return(value))

/**
 * Expect a write to the provided CSR.
 *
 * The tested code must use `CSR_WRITE(csr, value)`.
 *
 * @param csr The CSR that will be written to.
 * Note: does not need to be constant.
 * @param value The value that is expected to be written to the CSR.
 */
#define EXPECT_CSR_WRITE(csr, value) \
  EXPECT_CALL(::mock_csr::MockCsr::Instance(), Write(csr, value))

/**
 * Expect a set masked bits operation on the provided CSR.
 *
 * The tested code must use `CSR_SET_BITS(csr, mask)`
 *
 * @param csr The CSR that will be targeted. Note:
 * does not need to be constant.
 * @param mask The expected mask containing the bits to set.
 */
#define EXPECT_CSR_SET_BITS(csr, mask) \
  EXPECT_CALL(::mock_csr::MockCsr::Instance(), SetBits(csr, mask))

/**
 * Expect a clear masked bits operation on the provided CSR.
 *
 * The tested code must use `CSR_CLEAR_BITS(csr, mask)`.
 *
 * @param csr The CSR that will be targeted. Note:
 * does not need to be constant.
 * @param mask The expected mask containing the bits to clear.
 */
#define EXPECT_CSR_CLEAR_BITS(csr, mask) \
  EXPECT_CALL(::mock_csr::MockCsr::Instance(), ClearBits(csr, mask))

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_MOCK_CSR_H_
