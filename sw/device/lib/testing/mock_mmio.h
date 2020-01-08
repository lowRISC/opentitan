// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gmock/gmock.h"
#include "gtest/gtest.h"

extern "C" {
#include "sw/device/lib/base/mmio.h"
}  // extern "C"

// Class for mocking |reg32_read()| and |reg32_write()|.
// This class should only be used by MmioMockTest and
// the private constructor expresses this expectation.
class MmioMock {
 public:
  MOCK_METHOD(uint32_t, MmioRead, (reg32_t, ptrdiff_t));
  MOCK_METHOD(void, MmioWrite, (reg32_t, ptrdiff_t, uint32_t));

 private:
  MmioMock() = default;

  friend class MmioMockTest;
};

// Fixture for constructing and destroying a static MmioMock instance
// that can be used from |reg32_read()| and |reg32_write()| mocks.
class MmioMockTest : public testing::Test {
 protected:
  void SetUp() override;
  void TearDown() override;

  // Static mock instance
  thread_local static std::unique_ptr<MmioMock> mock_;

  // Friends to be able to redispatch calls to MmioMock
  friend uint32_t reg32_read(reg32_t, ptrdiff_t);
  friend void reg32_write(reg32_t, ptrdiff_t, uint32_t);

 private:
  testing::InSequence expectationSequence_;
};

// Equal to operator to able to use reg32_t in expectations
inline bool operator==(const reg32_t &lhs, const reg32_t &rhs) {
  return lhs.inner_ptr == rhs.inner_ptr;
}

// Helper macros for passing |*mock_| to |EXPECT_CALL|. Tests must use the
// |MmioMockTest| fixture defined above. These are not defined as member
// functions because error messages would end up pointing to this file,
// which is not very helpful.
#define EXPECT_MMIO_WRITE(addr, offset, val) \
  EXPECT_CALL(*mock_, MmioWrite(addr, offset, val))
#define EXPECT_MMIO_READ(addr, offset, val) \
  EXPECT_CALL(*mock_, MmioRead(addr, offset)).WillOnce(::testing::Return(val))
