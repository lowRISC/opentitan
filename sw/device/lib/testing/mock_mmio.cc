// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "mock_mmio.h"

void MmioMockTest::SetUp() {
  if (mock_ == nullptr) {
    // Using new because constructor is private
    mock_.reset(new MmioMock());
  }
}

void MmioMockTest::TearDown() {
  if (mock_ != nullptr) {
    // Destroy the mock object here to verify its expectations. Otherwise,
    // it is destroyed at program exit, i.e. we end up leaking it, and its
    // expectations are not verified.
    mock_.reset();
  }
}

thread_local std::unique_ptr<MmioMock> MmioMockTest::mock_;

extern "C" {
// Mock |reg32_read()| and |reg32_write()|
uint32_t reg32_read(reg32_t base, ptrdiff_t offset) {
  return MmioMockTest::mock_->MmioRead(base, offset);
}

void reg32_write(reg32_t base, ptrdiff_t offset, uint32_t value) {
  MmioMockTest::mock_->MmioWrite(base, offset, value);
}
}  // extern "C"