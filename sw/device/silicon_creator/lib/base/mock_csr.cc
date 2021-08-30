// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/base/mock_csr.h"

#include "sw/device/lib/base/csr.h"

namespace mock_csr {
extern "C" {

uint32_t mock_csr_read(uint32_t csr) { return MockCsr::Instance().Read(csr); }

void mock_csr_write(uint32_t csr, uint32_t value) {
  MockCsr::Instance().Write(csr, value);
}

void mock_csr_set_bits(uint32_t csr, uint32_t mask) {
  MockCsr::Instance().SetBits(csr, mask);
}

void mock_csr_clear_bits(uint32_t csr, uint32_t mask) {
  MockCsr::Instance().ClearBits(csr, mask);
}

}  // extern "C"
}  // namespace mock_csr
