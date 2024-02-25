// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_spi_host.h"

namespace rom_test {
extern "C" {

void spi_host_init(uint32_t precalculated_div) {
  MockSpiHost::Instance().Init(precalculated_div);
}

rom_error_t spi_host_transaction(uint32_t csid,
                                 const spi_host_segment_t *segments,
                                 size_t length) {
  return MockSpiHost::Instance().Transaction(csid, segments, length);
}

}  // extern "C"
}  // namespace rom_test
