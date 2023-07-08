// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/mock_boot_svc_header.h"

namespace rom_test {
extern "C" {
void boot_svc_header_finalize(uint32_t type, uint32_t length,
                              boot_svc_header_t *header) {
  MockBootSvcHeader::Instance().Finalize(type, length, header);
}
}
}  // namespace rom_test
