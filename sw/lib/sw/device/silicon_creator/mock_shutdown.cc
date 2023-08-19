// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/mock_shutdown.h"

namespace rom_test {
extern "C" {
shutdown_error_redact_t shutdown_redact_policy(void) {
  return MockShutdown::Instance().RedactPolicy();
}

uint32_t shutdown_redact(rom_error_t reason, shutdown_error_redact_t severity) {
  return MockShutdown::Instance().Redact(reason, severity);
}

void shutdown_finalize(rom_error_t reason) {
  return MockShutdown::Instance().Finalize(reason);
}
}  // extern "C"
}  // namespace rom_test
