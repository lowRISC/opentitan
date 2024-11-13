// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <utility>

#include "absl/types/span.h"
#include "sw/device/silicon_creator/lib/bootstrap_fuzzer_util.h"
#include "sw/device/silicon_creator/rom_ext/bootstrap.h"

#include "otp_ctrl_regs.h"

namespace {
using bootstrap_fuzzer::AbstractBootstrapMockGroup;
using bootstrap_fuzzer::StreamParser;

class RomExtMockGroup : public AbstractBootstrapMockGroup {
 public:
  RomExtMockGroup(StreamParser stream, bool verbose)
      : AbstractBootstrapMockGroup(std::move(stream), verbose) {}

  void ConfigureMocks() override {
    AbstractBootstrapMockGroup::ConfigureMocks();

    ON_CALL(otp_,
            read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN_OFFSET))
        .WillByDefault(::testing::Return(stream_.ParseIntOr<hardened_bool_t>(
            "bootstrap_enabled", kHardenedBoolFalse)));
  }
};
}  // namespace

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  static bootstrap_fuzzer::StaticFuzzerEnvironment static_fuzzer_env;

  constexpr bool kVerbose = false;
  StreamParser stream(absl::MakeConstSpan(data, size), kVerbose);
  RomExtMockGroup mock_group(std::move(stream), kVerbose);
  mock_group.ConfigureMocks();

  (void)rom_ext_bootstrap();

  return 0;  // Values other than 0 and -1 are reserved for future use.
}
