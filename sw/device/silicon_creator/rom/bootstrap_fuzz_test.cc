// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <utility>

#include "absl/types/span.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/bootstrap_fuzzer_util.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"

#include "gpio_regs.h"
#include "hw/ip/otp_ctrl/data/otp_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace {
using bootstrap_fuzzer::AbstractBootstrapMockGroup;
using bootstrap_fuzzer::StreamParser;

class RomMockGroup : public AbstractBootstrapMockGroup {
 public:
  RomMockGroup(StreamParser stream, bool verbose)
      : AbstractBootstrapMockGroup(std::move(stream), verbose) {}

  void ConfigureMocks() override {
    AbstractBootstrapMockGroup::ConfigureMocks();

    ON_CALL(otp_, read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET))
        .WillByDefault(::testing::Return(stream_.ParseIntOr<hardened_bool_t>(
            "bootstrap_enabled", kHardenedBoolFalse)));

    ON_CALL(mmio_,
            Read32(TOP_EARLGREY_GPIO_BASE_ADDR + GPIO_DATA_IN_REG_OFFSET))
        .WillByDefault(
            ::testing::Return(stream_.ParseIntOr<uint32_t>("strapping", 0)));
  }

 private:
  ::rom_test::NiceMockAbsMmio mmio_;
};
}  // namespace

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  static bootstrap_fuzzer::StaticFuzzerEnvironment static_fuzzer_env;

  constexpr bool kVerbose = false;
  StreamParser stream(absl::MakeConstSpan(data, size), kVerbose);
  RomMockGroup mock_group(std::move(stream), kVerbose);
  mock_group.ConfigureMocks();

  (void)bootstrap();

  return 0;  // Values other than 0 and -1 are reserved for future use.
}
