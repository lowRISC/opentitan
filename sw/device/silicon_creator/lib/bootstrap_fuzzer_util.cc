// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/bootstrap_fuzzer_util.h"

#include <iostream>
#include <stddef.h>
#include <stdint.h>
#include <type_traits>
#include <utility>

#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/bootstrap_unittest_util.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_spi_device.h"

#include "flash_ctrl_regs.h"
#include "hw/ip/otp_ctrl/data/otp_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace bootstrap_fuzzer {

namespace {
void Crash() { __builtin_trap(); }
}  // namespace

StaticFuzzerEnvironment::StaticFuzzerEnvironment() {
  testing::InitGoogleMock();
}

AbstractBootstrapMockGroup::AbstractBootstrapMockGroup(StreamParser stream,
                                                       bool verbose)
    : verbose_(verbose), stream_(std::move(stream)) {}

void AbstractBootstrapMockGroup::ConfigureMocks() {
  using ::testing::_;
  using ::testing::Return;

  ON_CALL(flash_ctrl_, DataErase(_, _)).WillByDefault(Return(kErrorOk));
  ON_CALL(flash_ctrl_, DataWrite(_, _, _)).WillByDefault(Return(kErrorOk));
  ON_CALL(flash_ctrl_, DataEraseVerify(_, _)).WillByDefault(Return(kErrorOk));

  ON_CALL(rstmgr_, ReasonGet()).WillByDefault([&] {
    return stream_.ParseIntOr<uint32_t>(
        "reset_reason",
        1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);
  });

  // It's possible that the bootstrap code will get stuck in a loop asking for
  // new SPI commands. The bootstrap loop will ignore RESET commands unless it
  // has first seen an erase command. It will also ignore RESET commands unless
  // the flash status's WEL bit is enabled.

  max_spi_cmd_count_ =
      (stream_.ParseIntOr<size_t>("max_spi_cmd_count_", 1024) % 1024) + 16;
  if (verbose_) {
    std::cout << "Clamped max_spi_cmd_count_: " << max_spi_cmd_count_
              << std::endl;
  }

  ON_CALL(spi_device_, FlashStatusGet()).WillByDefault([&] {
    return flash_status_override_
               ? uint32_t{1 << kSpiDeviceWelBit}
               : stream_.ParseIntOr<uint32_t>("flash_status", 0);
  });

  ON_CALL(spi_device_, CmdGet(testing::NotNull()))
      .WillByDefault([&](spi_device_cmd_t *cmd) -> rom_error_t {
        spi_cmd_count_++;

        if (spi_cmd_count_ < max_spi_cmd_count_) {
          *cmd = stream_.ParseCmdOr(bootstrap_unittest_util::ChipEraseCmd());
          return kErrorOk;
        }
        if (spi_cmd_count_ == max_spi_cmd_count_) {
          *cmd = bootstrap_unittest_util::ChipEraseCmd();
          flash_status_override_ = true;
          if (verbose_) {
            std::cout << "Attempting to end session: CHIP_ERASE" << std::endl;
          }
          return kErrorOk;
        }
        if (spi_cmd_count_ == max_spi_cmd_count_ + 1) {
          *cmd = bootstrap_unittest_util::ResetCmd();
          if (verbose_) {
            std::cout << "Attempting to end session: RESET" << std::endl;
          }
          return kErrorOk;
        }

        // We've already synthesized CHIP_ERASE and RESET commands, so the
        // bootstrap code should not have requested another SPI command.
        Crash();
        return kErrorUnknown;
      });
}

}  // namespace bootstrap_fuzzer
