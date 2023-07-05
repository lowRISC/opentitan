// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>
#include <type_traits>

#include "absl/types/optional.h"
#include "absl/types/span.h"
#include "gmock/gmock.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/bootstrap_unittest_util.h"
#include "sw/device/silicon_creator/lib/drivers/spi_device.h"
#include "sw/device/silicon_creator/rom_ext/bootstrap.h"

#include "flash_ctrl_regs.h"
#include "hw/ip/otp_ctrl/data/otp_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace {

// When `true`, the fuzzer will print the inputs it generates as human-readable
// strings. This is useful when debugging a crash, but is unnecessary overhead
// during exploratory fuzzing.
constexpr bool kVerbose = false;

void Crash() { __builtin_trap(); }

class StreamParser {
 public:
  // For speed, the constructor does not make a copy of `data`. Ensure that
  // `data` points to memory that outlives `this`.
  StreamParser(absl::Span<const uint8_t> data) : data_(data) {}

  // This method attempts to parse a `spi_device_cmd_t`. If there are not enough
  // bytes, it returns the value of `ResetCmd()`. When `kVerbose` is true, it
  // writes an informative message to stdout.
  spi_device_cmd_t ParseCmdOr(spi_device_cmd_t default_value) {
    const spi_device_cmd_t cmd = ParseCmd().value_or(default_value);
    if (kVerbose) {
      std::cout << std::hex << "Parsed spi_device_cmd_t: {"
                << "opcode=0x" << cmd.opcode << ", address=0x" << cmd.address
                << ", payload_byte_count=0x" << cmd.payload_byte_count << "}"
                << std::endl;
    }
    return cmd;
  }

  // This method attempts to parse an `IntType` from the stream. If there are
  // not enough bytes, it returns `default_value`. When `kVerbose` is true, it
  // uses `log_label` to write an informative message to stdout.
  template <typename IntType>
  IntType ParseIntOr(const char *log_label, IntType default_value) {
    const IntType value = ParseInt<IntType>().value_or(default_value);
    if (kVerbose) {
      std::cout << "Parsed " << log_label << ": 0x" << std::hex << value
                << std::endl;
    }
    return value;
  }

 private:
  template <typename IntType>
  absl::optional<IntType> ParseInt() {
    static_assert(
        std::is_integral<IntType>::value || std::is_enum<IntType>::value,
        "IntType must be an integral or enum type");
    if (data_.length() < sizeof(IntType)) {
      return absl::nullopt;
    }
    IntType n;
    memcpy(&n, data_.data(), sizeof(IntType));
    data_ = data_.subspan(sizeof(IntType));
    return n;
  }

  absl::optional<spi_device_cmd_t> ParseCmd() {
    auto opcode = ParseInt<uint8_t>();
    auto address = ParseInt<uint32_t>();
    auto payload_byte_count = ParseInt<size_t>();
    if (!opcode || !address || !payload_byte_count) {
      return absl::nullopt;
    }
    const spi_device_cmd_t cmd{
        .opcode = static_cast<spi_device_opcode_t>(*opcode & UINT8_MAX),
        .address = *address,
        .payload_byte_count =
            *payload_byte_count % (kSpiDevicePayloadAreaNumBytes + 1),
    };
    return cmd;
  }

  absl::Span<const uint8_t> data_;
};

class SpiFlashFuzzContext {
 public:
  void Fuzz(StreamParser stream);

  ::rom_test::NiceMockSpiDevice spi_device_;
  ::rom_test::NiceMockRstmgr rstmgr_;
  ::rom_test::NiceMockFlashCtrl flash_ctrl_;
  ::rom_test::NiceMockOtp otp_;
};

void SpiFlashFuzzContext::Fuzz(StreamParser stream) {
  using ::testing::_;
  using ::testing::Return;

  ON_CALL(flash_ctrl_, DataErase(_, _)).WillByDefault(Return(kErrorOk));

  ON_CALL(flash_ctrl_, DataWrite(_, _, _)).WillByDefault(Return(kErrorOk));

  ON_CALL(flash_ctrl_, DataEraseVerify(_, _)).WillByDefault(Return(kErrorOk));

  ON_CALL(otp_, read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN_OFFSET))
      .WillByDefault(Return(stream.ParseIntOr<hardened_bool_t>(
          "bootstrap_enabled", kHardenedBoolFalse)));

  ON_CALL(rstmgr_, ReasonGet()).WillByDefault([&] {
    return stream.ParseIntOr<uint32_t>(
        "reset_reason",
        1 << kRstmgrReasonPowerOn | 1 << kRstmgrReasonSoftwareRequest);
  });

  // It's possible that the bootstrap code will get stuck in a loop asking for
  // new SPI commands. The bootstrap loop will ignore RESET commands unless it
  // has first seen an erase command. It will also ignore RESET commands unless
  // the flash status's WEL bit is enabled.

  const size_t max_spi_cmd_count =
      (stream.ParseIntOr<size_t>("max_spi_cmd_count", 1024) % 1024) + 16;
  if (kVerbose) {
    std::cout << "Clamped max_spi_cmd_count: " << max_spi_cmd_count
              << std::endl;
  }

  bool flash_status_override = false;
  ON_CALL(spi_device_, FlashStatusGet()).WillByDefault([&] {
    return flash_status_override
               ? uint32_t{1 << kSpiDeviceWelBit}
               : stream.ParseIntOr<uint32_t>("flash_status", 0);
  });

  size_t spi_cmd_count = 0;
  ON_CALL(spi_device_, CmdGet(testing::NotNull()))
      .WillByDefault([&](spi_device_cmd_t *cmd) -> rom_error_t {
        spi_cmd_count++;

        if (spi_cmd_count < max_spi_cmd_count) {
          *cmd = stream.ParseCmdOr(bootstrap_unittest_util::ChipEraseCmd());
          return kErrorOk;
        }
        if (spi_cmd_count == max_spi_cmd_count) {
          *cmd = bootstrap_unittest_util::ChipEraseCmd();
          flash_status_override = true;
          if (kVerbose) {
            std::cout << "Attempting to end session: CHIP_ERASE" << std::endl;
          }
          return kErrorOk;
        }
        if (spi_cmd_count == max_spi_cmd_count + 1) {
          *cmd = bootstrap_unittest_util::ResetCmd();
          if (kVerbose) {
            std::cout << "Attempting to end session: RESET" << std::endl;
          }
          return kErrorOk;
        }

        // We've already synthesized CHIP_ERASE and RESET commands, so the
        // bootstrap code should not have requested another SPI command.
        Crash();
        return kErrorUnknown;
      });

  (void)rom_ext_bootstrap();
}
}  // namespace

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  // Only initialize the environment once.
  static struct FuzzerEnvironment {
    FuzzerEnvironment() { testing::InitGoogleMock(); }
  } env;

  SpiFlashFuzzContext fuzz_context;
  StreamParser stream(absl::MakeSpan(data, size));
  fuzz_context.Fuzz(stream);

  return 0;  // Values other than 0 and -1 are reserved for future use.
}
