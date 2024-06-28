// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kImmutableRomExtSectionHashSizeIn32BitWords =
      OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH_SIZE /
      sizeof(uint32_t),
  kSramValuePass = 0x53534150,  // PASS
};

OT_SECTION(".rom_ext_immutable")
void rom_ext_non_mutable(void) {
  // Print "Immutable" to the UART console.
  //                        l b a t u m m I
  const uint64_t kStr1 = 0x6c626174756d6d49;
  //                        e
  const uint32_t kStr2 = 0x65;
  const uint32_t kNewline = 0x0a0d;
  uart_write_imm(kStr1);
  uart_write_imm(kStr2);
  uart_write_imm(kNewline);

  // Set a magic value ("PASS") in retention SRAM.
  retention_sram_get()->owner.reserved[0] = kSramValuePass;

  return;
}

bool test_main(void) {
  uint32_t immutable_rom_ext_section_enabled =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN_OFFSET);
  LOG_INFO("Immutable ROM_EXT Enable OTP:       0x%08x",
           immutable_rom_ext_section_enabled);
  LOG_INFO(
      "Immutable ROM_EXT Start Offset OTP: 0x%08x",
      otp_read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_START_OFFSET_OFFSET));
  LOG_INFO("Immutable ROM_EXT Length OTP:       0x%08x",
           otp_read32(
               OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_LENGTH_OFFSET));
  uint32_t immutable_rom_ext_hash[kImmutableRomExtSectionHashSizeIn32BitWords];
  otp_read(OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_SHA256_HASH_OFFSET,
           immutable_rom_ext_hash, kImmutableRomExtSectionHashSizeIn32BitWords);
  LOG_INFO(
      "Immutable ROM_EXT Section Hash OTP: 0x%08x%08x%08x%08x%08x%08x%08x%08x",
      immutable_rom_ext_hash[7], immutable_rom_ext_hash[6],
      immutable_rom_ext_hash[5], immutable_rom_ext_hash[4],
      immutable_rom_ext_hash[3], immutable_rom_ext_hash[2],
      immutable_rom_ext_hash[1], immutable_rom_ext_hash[0]);

  // Check the immutabled section executed by reading out the retention SRAM.
  if (immutable_rom_ext_section_enabled == kHardenedBoolTrue) {
    CHECK(retention_sram_get()->owner.reserved[0] == kSramValuePass);
  }

  return true;
}
