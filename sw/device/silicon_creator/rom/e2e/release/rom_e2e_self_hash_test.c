// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/build_info.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

OTTF_DEFINE_TEST_CONFIG(.silence_console_prints = true);

enum {
  // Hash size.
  kSha256HashSizeInBits = 256,
  kSha256HashSizeInBytes = kSha256HashSizeInBits / 8,
  kSha256HashSizeIn32BitWords = kSha256HashSizeInBytes / 4,
};

/**
 * The golden ROM size and hashes expected below are generated using the
 * following instructions. If the ROM is updated, these values must also be
 * updated to prevent CI failures.
 *
 * 1. Build the ROM and query the ROM hashes:
 *    bazel build //sw/device/silicon_creator/rom:rom_hashes
 *    cat bazel-bin/sw/device/silicon_creator/rom/rom_hashes.txt
 *
 * 2. Update the size and golden ROM hashes below (`k*GoldenRomHash`) by
 *    copying the little-endian-32 value arrays from the `rom_hashes.txt`
 *    report.
 */

// Fetch from the linker script: the start of the `.chip_info` region, which
// occupies the top `_chip_info_size` bytes of ROM and the `.chip_info` size.
// Note: `_rom_chip_info_start` + `_chip_info_size` is equal to
//       TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES
extern const char _rom_chip_info_start[];
extern const char _chip_info_size[];

// `rom_hashes.txt` reports the hash of the ROM image with `build_info`
// stripped off, which is everything below `.chip_info`. Calculate the
// hashable size by substracting the ROM base address from the start of
// `.chip_info`.
const size_t kGoldenRomSizeBytes =
    (size_t)_rom_chip_info_start - TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR;
const uint32_t kSimDvGoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0xaf951ef4, 0x0335bd5a, 0x980905d7, 0xd2656121,
    0xe19922cf, 0xdcbbb2bf, 0x58ae053a, 0x0dc03d2d,
};
const uint32_t kFpgaCw310GoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0x03dff5d4, 0xf782776b, 0x56b8e7ac, 0xbeaa8f1a,
    0x606aff59, 0x62a47652, 0x1fe8655a, 0x41a966a7,
};
const uint32_t kSiliconGoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0xedef8122, 0x1d3cf7d0, 0x1ffbe06c, 0x6c32788d,
    0x3a96929d, 0x217ff978, 0xafc69dfb, 0x9b533921,
};

// We hash the ROM using the SHA256 algorithm and print the hash to the console.
status_t hash_rom(void) {
  hmac_digest_t rom_hash;

  // The hashed range must be exactly the ROM size minus the `.chip_info`
  // region.
  TRY_CHECK(kGoldenRomSizeBytes + (size_t)_chip_info_size ==
                (size_t)TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES,
            "Golden ROM size %u + chip_info size %u != ROM size %u",
            kGoldenRomSizeBytes, (size_t)_chip_info_size,
            (size_t)TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES);

  hmac_sha256((void *)TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR, kGoldenRomSizeBytes,
              &rom_hash);
  // Use printf directly here instead of the `LOG()` macros which print extra
  // filenames and line numbers which bloat DV and GLS runtimes.
  // DO NOT MODIFY the printf immediately below without modifying the check in
  // `hw/top_earlgrey/dv/env/seq_lib/chip_sw_rom_e2e_self_hash_gls_vseq.sv`
  base_printf("ROM Hash: 0x%08x%08x%08x%08x%08x%08x%08x%08x\r\n",
              rom_hash.digest[7], rom_hash.digest[6], rom_hash.digest[5],
              rom_hash.digest[4], rom_hash.digest[3], rom_hash.digest[2],
              rom_hash.digest[1], rom_hash.digest[0]);
  build_info_t *rom_build_info = (build_info_t *)_rom_chip_info_start;
  LOG_INFO("rom_build_info @ %p:", rom_build_info);
  LOG_INFO("scm_revision = %08x%08x",
           rom_build_info->scm_revision.scm_revision_high,
           rom_build_info->scm_revision.scm_revision_low);
  LOG_INFO("version = %08x", rom_build_info->version);

  // TODO(#18868) Add checks for the build_info values we expect to see in the
  // released ROM binary.

  if (kDeviceType == kDeviceSimDV) {
    TRY_CHECK_ARRAYS_EQ(rom_hash.digest, kSimDvGoldenRomHash,
                        ARRAYSIZE(kSimDvGoldenRomHash));
  } else if (kDeviceType == kDeviceFpgaCw310) {
    TRY_CHECK_ARRAYS_EQ(rom_hash.digest, kFpgaCw310GoldenRomHash,
                        ARRAYSIZE(kFpgaCw310GoldenRomHash));
  } else if (kDeviceType == kDeviceSilicon) {
    TRY_CHECK_ARRAYS_EQ(rom_hash.digest, kSiliconGoldenRomHash,
                        ARRAYSIZE(kSiliconGoldenRomHash));
  } else {
    LOG_ERROR("ROM hash not self-checked for this device type: 0x%x",
              kDeviceType);
    return INTERNAL();
  }

  return OK_STATUS();
};

bool test_main(void) { return status_ok(hash_rom()); }
