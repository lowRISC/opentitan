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

const size_t kGoldenRomSizeBytes = 32652 - sizeof(build_info_t);
const uint32_t kSimDvGoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0x25c5b824, 0x428a20dc, 0xc139cfb8, 0xb0b03a5a,
    0xda61df49, 0x00bdab5f, 0x565f383e, 0x58234921,
};
const uint32_t kFpgaCw310GoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0x036c3e10, 0xd1add4c5, 0x24574287, 0x4f50c492,
    0x3f0feb73, 0xdeb18dd4, 0xb453d84c, 0x573e0d1f,
};
const uint32_t kSiliconGoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0x5eb4c370, 0xddec31a1, 0xe73816f2, 0x7ee119d1,
    0xac8c89a5, 0x198ce068, 0xca885ef2, 0x4f41f620,
};

extern const char _chip_info_start[];

// We hash the ROM using the SHA256 algorithm and print the hash to the console.
status_t hash_rom(void) {
  hmac_digest_t rom_hash;
  hmac_sha256((void *)TOP_EARLGREY_ROM_BASE_ADDR, kGoldenRomSizeBytes,
              &rom_hash);
  // Use printf directly here instead of the `LOG()` macros which print extra
  // filenames and line numbers which bloat DV and GLS runtimes.
  // DO NOT MODIFY the printf immediately below without modifying the check in
  // `hw/top_earlgrey/dv/env/seq_lib/chip_sw_rom_e2e_self_hash_gls_vseq.sv`
  base_printf("ROM Hash: 0x%08x%08x%08x%08x%08x%08x%08x%08x\r\n",
              rom_hash.digest[7], rom_hash.digest[6], rom_hash.digest[5],
              rom_hash.digest[4], rom_hash.digest[3], rom_hash.digest[2],
              rom_hash.digest[1], rom_hash.digest[0]);
  build_info_t *rom_build_info = (build_info_t *)_chip_info_start;
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
