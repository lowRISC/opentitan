// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/chip_info.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  // Hash size.
  kSha256HashSizeInBits = 256,
  kSha256HashSizeInBytes = kSha256HashSizeInBits / 8,
  kSha256HashSizeIn32BitWords = kSha256HashSizeInBytes / 4,
};

// TODO(#18686): replace with real golden hashes (when real keys are generated).
/**
 * The golden ROM size and hashes expected below are generated using the
 * following instructions. If the ROM is updated, these values must also be
 * updated to prevent CI failures.
 *
 * 1. Build the ROM with Bazel using:
 *    `bazel build //sw/device/silicon_creator/rom:rom_with_real_keys`
 *    Note, this will build a separate ROM binary for each device, that can both
 *    be located with `./bazelisk.sh outquery-all
 *    //sw/device/silicon_creator/rom:rom_with_real_keys`, including:
 *    a. one for DV simulations: "rom_with_real_keys_sim_dv.bin", and
 *    b. one for CW310 FPGA: "rom_with_real_keys_fpga_cw310.bin".
 *
 * 2. Query the ROM hashes:
 *    bazel build //sw/device/silicon_creator/rom:rom_hashes
 *    cat bazel-bin/sw/device/silicon_creator/rom/rom_hashes.txt
 *
 * 3. Update the size and golden ROM hashes below (`k*GoldenRomHash`) by
 *    copying the little-endian-32 value arrays from the `rom_hashes.txt`
 *    report.
 */

const size_t kGoldenRomSizeBytes = 32652 - sizeof(chip_info_t);
const uint32_t kSimDvGoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0x76238644, 0x6509c464, 0x5a598a36, 0xe74a800b,
    0x4069c647, 0x3eaf3a88, 0x96797302, 0x96993d2e,
};
const uint32_t kFpgaCw310GoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0xeac888af, 0x1f12fade, 0xc0960031, 0xcdf14768,
    0xfb797390, 0xea6c738b, 0xc47ae33e, 0xd54af879,
};

extern const char _chip_info_start[];

// We hash the ROM using the SHA256 algorithm and print the hash to the console.
status_t hash_rom(void) {
  uint32_t rom_hash[kSha256HashSizeIn32BitWords];
  crypto_const_uint8_buf_t input = {
      .data = (uint8_t *)TOP_EARLGREY_ROM_BASE_ADDR,
      .len = kGoldenRomSizeBytes,
  };
  crypto_uint8_buf_t output = {
      .data = (uint8_t *)rom_hash,
      .len = kSha256HashSizeInBytes,
  };

  TRY(otcrypto_hash(input, kHashModeSha256, &output));
  LOG_INFO("ROM Hash: 0x%!x", kSha256HashSizeInBytes, rom_hash);
  chip_info_t *rom_chip_info = (chip_info_t *)_chip_info_start;
  LOG_INFO("rom_chip_info @ %p:", rom_chip_info);
  LOG_INFO("scm_revision = %08x%08x",
           rom_chip_info->scm_revision.scm_revision_high,
           rom_chip_info->scm_revision.scm_revision_low);
  LOG_INFO("version = %08x", rom_chip_info->version);

  // TODO(#18868) Add checks for the chip_info values we expect to see in the
  // released ROM binary.

  if (kDeviceType == kDeviceSimDV) {
    TRY_CHECK_ARRAYS_EQ((uint8_t *)output.data, (uint8_t *)kSimDvGoldenRomHash,
                        sizeof(kSimDvGoldenRomHash));
  } else if (kDeviceType == kDeviceFpgaCw310) {
    TRY_CHECK_ARRAYS_EQ((uint8_t *)output.data,
                        (uint8_t *)kFpgaCw310GoldenRomHash,
                        sizeof(kFpgaCw310GoldenRomHash));
  } else {
    LOG_ERROR("ROM hash not self-checked for this device type: 0x%x",
              kDeviceType);
    return INTERNAL();
  }

  return OK_STATUS();
};

bool test_main(void) {
  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, hash_rom);
  return status_ok(test_result);
}
