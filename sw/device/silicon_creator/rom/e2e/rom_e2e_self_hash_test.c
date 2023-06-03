// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

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
 * 2. Query and update the ROM size below (`kGoldenRomSizeBytes`) with:
 *    `stat -c %s <path to *.bin>`
 *
 * 3. Compute and update the golden ROM hashes below (`k*GoldenRomHash`) with:
 *    `sha256sum <path to *.bin>`
 *    Note, make sure to reverse the byte order so order is little endian.
 */
const size_t kGoldenRomSizeBytes = 32648;
const uint32_t kSimDvGoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0xa89b5d02, 0x45ac9691, 0x37ecafa7, 0x3feb8e85,
    0x8856d902, 0x36012a3e, 0x11ca064b, 0xa5358f02,
};
const uint32_t kFpgaCw310GoldenRomHash[kSha256HashSizeIn32BitWords] = {
    0x40e52a49, 0x81729b5d, 0x05f8221f, 0xab685ed2,
    0xec153ccc, 0xf372b97f, 0x8f9136bc, 0x0ce5576f,
};

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

  TRY_CHECK(otcrypto_hash(input, kHashModeSha256, &output) == kCryptoStatusOK);
  LOG_INFO("ROM Hash: 0x%!x", kSha256HashSizeInBytes, rom_hash);
  if (kDeviceType == kDeviceSimDV) {
    TRY_CHECK_ARRAYS_EQ((uint8_t *)output.data, (uint8_t *)kSimDvGoldenRomHash,
                        sizeof(kSimDvGoldenRomHash));
  } else if (kDeviceType == kDeviceFpgaCw310) {
    TRY_CHECK_ARRAYS_EQ((uint8_t *)output.data,
                        (uint8_t *)kFpgaCw310GoldenRomHash,
                        sizeof(kFpgaCw310GoldenRomHash));
  } else {
    LOG_WARNING("ROM hash not self-checked for this device type: 0x%x",
                kDeviceType);
  }

  return OK_STATUS();
};

bool test_main(void) {
  status_t test_result = OK_STATUS();
  EXECUTE_TEST(test_result, hash_rom);
  return status_ok(test_result);
}
