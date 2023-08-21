// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_log.h"

#include "sw/device/silicon_creator/lib/drivers/hmac.h"

static void boot_log_digest_compute(const boot_log_t *boot_log,
                                    hmac_digest_t *digest) {
  enum {
    kDigestRegionOffset = sizeof(boot_log->digest),
    kDigestRegionSize = sizeof(boot_log_t) - kDigestRegionOffset,
  };
  static_assert(offsetof(boot_log_t, digest) == 0,
                "`digest` must be the first field of `boot_log_t`.");
  hmac_sha256((const char *)boot_log + kDigestRegionOffset, kDigestRegionSize,
              digest);
}

void boot_log_digest_update(boot_log_t *boot_log) {
  boot_log_digest_compute(boot_log, &boot_log->digest);
}

/*
 * Shares for producing the `error` value in `boot_log_digest_check()`. First 8
 * shares are generated using the `sparse-fsm-encode` script while the last
 * share is `kErrorOk ^ kErrorBootLogInvalid^ kBootLogIdentifier ^
 * kCheckShares[0] ^ ... ^ kCheckShares[7]` so that xor'ing all shares with the
 * initial value of `error`, i.e. `kErrorBootLogInvalid`, and
 * `kBootLogIdentifier` produces `kErrorOk`.
 *
 * Encoding generated with:
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 8 -n 32 \
 *     -s 273200238 --language=c
 *
 * Minimum Hamming distance: 10
 * Maximum Hamming distance: 21
 * Minimum Hamming weight: 12
 * Maximum Hamming weight: 22
 */

static const uint32_t kCheckShares[kHmacDigestNumWords + 1] = {
    0x7b00d08e, 0xfdb69374, 0x336c86df, 0xff2ef417, 0xe1517012,
    0x4bf5408c, 0x9c6a7b25, 0xf771f8fa, 0xcd458605,
};

rom_error_t boot_log_check(const boot_log_t *boot_log) {
  static_assert(offsetof(boot_log_t, digest) == 0,
                "`digest` must be the first field of `boot_log_t`.");

  rom_error_t error = kErrorBootLogInvalid;
  hmac_digest_t actual_digest;
  boot_log_digest_compute(boot_log, &actual_digest);

  size_t i = 0;
  for (; launder32(i) < kHmacDigestNumWords; ++i) {
    error ^=
        boot_log->digest.digest[i] ^ actual_digest.digest[i] ^ kCheckShares[i];
  }
  HARDENED_CHECK_EQ(i, kHmacDigestNumWords);

  error ^= boot_log->identifier ^ kCheckShares[kHmacDigestNumWords];

  if (launder32(error) == kErrorOk) {
    HARDENED_CHECK_EQ(error, kErrorOk);
    return error;
  }

  return kErrorBootLogInvalid;
}
