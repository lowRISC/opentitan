// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"

#include <stddef.h>

#include "sw/device/silicon_creator/lib/drivers/hmac.h"

/**
 * Computes the digest of a boot services message.
 *
 * This function assumes that message payload starts immediately after the
 * header and is exactly `length - sizeof(boot_svc_header_t)` bytes.
 *
 * @param header Header of a boot services message.
 * @param[out] digest Output buffer for the digest.
 */
static void boot_svc_header_digest_compute(const boot_svc_header_t *header,
                                           hmac_digest_t *digest) {
  enum {
    kDigestRegionOffset = sizeof(header->digest),
  };
  static_assert(offsetof(boot_svc_header_t, digest) == 0,
                "`digest` must be the first field of `boot_svc_header_t`.");

  hmac_sha256((const char *)header + kDigestRegionOffset,
              header->length - kDigestRegionOffset, digest);
}

void boot_svc_header_finalize(uint32_t type, uint32_t length,
                              boot_svc_header_t *header) {
  header->identifier = kBootSvcIdentifier;
  header->type = type;
  header->length = length;
  boot_svc_header_digest_compute(header, &header->digest);
}

/**
 * Shares for producing the `error` value in `boot_svc_header_check()`. First 8
 * shares are used for checking the digest while the 9th and the 10th shares are
 * used during the length check. First 10 shares are generated using the
 * `sparse-fsm-encode` script while the last share is `kErrorOk ^
 * kErrorBootSvcBadHeader ^ kBootSvcIdentifier ^ kCheckDigestShares[0] ^ ... ^
 * kCheckDigestShares[7] ^ kCheckLengthShares[0] ^ kCheckLengthShares[1]` so
 * that xor'ing all shares with the initial value of `error`, i.e.
 * `kErrorBootSvcBadHeader`, and `kBootSvcIdentifier` produces `kErrorOk`.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 10 -n 32 \
 *     -s 1606528195 --language=c

 * Minimum Hamming distance: 9
 * Maximum Hamming distance: 22
 * Minimum Hamming weight: 12
 * Maximum Hamming weight: 18
 */
static const uint32_t kCheckShares[kHmacDigestNumWords + 3] = {
    0xc038253c, 0xfa1ebc13, 0x608b15e1, 0x883053ed, 0x3d28e980, 0x16009f6e,
    0xa7944bde, 0x3c096b6f, 0xe2828469, 0x2d507673, 0xefee6c10,
};

rom_error_t boot_svc_header_check(const boot_svc_header_t *header) {
  rom_error_t error = kErrorBootSvcBadHeader;
  hmac_digest_t digest;
  boot_svc_header_digest_compute(header, &digest);

  size_t i = 0;
  for (; launder32(i) < kHmacDigestNumWords; ++i) {
    error ^= header->digest.digest[i] ^ digest.digest[i] ^ kCheckShares[i];
  }

  if (launder32(header->length) >= CHIP_BOOT_SVC_MSG_HEADER_SIZE) {
    HARDENED_CHECK_GE(header->length, CHIP_BOOT_SVC_MSG_HEADER_SIZE);
    error ^= kCheckShares[i];
  }

  ++i;
  if (launder32(header->length) <= CHIP_BOOT_SVC_MSG_SIZE_MAX) {
    HARDENED_CHECK_LE(header->length, CHIP_BOOT_SVC_MSG_SIZE_MAX);
    error ^= kCheckShares[i];
  }

  error ^= header->identifier ^ kCheckShares[++i];
  if (launder32(error) == kErrorOk) {
    HARDENED_CHECK_EQ(error, kErrorOk);
    HARDENED_CHECK_EQ(i, ARRAYSIZE(kCheckShares) - 1);
    return error;
  }

  return kErrorBootSvcBadHeader;
}
