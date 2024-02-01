// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p384_common.h"

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/status.h"

enum {
  /**
   * Number of extra padding words needed for masked scalar shares.
   *
   * Where W is the word size and S is the share size, the padding needed is:
   *   (W - (S % W)) % W
   *
   * The extra outer "% W" ensures that the padding is 0 if (S % W) is 0.
   */
  kMaskedScalarPaddingWords =
      (kOtbnWideWordNumWords -
       (kP384MaskedScalarShareWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
};

status_t p384_masked_scalar_write(const p384_masked_scalar_t *src,
                                  const otbn_addr_t share0_addr,
                                  const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(kP384MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(kP384MaskedScalarShareWords, src->share1, share1_addr));

  // Write trailing 0s so that OTBN's 384-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + kP384MaskedScalarShareBytes));
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share1_addr + kP384MaskedScalarShareBytes));

  return OTCRYPTO_OK;
}

status_t set_message_digest(const uint32_t digest[kP384ScalarWords],
                            const otbn_addr_t kOtbnVarEcdsaMsg) {
  // Set the message digest. We swap all the bytes so that OTBN can interpret
  // the digest as a little-endian integer, which is a more natural fit for the
  // architecture than the big-endian form requested by the specification (FIPS
  // 186-5, section B.2.1).
  uint32_t digest_little_endian[kP384ScalarWords];
  size_t i = 0;
  for (; launder32(i) < kP384ScalarWords; i++) {
    digest_little_endian[i] =
        __builtin_bswap32(digest[kP384ScalarWords - 1 - i]);
  }
  HARDENED_CHECK_EQ(i, kP384ScalarWords);
  return otbn_dmem_write(kP384ScalarWords, digest_little_endian,
                         kOtbnVarEcdsaMsg);
}
