// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sm2/p256_common.h"

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
       (kP256MaskedScalarShareWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
};

status_t p256_masked_scalar_write(const p256_masked_scalar_t *src,
                                  const otbn_addr_t share0_addr,
                                  const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(kP256MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(kP256MaskedScalarShareWords, src->share1, share1_addr));

  // Write trailing 0s so that OTBN's 256-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + kP256MaskedScalarShareBytes));
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share1_addr + kP256MaskedScalarShareBytes));

  return OTCRYPTO_OK;
}
