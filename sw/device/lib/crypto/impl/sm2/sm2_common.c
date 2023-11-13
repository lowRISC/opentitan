// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/sm2/sm2_common.h"

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
       (ksm2MaskedScalarShareWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
};

status_t sm2_masked_scalar_write(const sm2_masked_scalar_t *src,
                                  const otbn_addr_t share0_addr,
                                  const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(ksm2MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(ksm2MaskedScalarShareWords, src->share1, share1_addr));

  // Write trailing 0s so that OTBN's 256-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + ksm2MaskedScalarShareBytes));
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share1_addr + ksm2MaskedScalarShareBytes));

  return OTCRYPTO_OK;
}
