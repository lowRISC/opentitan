// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/prng_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/crypto/cryptotest/json/prng_sca_commands.h"

/**
 * Seed PRNG command handler.
 *
 * Seed the SCA internal PRNG. Only 4-byte seeds are supported.
 * The uJSON data contains:
 *  - seed: A buffer holding the seed.
 *  - seed_len: Seed length.
 *
 * @param uj The received uJSON data.
 */
status_t handle_prng_sca_seed_prng(ujson_t *uj) {
  cryptotest_prng_sca_lfsr_t uj_data;
  TRY(ujson_deserialize_cryptotest_prng_sca_lfsr_t(uj, &uj_data));

  if (uj_data.seed_length != sizeof(uint32_t)) {
    return OUT_OF_RANGE();
  }
  prng_seed(read_32(uj_data.seed));

  return OK_STATUS(0);
}

/**
 * PRNG SCA command handler.
 *
 * Command hanlder for the PRNG SCA command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_prng_sca(ujson_t *uj) {
  prng_sca_subcommand_t cmd;
  TRY(ujson_deserialize_prng_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kPrngScaSubcommandSeedPrng:
      return handle_prng_sca_seed_prng(uj);
      break;
    default:
      LOG_ERROR("Unrecognized PRNG SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
