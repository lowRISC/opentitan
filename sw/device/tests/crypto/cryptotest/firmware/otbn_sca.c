// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/otbn_sca.h"

#include "ecc256_keygen_sca.h"
#include "ecc256_modinv_sca.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/json/otbn_sca_commands.h"

/**
 * App select command handler.
 *
 * This handler has to be called to load a new app to otbn.
 *
 * The uJSON data contains:
 *  - app: 0 => ecc256 keygen, 1 => ecc256 modular inverse.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_app_select(ujson_t *uj) {
  cryptotest_otbn_sca_app_select_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_app_select_t(uj, &uj_data));

  if (*uj_data.app == 0) {
    // load keygen app
    if (otbn_load_app(kOtbnAppP256KeyFromSeed).value != OTCRYPTO_OK.value) {
      return ABORTED();
    }
  } else if (*uj_data.app == 1) {
    // load mod inv app
    if (otbn_load_app(kOtbnAppP256ModInv).value != OTCRYPTO_OK.value) {
      return ABORTED();
    }
  } else {
    LOG_ERROR("Wrong app select command.");
    return ABORTED();
  }

  return OK_STATUS(0);
}

/**
 * Initialize OTBN command handler.
 *
 * This command is designed to setup the AES.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_init(ujson_t *uj) {
  sca_init(kScaTriggerSourceOtbn, kScaPeripheralEntropy | kScaPeripheralIoDiv4 |
                                      kScaPeripheralOtbn | kScaPeripheralCsrng |
                                      kScaPeripheralEdn | kScaPeripheralHmac);

  // Load p256 keygen from seed app into OTBN.
  if (otbn_load_app(kOtbnAppP256KeyFromSeed).value != OTCRYPTO_OK.value) {
    return ABORTED();
  }
  return OK_STATUS(0);
}

/**
 * OTBN SCA command handler.
 *
 * Command hanlder for the OTBN SCA command.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca(ujson_t *uj) {
  otbn_sca_subcommand_t cmd;
  TRY(ujson_deserialize_otbn_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtbnScaSubcommandInit:
      return handle_otbn_sca_init(uj);
    case kOtbnScaSubcommandEcc256EcdsaKeygenFvsrSeedBatch:
      return handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(uj);
    case kOtbnScaSubcommandEcc256EcdsaKeygenFvsrKeyBatch:
      return handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(uj);
    case kOtbnScaSubcommandEcc256EcdsaSecretKeygen:
      return handle_otbn_sca_ecc256_ecdsa_secret_keygen(uj);
    case kOtbnScaSubcommandEcc256EcdsaGenKeypair:
      return handle_otbn_sca_ecc256_ecdsa_gen_keypair(uj);
    case kOtbnScaSubcommandEcc256SetSeed:
      return handle_otbn_sca_ecc256_set_seed(uj);
    case kOtbnScaSubcommandEcc256SetC:
      return handle_otbn_sca_ecc256_set_c(uj);
    case kOtbnScaSubcommandEcc256EnMasks:
      return handle_otbn_sca_ecc256_en_masks(uj);
    case kOtbnScaSubcommandEcc256AppSelect:
      return handle_otbn_sca_ecc256_app_select(uj);
    case kOtbnScaSubcommandEcc256Modinv:
      return handle_otbn_sca_ecc256_modinv(uj);
    default:
      LOG_ERROR("Unrecognized OTBN SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
