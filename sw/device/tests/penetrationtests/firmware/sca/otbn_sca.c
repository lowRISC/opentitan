// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/otbn_sca.h"

#include "ecc256_keygen_sca.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/penetrationtests/firmware//lib/sca_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_sca_commands.h"

status_t handle_otbn_sca_init(ujson_t *uj) {
  // Configure the entropy complex for OTBN. Set the reseed interval to max
  // to avoid a non-constant trigger window.
  TRY(sca_configure_entropy_source_max_reseed_interval());

  sca_init(kScaTriggerSourceOtbn, kScaPeripheralEntropy | kScaPeripheralIoDiv4 |
                                      kScaPeripheralOtbn | kScaPeripheralCsrng |
                                      kScaPeripheralEdn | kScaPeripheralHmac);

  // Load p256 keygen from seed app into OTBN.
  if (otbn_load_app(kOtbnAppP256KeyFromSeed).value != OTCRYPTO_OK.value) {
    return ABORTED();
  }

  // Disable the instruction cache and dummy instructions for better SCA
  // measurements.
  sca_configure_cpu();

  return OK_STATUS();
}

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
    case kOtbnScaSubcommandEcc256SetSeed:
      return handle_otbn_sca_ecc256_set_seed(uj);
    case kOtbnScaSubcommandEcc256SetC:
      return handle_otbn_sca_ecc256_set_c(uj);
    case kOtbnScaSubcommandEcc256EnMasks:
      return handle_otbn_sca_ecc256_en_masks(uj);
    default:
      LOG_ERROR("Unrecognized OTBN SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
