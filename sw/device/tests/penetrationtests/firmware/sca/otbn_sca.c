// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/otbn_sca.h"

#include "ecc256_keygen_sca.h"
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

static dif_otbn_t otbn;
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;

// NOP macros.
#define NOP1 "addi x0, x0, 0\n"
#define NOP10 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1 NOP1
#define NOP30 NOP10 NOP10 NOP10

enum {
  kKeySideloadNumIt = 16,
};

// Data structs for key sideloading test.
OTBN_DECLARE_APP_SYMBOLS(otbn_key_sideload_sca);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s0_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s0_h);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s1_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s1_h);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_h);
const otbn_app_t kOtbnAppKeySideloadSca =
    OTBN_APP_T_INIT(otbn_key_sideload_sca);
static const otbn_addr_t kOtbnAppKeySideloadks0l =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s0_l);
static const otbn_addr_t kOtbnAppKeySideloadks0h =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s0_h);
static const otbn_addr_t kOtbnAppKeySideloadks1l =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s1_l);
static const otbn_addr_t kOtbnAppKeySideloadks1h =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s1_h);
static const otbn_addr_t kOtbnAppKeySideloadkl =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_l);
static const otbn_addr_t kOtbnAppKeySideloadkh =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_h);

// RSA OTBN App.
OTBN_DECLARE_APP_SYMBOLS(rsa);
OTBN_DECLARE_SYMBOL_ADDR(rsa, mode);
OTBN_DECLARE_SYMBOL_ADDR(rsa, n_limbs);
OTBN_DECLARE_SYMBOL_ADDR(rsa, inout);
OTBN_DECLARE_SYMBOL_ADDR(rsa, modulus);
OTBN_DECLARE_SYMBOL_ADDR(rsa, exp);

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa);
static const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(rsa, mode);
static const otbn_addr_t kOtbnVarRsaNLimbs = OTBN_ADDR_T_INIT(rsa, n_limbs);
static const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(rsa, inout);
static const otbn_addr_t kOtbnVarRsaModulus = OTBN_ADDR_T_INIT(rsa, modulus);
static const otbn_addr_t kOtbnVarRsaExp = OTBN_ADDR_T_INIT(rsa, exp);

/**
 * Clears the OTBN DMEM and IMEM.
 *
 * @returns OK or error.
 */
static status_t clear_otbn(void) {
  // Clear OTBN memory.
  TRY(otbn_dmem_sec_wipe());
  TRY(otbn_imem_sec_wipe());

  return OK_STATUS();
}

status_t handle_otbn_pentest_init(ujson_t *uj) {
  // Configure the entropy complex for OTBN. Set the reseed interval to max
  // to avoid a non-constant trigger window.
  TRY(pentest_configure_entropy_source_max_reseed_interval());

  pentest_init(kPentestTriggerSourceOtbn,
               kPentestPeripheralEntropy | kPentestPeripheralIoDiv4 |
                   kPentestPeripheralOtbn | kPentestPeripheralCsrng |
                   kPentestPeripheralEdn | kPentestPeripheralHmac |
                   kPentestPeripheralKmac);

  // Init the OTBN core.
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Load p256 keygen from seed app into OTBN.
  if (otbn_load_app(kOtbnAppP256KeyFromSeed).value != OTCRYPTO_OK.value) {
    return ABORTED();
  }

  // Disable the instruction cache and dummy instructions for better SCA
  // measurements.
  pentest_configure_cpu();

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_pentest_init_keymgr(ujson_t *uj) {
  if (kBootStage != kBootStageOwner) {
    TRY(keymgr_testutils_startup(&keymgr, &kmac));
    // Advance to OwnerIntermediateKey state.
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
    TRY(keymgr_testutils_check_state(&keymgr,
                                     kDifKeymgrStateOwnerIntermediateKey));
    LOG_INFO("Keymgr entered OwnerIntKey State");
  } else {
    TRY(dif_keymgr_init(mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR),
                        &keymgr));
    TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));
  }

  dif_otbn_t otbn;
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  return OK_STATUS();
}

status_t handle_otbn_sca_key_sideload_fvsr(ujson_t *uj) {
  // Get fixed seed.
  penetrationtest_otbn_sca_fixed_seed_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_fixed_seed_t(uj, &uj_data));

  // Key generation parameters.
  dif_keymgr_versioned_key_params_t sideload_params[kKeySideloadNumIt];

  // Generate FvsR values.
  bool sample_fixed = true;
  for (size_t it = 0; it < kKeySideloadNumIt; it++) {
    sideload_params[it].version = 0x0;
    sideload_params[it].dest = kDifKeymgrVersionedKeyDestOtbn;
    memset(sideload_params[it].salt, 0, sizeof(sideload_params[it].salt));
    if (sample_fixed) {
      sideload_params[it].salt[0] = uj_data.fixed_seed;
    } else {
      sideload_params[it].salt[0] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  otbn_load_app(kOtbnAppKeySideloadSca);

  uint32_t key_share_0_l[kKeySideloadNumIt], key_share_0_h[kKeySideloadNumIt];
  uint32_t key_share_1_l[16], key_share_1_h[kKeySideloadNumIt];
  uint32_t key_l[kKeySideloadNumIt], key_h[kKeySideloadNumIt];

  // SCA code target.
  for (size_t it = 0; it < kKeySideloadNumIt; it++) {
    TRY(keymgr_testutils_generate_versioned_key(&keymgr, sideload_params[it]));

    TRY(dif_otbn_set_ctrl_software_errs_fatal(&otbn, /*enable=*/false));

    pentest_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP30);
    otbn_execute();
    otbn_busy_wait_for_done();
    pentest_set_trigger_low();
    asm volatile(NOP30);

    otbn_dmem_read(1, kOtbnAppKeySideloadks0l, &key_share_0_l[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadks0h, &key_share_0_h[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadks1l, &key_share_1_l[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadks1h, &key_share_1_h[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadkl, &key_l[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadkh, &key_h[it]);
  }

  // Write back shares and keys to host.
  penetrationtest_otbn_sca_key_t uj_output;
  for (size_t it = 0; it < kKeySideloadNumIt; it++) {
    uj_output.shares[0] = key_share_0_l[it];
    uj_output.shares[1] = key_share_0_h[it];
    uj_output.shares[2] = key_share_1_l[it];
    uj_output.shares[3] = key_share_1_h[it];
    uj_output.keys[0] = key_l[it];
    uj_output.keys[1] = key_h[it];
    RESP_OK(ujson_serialize_penetrationtest_otbn_sca_key_t, uj, &uj_output);
  }

  return OK_STATUS();
}

status_t handle_otbn_sca_rsa512_decrypt(ujson_t *uj) {
  // Get RSA256 parameters.
  penetrationtest_otbn_sca_rsa512_dec_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_rsa512_dec_t(uj, &uj_data));

  otbn_load_app(kOtbnAppRsa);

  uint32_t mode = 2;  // Decrypt.
  // RSA512 configuration.
  uint32_t n_limbs = 2;

  // Write data into OTBN DMEM.
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaMode, &mode, sizeof(mode)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaNLimbs, &n_limbs, sizeof(n_limbs)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaModulus, uj_data.mod,
                          sizeof(uj_data.mod)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaExp, uj_data.exp,
                          sizeof(uj_data.exp)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaInOut, uj_data.msg,
                          sizeof(uj_data.msg)));

  pentest_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP30);
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Send back decryption result to host.
  penetrationtest_otbn_sca_rsa512_dec_out_t uj_output;
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarRsaInOut, uj_output.out,
                         sizeof(uj_output.out)));
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_rsa512_dec_out_t, uj,
          &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_sca(ujson_t *uj) {
  otbn_sca_subcommand_t cmd;
  TRY(ujson_deserialize_otbn_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtbnScaSubcommandEcc256EcdsaKeygenFvsrKeyBatch:
      return handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(uj);
    case kOtbnScaSubcommandEcc256EcdsaKeygenFvsrSeedBatch:
      return handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(uj);
    case kOtbnScaSubcommandEcc256EnMasks:
      return handle_otbn_sca_ecc256_en_masks(uj);
    case kOtbnScaSubcommandEcc256SetC:
      return handle_otbn_sca_ecc256_set_c(uj);
    case kOtbnScaSubcommandEcc256SetSeed:
      return handle_otbn_sca_ecc256_set_seed(uj);
    case kOtbnScaSubcommandInit:
      return handle_otbn_pentest_init(uj);
    case kOtbnScaSubcommandInitKeyMgr:
      return handle_otbn_pentest_init_keymgr(uj);
    case kOtbnScaSubcommandKeySideloadFvsr:
      return handle_otbn_sca_key_sideload_fvsr(uj);
    case kOtbnScaSubcommandRsa512Decrypt:
      return handle_otbn_sca_rsa512_decrypt(uj);
    default:
      LOG_ERROR("Unrecognized OTBN SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
