// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/ecc256_modinv_sca.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/json/otbn_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"

enum {
  /**
   * Number of cycles that Ibex should sleep to minimize noise during OTBN
   * operations. Caution: This number should be chosen to provide enough time
   * to complete the operation. Otherwise, Ibex might wake up while OTBN is
   * still busy and disturb the capture.
   */
  kIbexOtbnSleepCycles = 50000,
  /**
   * Number of bytes for ECDSA P-256 modular inverse input shares (k0,k1).
   */
  kEcc256ModInvInputShareNumBytes = 320 / 8,
  /**
   * Number of words for ECDSA P-256 modular inverse input shares (k0,k1).
   */
  kEcc256ModInvInputShareNumWords =
      kEcc256ModInvInputShareNumBytes / sizeof(uint32_t),
  /**
   * Number of bytes for ECDSA P-256 modular inverse output ((k*alpha)^-1 mod
   * n).
   */
  kEcc256ModInvOutputKAlphaInvNumBytes = 256 / 8,
  /**
   * Number of words for ECDSA P-256 modular inverse output ((k*alpha)^-1 mod
   * n).
   */
  kEcc256ModInvOutputKAlphaInvNumWords =
      kEcc256ModInvOutputKAlphaInvNumBytes / sizeof(uint32_t),
  /**
   * Number of bytes for ECDSA P-256 modular inverse output mask (alpha).
   */
  kEcc256ModInvOutputAlphaNumBytes = 128 / 8,
  /**
   * Number of words for ECDSA P-256 modular inverse output mask (alpha).
   */
  kEcc256ModInvOutputAlphaNumWords =
      kEcc256ModInvOutputAlphaNumBytes / sizeof(uint32_t),
};

/**
 * App configuration for p256_mod_inv_sca
 */
const otbn_app_t kOtbnAppP256ModInv = OTBN_APP_T_INIT(p256_mod_inv_sca);

static const otbn_addr_t kOtbnVarModInvK0 =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, k0);
static const otbn_addr_t kOtbnVarModInvK1 =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, k1);
static const otbn_addr_t kOtbnVarModInvKAplhaInv =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, kalpha_inv);
static const otbn_addr_t kOtbnVarModInvAlpha =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, alpha);

/**
 * Callback wrapper for OTBN manual trigger function.
 */
static void otbn_manual_trigger(void) { otbn_execute(); }

/**
 * Runs the OTBN modular inverse program.
 *
 * The input must be `kEcc256ModInvInputShareNumWords` words long.
 *
 * @param[in] input  Iput value for the OTBN modular inverse.
 */
static ecc256_modinv_sca_error_t p256_run_modinv(uint32_t *k0, uint32_t *k1) {
  // Write input.
  if (otbn_dmem_write(kEcc256ModInvInputShareNumWords, k0, kOtbnVarModInvK0)
          .value != OTCRYPTO_OK.value) {
    return ecc256ModinvAborted;
  }

  if (otbn_dmem_write(kEcc256ModInvInputShareNumWords, k1, kOtbnVarModInvK1)
          .value != OTCRYPTO_OK.value) {
    return ecc256ModinvAborted;
  }

  // Execute program.
  sca_set_trigger_high();
  sca_call_and_sleep(otbn_manual_trigger, kIbexOtbnSleepCycles);
  otbn_busy_wait_for_done();
  sca_set_trigger_low();

  return ecc256ModinvOk;
}

/**
 * Computes the modular inverse of a certain input.
 *
 * The uJSON data contains:
 *  - k0_k1: Input for modular inverse computation.
 *  - k0_k1:len: Length.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_modinv(ujson_t *uj) {
  cryptotest_otbn_sca_k_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_k_t(uj, &uj_data));
  LOG_ERROR("In handle_otbn_sca_ecc256_modinv");
  if (uj_data.k_len != 2 * kEcc256ModInvInputShareNumBytes) {
    return OUT_OF_RANGE();
  }

  // Copy input to an aligned buffer.
  uint32_t modinv_k0[kEcc256ModInvInputShareNumWords];
  uint32_t modinv_k1[kEcc256ModInvInputShareNumWords];
  memcpy(modinv_k0, uj_data.k, kEcc256ModInvInputShareNumBytes);
  memcpy(modinv_k1, (uj_data.k + kEcc256ModInvInputShareNumBytes),
         kEcc256ModInvInputShareNumBytes);

  // Run the key generation program.
  if (p256_run_modinv(modinv_k0, modinv_k1) != ecc256ModinvOk) {
    return ABORTED();
  };

  // Read result.
  uint32_t modinv_kalpha_inv[kEcc256ModInvOutputKAlphaInvNumWords];
  uint32_t modinv_alpha[kEcc256ModInvOutputAlphaNumWords];
  if (otbn_dmem_read(kEcc256ModInvOutputKAlphaInvNumWords,
                     kOtbnVarModInvKAplhaInv, modinv_kalpha_inv)
          .value != OTCRYPTO_OK.value) {
    return ABORTED();
  }
  if (otbn_dmem_read(kEcc256ModInvOutputAlphaNumWords, kOtbnVarModInvAlpha,
                     modinv_alpha)
          .value != OTCRYPTO_OK.value) {
    return ABORTED();
  }
  cryptotest_otbn_sca_alpha_t uj_output;
  memcpy(uj_output.alpha_inv, (uint8_t *)modinv_kalpha_inv,
         kEcc256ModInvOutputKAlphaInvNumBytes);
  memcpy(uj_output.alpha, (uint8_t *)modinv_alpha,
         kEcc256ModInvOutputAlphaNumBytes);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_alpha_t, uj, &uj_output);

  LOG_ERROR("Fin handle_otbn_sca_ecc256_modinv");
  return OK_STATUS(0);
}
