// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/sca/otbn_vertical/ecc256_modinv_serial.h"

#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"
#include "sw/ip/entropy_src/test/utils/entropy_testutils.h"
#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
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
static void otbn_manual_trigger(void) { SS_CHECK_STATUS_OK(otbn_execute()); }

/**
 * Runs the OTBN modular inverse program.
 *
 * The input must be `kEcc256ModInvInputShareNumWords` words long.
 *
 * @param[in] input  Iput value for the OTBN modular inverse.
 */
static void p256_run_modinv(uint32_t *k0, uint32_t *k1) {
  // Write input.
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256ModInvInputShareNumWords, k0, kOtbnVarModInvK0));
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256ModInvInputShareNumWords, k1, kOtbnVarModInvK1));

  // Execute program.
  sca_set_trigger_high();
  sca_call_and_sleep(otbn_manual_trigger, kIbexOtbnSleepCycles, false);
  otbn_busy_wait_for_done();
  sca_set_trigger_low();
}

void ecc256_modinv(const uint8_t *k0_k1, size_t k0_k1_len) {
  if (k0_k1_len != 2 * kEcc256ModInvInputShareNumBytes) {
    LOG_ERROR("Invalid input length %hu", (uint8_t)k0_k1_len);
    return;
  }

  // Copy input to an aligned buffer.
  uint32_t modinv_k0[kEcc256ModInvInputShareNumWords];
  uint32_t modinv_k1[kEcc256ModInvInputShareNumWords];
  memcpy(modinv_k0, k0_k1, kEcc256ModInvInputShareNumBytes);
  memcpy(modinv_k1, (k0_k1 + kEcc256ModInvInputShareNumBytes),
         kEcc256ModInvInputShareNumBytes);

  // Run the key generation program.
  p256_run_modinv(modinv_k0, modinv_k1);

  // Read result.
  uint32_t modinv_kalpha_inv[kEcc256ModInvOutputKAlphaInvNumWords];
  uint32_t modinv_alpha[kEcc256ModInvOutputAlphaNumWords];
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256ModInvOutputKAlphaInvNumWords,
                                    kOtbnVarModInvKAplhaInv,
                                    modinv_kalpha_inv));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256ModInvOutputAlphaNumWords,
                                    kOtbnVarModInvAlpha, modinv_alpha));

  simple_serial_send_packet('r', (unsigned char *)modinv_kalpha_inv,
                            kEcc256ModInvOutputKAlphaInvNumBytes);
  simple_serial_send_packet('r', (unsigned char *)modinv_alpha,
                            kEcc256ModInvOutputAlphaNumBytes);
}
