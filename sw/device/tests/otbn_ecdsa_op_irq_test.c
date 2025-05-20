// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/profile.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * ECDSA sign and verify test with the NIST P-256 curve using OTBN.
 *
 * IMPORTANT: This test is not a secure, complete, or reusable implementation of
 * a cryptographic algorithm; it is not even close to being production-ready.
 * It is only meant as an end-to-end test for OTBN during the bringup phase.
 *
 * The test contains constants and expected output, which can be independently
 * and conveniently verified using a Python script.
 *
 * <code>
 * # Optional: generate a new key
 * $ openssl ecparam -name prime256v1 -genkey -noout -out \
 *     otbn_ecdsa_p256_test_private_key.pem
 *
 * # Create all constants/variables
 * $ ./otbn_test_params.py ecc otbn_ecdsa_p256_test_private_key.pem
 * </code>
 */

OTBN_DECLARE_APP_SYMBOLS(run_p256);

OTBN_DECLARE_SYMBOL_ADDR(run_p256, mode);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, msg);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, r);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, s);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, x);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, y);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, d0_io);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, d1_io);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, x_r);

static const otbn_app_t kOtbnAppP256Ecdsa = OTBN_APP_T_INIT(run_p256);

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_p256, mode);
static const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p256, msg);
static const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p256, r);
static const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p256, s);
static const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p256, x);
static const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p256, y);
static const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
static const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
static const otbn_addr_t kOtbnVarXR = OTBN_ADDR_T_INIT(run_p256, x_r);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_VERIFY);
static const uint32_t kModeSign = OTBN_ADDR_T_INIT(run_p256, MODE_SIGN);
static const uint32_t kModeVerify = OTBN_ADDR_T_INIT(run_p256, MODE_VERIFY);

OTTF_DEFINE_TEST_CONFIG();

/**
 * The plic dif to access the hardware.
 */
static dif_rv_plic_t plic;

/**
 * The otbn context handler.
 */
static dif_otbn_t otbn;

/**
 * The peripheral which fired the irq to be filled by the irq handler.
 */
static volatile top_earlgrey_plic_peripheral_t plic_peripheral;

/**
 * The irq id to be filled by the irq handler.
 */
static volatile dif_rv_plic_irq_id_t irq_id;

/**
 * The otbn irq to be filled by the irq handler.
 */
static volatile dif_otbn_irq_t irq;

/**
 * Provides external IRQ handling for otbn tests.
 *
 * This function overrides the default OTTF external ISR.
 *
 * It performs the following:
 * 1. Claims the IRQ fired (finds PLIC IRQ index).
 * 2. Compute the OTBN peripheral.
 * 3. Compute the otbn irq.
 * 4. Clears the IRQ at the peripheral.
 * 5. Completes the IRQ service at PLIC.
 */
void ottf_external_isr(uint32_t *exc_info) {
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0,
                                     (dif_rv_plic_irq_id_t *)&irq_id));

  plic_peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  irq = (dif_otbn_irq_t)(irq_id -
                         (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdOtbnDone);

  CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn, irq));

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register.
  CHECK_DIF_OK(
      dif_rv_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0, irq_id));
}

static void otbn_wait_for_done_irq(dif_otbn_t *otbn) {
  // Clear the otbn irq variable: we'll set it in the interrupt handler when
  // we see the Done interrupt fire.
  irq = UINT32_MAX;
  irq_id = UINT32_MAX;
  plic_peripheral = UINT32_MAX;
  // Enable Done interrupt.
  CHECK_DIF_OK(
      dif_otbn_irq_set_enabled(otbn, kDifOtbnIrqDone, kDifToggleEnabled));

  // At this point, OTBN should be running. Wait for an interrupt that says
  // it's done.
  ATOMIC_WAIT_FOR_INTERRUPT(plic_peripheral != UINT32_MAX);

  CHECK(plic_peripheral == kTopEarlgreyPlicPeripheralOtbn,
        "Interrupt from incorrect peripheral: (exp: %d, obs: %s)",
        kTopEarlgreyPlicPeripheralOtbn, plic_peripheral);

  // Check this is the interrupt we expected.
  CHECK(irq_id == kTopEarlgreyPlicIrqIdOtbnDone);

  // Disable Done interrupt.
  CHECK_DIF_OK(
      dif_otbn_irq_set_enabled(otbn, kDifOtbnIrqDone, kDifToggleDisabled));

  // Acknowledge Done interrupt. This clears INTR_STATE.done back to 0.
  CHECK_DIF_OK(dif_otbn_irq_acknowledge(otbn, kDifOtbnIrqDone));
}

static void otbn_init_irq(void) {
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  // Initialize PLIC and configure OTBN interrupt.
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic));

  // Set interrupt priority to be positive.
  dif_rv_plic_irq_id_t irq_id = kTopEarlgreyPlicIrqIdOtbnDone;
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&plic, irq_id, 0x1));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &plic, irq_id, kTopEarlgreyPlicTargetIbex0, kDifToggleEnabled));

  // Set the threshold for Ibex to 0.
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(
      &plic, kTopEarlgreyPlicTargetIbex0, 0x0));

  // Enable the external IRQ (so that we see the interrupt from the PLIC).
  irq_global_ctrl(true);
  irq_external_ctrl(true);
}

/**
 * Securely wipes OTBN DMEM and waits for Done interrupt.
 *
 * @param otbn The OTBN context object.
 */
static void otbn_wipe_dmem(dif_otbn_t *otbn) {
  CHECK_DIF_OK(dif_otbn_write_cmd(otbn, kDifOtbnCmdSecWipeDmem));
  otbn_wait_for_done_irq(otbn);
}

/**
 * CHECK()s that the actual data matches the expected data.
 *
 * @param actual The actual data.
 * @param expected The expected data.
 * @param size_bytes The size of the actual/expected data.
 */
static void check_data(const char *msg, const uint8_t *actual,
                       const uint8_t *expected, size_t size_bytes) {
  for (int i = 0; i < size_bytes; ++i) {
    CHECK(actual[i] == expected[i],
          "%s: mismatch at byte %d: 0x%x (actual) != 0x%x (expected)", msg, i,
          actual[i], expected[i]);
  }
}

/**
 * Signs a message with ECDSA using the P-256 curve.
 *
 * @param otbn                The OTBN context object.
 * @param msg                 The message to sign (32B).
 * @param private_key_d       The private key (32B).
 * @param[out] signature_r    Signature component r (the x-coordinate of R).
 *                            Provide a pre-allocated 32B buffer.
 * @param[out] signature_s    Signature component s (the proof).
 *                            Provide a pre-allocated 32B buffer.
 */
static void p256_ecdsa_sign(dif_otbn_t *otbn, const uint8_t *msg,
                            const uint8_t *private_key_d, uint8_t *signature_r,
                            uint8_t *signature_s) {
  CHECK(otbn != NULL);

  // Write input arguments.
  uint32_t mode = kModeSign;
  CHECK_STATUS_OK(
      otbn_testutils_write_data(otbn, sizeof(uint32_t), &mode, kOtbnVarMode));
  CHECK_STATUS_OK(
      otbn_testutils_write_data(otbn, /*len_bytes=*/32, msg, kOtbnVarMsg));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, /*len_bytes=*/32,
                                            private_key_d, kOtbnVarD0));

  // Write redundant upper bits of d (all-zero for this test).
  uint8_t d0_high[32] = {0};
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, /*len_bytes=*/32, d0_high,
                                            kOtbnVarD0 + 32));

  // Write second share of d (all-zero for this test).
  uint8_t d1[64] = {0};
  CHECK_STATUS_OK(
      otbn_testutils_write_data(otbn, /*len_bytes=*/64, d1, kOtbnVarD1));

  // Call OTBN to perform operation, and wait for it to complete.
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
  otbn_wait_for_done_irq(otbn);

  // Read back results.
  CHECK_STATUS_OK(
      otbn_testutils_read_data(otbn, /*len_bytes=*/32, kOtbnVarR, signature_r));
  CHECK_STATUS_OK(
      otbn_testutils_read_data(otbn, /*len_bytes=*/32, kOtbnVarS, signature_s));
}

/**
 * Verifies a message with ECDSA using the P-256 curve.
 *
 * @param otbn                 The OTBN context object.
 * @param msg                  The message to verify (32B).
 * @param signature_r          The signature component r (the proof) (32B).
 * @param signature_s          The signature component s (the proof) (32B).
 * @param public_key_x         The public key x-coordinate (32B).
 * @param public_key_y         The public key y-coordinate (32B).
 * @param[out] signature_x_r   Recovered point x_r (== R'.x). Provide a
 *                             pre-allocated 32B buffer.
 */
static void p256_ecdsa_verify(dif_otbn_t *otbn, const uint8_t *msg,
                              const uint8_t *signature_r,
                              const uint8_t *signature_s,
                              const uint8_t *public_key_x,
                              const uint8_t *public_key_y,
                              uint8_t *signature_x_r) {
  CHECK(otbn != NULL);

  // Write input arguments.
  uint32_t mode = kModeVerify;
  CHECK_STATUS_OK(
      otbn_testutils_write_data(otbn, sizeof(uint32_t), &mode, kOtbnVarMode));
  CHECK_STATUS_OK(
      otbn_testutils_write_data(otbn, /*len_bytes=*/32, msg, kOtbnVarMsg));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, /*len_bytes=*/32, signature_r,
                                            kOtbnVarR));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, /*len_bytes=*/32, signature_s,
                                            kOtbnVarS));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, /*len_bytes=*/32,
                                            public_key_x, kOtbnVarX));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, /*len_bytes=*/32,
                                            public_key_y, kOtbnVarY));

  // Call OTBN to perform operation, and wait for it to complete.
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
  otbn_wait_for_done_irq(otbn);

  // Read back results.
  CHECK_STATUS_OK(otbn_testutils_read_data(otbn, /*len_bytes=*/32, kOtbnVarXR,
                                           signature_x_r));
}

/**
 * Performs a ECDSA roundtrip test using the NIST P-256 curve.
 *
 * A roundtrip consists of three steps: Initialize OTBN, sign, and verify.
 */
static void test_ecdsa_p256_roundtrip(void) {
  // Message
  static const uint8_t kIn[32] = {"Hello OTBN."};

  // Public key x-coordinate (Q.x)
  static const uint8_t kPublicKeyQx[32] = {
      0x4e, 0xb2, 0x8b, 0x55, 0xeb, 0x88, 0x62, 0x24, 0xf2, 0xbf, 0x1b,
      0x9e, 0xd8, 0x4a, 0x09, 0xa7, 0x86, 0x67, 0x92, 0xcd, 0xca, 0x07,
      0x5d, 0x07, 0x82, 0xe7, 0x2d, 0xac, 0x31, 0x14, 0x79, 0x1f};

  // Public key y-coordinate (Q.y)
  static const uint8_t kPublicKeyQy[32] = {
      0x27, 0x9c, 0xe4, 0x23, 0x24, 0x10, 0xa2, 0xfa, 0xbd, 0x53, 0x73,
      0xf1, 0xa5, 0x08, 0xf0, 0x40, 0x9e, 0xc0, 0x55, 0x21, 0xa4, 0xf0,
      0x54, 0x59, 0x00, 0x3e, 0x5f, 0x15, 0x3c, 0xc6, 0x4b, 0x87};

  // Private key (d)
  static const uint8_t kPrivateKeyD[32] = {
      0xcd, 0xb4, 0x57, 0xaf, 0x1c, 0x9f, 0x4c, 0x74, 0x02, 0x0c, 0x7e,
      0x8b, 0xe9, 0x93, 0x3e, 0x28, 0x0c, 0xf0, 0x18, 0x0d, 0xf4, 0x6c,
      0x0b, 0xda, 0x7a, 0xbb, 0xe6, 0x8f, 0xb7, 0xa0, 0x45, 0x55};

  // Initialize
  uint64_t t_start_init = profile_start();
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  otbn_init_irq();
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kOtbnAppP256Ecdsa));
  profile_end_and_print(t_start_init, "Initialization");

  // Sign
  uint8_t signature_r[32] = {0};
  uint8_t signature_s[32] = {0};

  LOG_INFO("Signing");
  uint64_t t_start_sign = profile_start();
  p256_ecdsa_sign(&otbn, kIn, kPrivateKeyD, signature_r, signature_s);
  profile_end_and_print(t_start_sign, "Sign");

  // Securely wipe OTBN data memory and reload app
  LOG_INFO("Wiping OTBN DMEM and reloading app");
  otbn_wipe_dmem(&otbn);
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kOtbnAppP256Ecdsa));

  // Verify
  uint8_t signature_x_r[32] = {0};

  LOG_INFO("Verifying");
  uint64_t t_start_verify = profile_start();
  p256_ecdsa_verify(&otbn, kIn, signature_r, signature_s, kPublicKeyQx,
                    kPublicKeyQy, signature_x_r);

  // Include the r =? x_r comparison in the profiling as this is something
  // either OTBN or the host CPU needs to do as part of the signature
  // verification.
  check_data("signature_x_r", signature_r, signature_x_r, 32);
  profile_end_and_print(t_start_verify, "Verify");

  // Securely wipe OTBN data memory
  LOG_INFO("Wiping OTBN DMEM");
  otbn_wipe_dmem(&otbn);
}

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  test_ecdsa_p256_roundtrip();

  return true;
}
