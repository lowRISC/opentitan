// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
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

OTBN_DECLARE_APP_SYMBOLS(p256_ecdsa);

OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_msg);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_r);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_s);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_x);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_y);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_d);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, dptr_x_r);

OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, mode);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, msg);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, r);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, s);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, y);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, d);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x_r);

static const otbn_app_t kOtbnAppP256Ecdsa = OTBN_APP_T_INIT(p256_ecdsa);

static const otbn_addr_t kOtbnVarDptrMsg =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_msg);
static const otbn_addr_t kOtbnVarDptrR = OTBN_ADDR_T_INIT(p256_ecdsa, dptr_r);
static const otbn_addr_t kOtbnVarDptrS = OTBN_ADDR_T_INIT(p256_ecdsa, dptr_s);
static const otbn_addr_t kOtbnVarDptrX = OTBN_ADDR_T_INIT(p256_ecdsa, dptr_x);
static const otbn_addr_t kOtbnVarDptrY = OTBN_ADDR_T_INIT(p256_ecdsa, dptr_y);
static const otbn_addr_t kOtbnVarDptrD = OTBN_ADDR_T_INIT(p256_ecdsa, dptr_d);
static const otbn_addr_t kOtbnVarDptrXR =
    OTBN_ADDR_T_INIT(p256_ecdsa, dptr_x_r);

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(p256_ecdsa, mode);
static const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(p256_ecdsa, msg);
static const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(p256_ecdsa, r);
static const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(p256_ecdsa, s);
static const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(p256_ecdsa, x);
static const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(p256_ecdsa, y);
static const otbn_addr_t kOtbnVarD = OTBN_ADDR_T_INIT(p256_ecdsa, d);
static const otbn_addr_t kOtbnVarXR = OTBN_ADDR_T_INIT(p256_ecdsa, x_r);

OTTF_DEFINE_TEST_CONFIG();

/**
 * The plic dif to access the hardware.
 */
static dif_rv_plic_t plic;

/**
 * The otbn context handler.
 */
static otbn_t otbn_ctx;

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
void ottf_external_isr(void) {
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kTopEarlgreyPlicTargetIbex0,
                                     (dif_rv_plic_irq_id_t *)&irq_id));

  plic_peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  irq = (dif_otbn_irq_t)(irq_id -
                         (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdOtbnDone);

  CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn_ctx.dif, irq));

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC.
  // register.
  CHECK_DIF_OK(
      dif_rv_plic_irq_complete(&plic, kTopEarlgreyPlicTargetIbex0, irq_id));
}

static void otbn_wait_for_done_irq(otbn_t *otbn_ctx) {
  // Clear the otbn irq variable: we'll set it in the interrupt handler when
  // we see the Done interrupt fire.
  irq = UINT32_MAX;
  irq_id = UINT32_MAX;
  plic_peripheral = UINT32_MAX;
  // Enable Done interrupt.
  CHECK_DIF_OK(dif_otbn_irq_set_enabled(&otbn_ctx->dif, kDifOtbnIrqDone,
                                        kDifToggleEnabled));

  // At this point, OTBN should be running. Wait for an interrupt that says
  // it's done.
  while (true) {
    // This looks a bit odd, but is needed to avoid a race condition where the
    // OTBN interrupt comes in after we load the otbn_finished flag but before
    // we run the WFI instruction. The trick is that WFI returns when an
    // interrupt comes in even if interrupts are globally disabled, which means
    // that the WFI can actually sit *inside* the critical section.
    irq_global_ctrl(false);
    if (plic_peripheral != UINT32_MAX) {
      break;
    }
    wait_for_interrupt();
    irq_global_ctrl(true);
  }
  irq_global_ctrl(true);

  CHECK(plic_peripheral == kTopEarlgreyPlicPeripheralOtbn,
        "Interrupt from incorrect peripheral: (exp: %d, obs: %s)",
        kTopEarlgreyPlicPeripheralOtbn, plic_peripheral);

  // Check this is the interrupt we expected.
  CHECK(irq_id == kTopEarlgreyPlicIrqIdOtbnDone);

  // Disable Done interrupt.
  CHECK_DIF_OK(dif_otbn_irq_set_enabled(&otbn_ctx->dif, kDifOtbnIrqDone,
                                        kDifToggleDisabled));

  // Acknowledge Done interrupt. This clears INTR_STATE.done back to 0.
  CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn_ctx->dif, kDifOtbnIrqDone));
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
 * @param otbn_ctx The OTBN context object.
 */
static void otbn_wipe_dmem(otbn_t *otbn_ctx) {
  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn_ctx->dif, kDifOtbnCmdSecWipeDmem));
  otbn_wait_for_done_irq(otbn_ctx);
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
 * Starts a profiling section.
 *
 * Call this function at the start of a section that should be profiled, and
 * call `profile_end()` at the end of it to display the results.
 *
 * @return The cycle counter when starting the profiling.
 */
static uint64_t profile_start(void) { return ibex_mcycle_read(); }

/**
 * Ends a profiling section.
 *
 * The time since `profile_start()` is printed as log message.
 *
 * @param t_start Start timestamp, as returned from profile_start().
 * @param msg Name of the operation (for logging purposes).
 */
static void profile_end(uint64_t t_start, const char *msg) {
  uint64_t t_end = ibex_mcycle_read();
  uint32_t cycles = t_end - t_start;
  uint32_t time_us = cycles / 100;
  LOG_INFO("%s took %u cycles or %u us @ 100 MHz.", msg, cycles, time_us);
}

/**
 * Makes a single dptr in the P256 library point to where its value is stored.
 */
static void setup_data_pointer(otbn_t *otbn_ctx, otbn_addr_t dptr,
                               otbn_addr_t value) {
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, sizeof(value), &value, dptr) ==
        kOtbnOk);
}

/**
 * Sets up all data pointers used by the P256 library to point to DMEM.
 *
 * The ECDSA P256 OTBN library makes use of "named" data pointers as part of
 * its calling convention, which are exposed as symbol starting with `dptr_`.
 * The DMEM locations these pointers refer to is not mandated by the P256
 * calling convention; the values can be placed anywhere in OTBN DMEM.
 *
 * As convenience, `ecdsa_p256.s` pre-allocates space for the data values.
 *
 * This function makes the data pointers refer to the pre-allocated DMEM
 * regions to store the actual values.
 */
static void setup_data_pointers(otbn_t *otbn_ctx) {
  setup_data_pointer(otbn_ctx, kOtbnVarDptrMsg, kOtbnVarMsg);
  setup_data_pointer(otbn_ctx, kOtbnVarDptrR, kOtbnVarR);
  setup_data_pointer(otbn_ctx, kOtbnVarDptrS, kOtbnVarS);
  setup_data_pointer(otbn_ctx, kOtbnVarDptrX, kOtbnVarX);
  setup_data_pointer(otbn_ctx, kOtbnVarDptrY, kOtbnVarY);
  setup_data_pointer(otbn_ctx, kOtbnVarDptrD, kOtbnVarD);
  setup_data_pointer(otbn_ctx, kOtbnVarDptrXR, kOtbnVarXR);
}

/**
 * Signs a message with ECDSA using the P-256 curve.
 *
 * @param otbn_ctx            The OTBN context object.
 * @param msg                 The message to sign (32B).
 * @param private_key_d       The private key (32B).
 * @param[out] signature_r    Signature component r (the x-coordinate of R).
 *                            Provide a pre-allocated 32B buffer.
 * @param[out] signature_s    Signature component s (the proof).
 *                            Provide a pre-allocated 32B buffer.
 */
static void p256_ecdsa_sign(otbn_t *otbn_ctx, const uint8_t *msg,
                            const uint8_t *private_key_d, uint8_t *signature_r,
                            uint8_t *signature_s) {
  CHECK(otbn_ctx != NULL);

  // Set pointers to input arguments.
  setup_data_pointers(otbn_ctx);

  // Write input arguments.
  uint32_t mode = 1;  // mode 1 => sign
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, sizeof(mode), &mode, kOtbnVarMode) ==
        kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, msg, kOtbnVarMsg) ==
        kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, private_key_d,
                               kOtbnVarD) == kOtbnOk);

  // Call OTBN to perform operation, and wait for it to complete.
  CHECK(otbn_execute(otbn_ctx) == kOtbnOk);
  otbn_wait_for_done_irq(otbn_ctx);

  // Read back results.
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarR,
                                 signature_r) == kOtbnOk);
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarS,
                                 signature_s) == kOtbnOk);
}

/**
 * Verifies a message with ECDSA using the P-256 curve.
 *
 * @param otbn_ctx             The OTBN context object.
 * @param msg                  The message to verify (32B).
 * @param signature_r          The signature component r (the proof) (32B).
 * @param signature_s          The signature component s (the proof) (32B).
 * @param public_key_x         The public key x-coordinate (32B).
 * @param public_key_y         The public key y-coordinate (32B).
 * @param[out] signature_x_r   Recovered point x_r (== R'.x). Provide a
 *                             pre-allocated 32B buffer.
 */
static void p256_ecdsa_verify(otbn_t *otbn_ctx, const uint8_t *msg,
                              const uint8_t *signature_r,
                              const uint8_t *signature_s,
                              const uint8_t *public_key_x,
                              const uint8_t *public_key_y,
                              uint8_t *signature_x_r) {
  CHECK(otbn_ctx != NULL);

  // Set pointers to input arguments.
  setup_data_pointers(otbn_ctx);

  // Write input arguments.
  uint32_t mode = 2;  // mode 2 => verify
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, sizeof(mode), &mode, kOtbnVarMode) ==
        kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, msg, kOtbnVarMsg) ==
        kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, signature_r,
                               kOtbnVarR) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, signature_s,
                               kOtbnVarS) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, public_key_x,
                               kOtbnVarX) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, public_key_y,
                               kOtbnVarY) == kOtbnOk);

  // Call OTBN to perform operation, and wait for it to complete.
  CHECK(otbn_execute(otbn_ctx) == kOtbnOk);
  otbn_wait_for_done_irq(otbn_ctx);

  // Read back results.
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarXR,
                                 signature_x_r) == kOtbnOk);
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
  CHECK(otbn_init(&otbn_ctx, mmio_region_from_addr(
                                 TOP_EARLGREY_OTBN_BASE_ADDR)) == kOtbnOk);
  otbn_init_irq();
  CHECK(otbn_load_app(&otbn_ctx, kOtbnAppP256Ecdsa) == kOtbnOk);
  profile_end(t_start_init, "Initialization");

  // Sign
  uint8_t signature_r[32] = {0};
  uint8_t signature_s[32] = {0};

  LOG_INFO("Signing");
  uint64_t t_start_sign = profile_start();
  p256_ecdsa_sign(&otbn_ctx, kIn, kPrivateKeyD, signature_r, signature_s);
  profile_end(t_start_sign, "Sign");

  // Securely wipe OTBN data memory and reload app
  LOG_INFO("Wiping OTBN DMEM and reloading app");
  otbn_wipe_dmem(&otbn_ctx);
  CHECK(otbn_load_app(&otbn_ctx, kOtbnAppP256Ecdsa) == kOtbnOk);

  // Verify
  uint8_t signature_x_r[32] = {0};

  LOG_INFO("Verifying");
  uint64_t t_start_verify = profile_start();
  p256_ecdsa_verify(&otbn_ctx, kIn, signature_r, signature_s, kPublicKeyQx,
                    kPublicKeyQy, signature_x_r);

  // Include the r =? x_r comparison in the profiling as this is something
  // either OTBN or the host CPU needs to do as part of the signature
  // verification.
  check_data("signature_x_r", signature_r, signature_x_r, 32);
  profile_end(t_start_verify, "Verify");

  // Securely wipe OTBN data memory
  LOG_INFO("Wiping OTBN DMEM");
  otbn_wipe_dmem(&otbn_ctx);
}

bool test_main(void) {
  entropy_testutils_auto_mode_init();

  test_ecdsa_p256_roundtrip();

  return true;
}
