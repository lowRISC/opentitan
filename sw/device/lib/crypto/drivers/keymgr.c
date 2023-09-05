// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/keymgr.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/hart.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'k', 'r')

enum {
  kBaseAddr = TOP_EARLGREY_KEYMGR_BASE_ADDR,
};
static_assert(kKeymgrSaltNumWords == KEYMGR_SALT_MULTIREG_COUNT,
              "Number of salt registers does not match.");
static_assert(kKeymgrOutputShareNumWords ==
                  KEYMGR_SW_SHARE0_OUTPUT_MULTIREG_COUNT,
              "Number of output share 0 registers does not match.");
static_assert(kKeymgrOutputShareNumWords ==
                  KEYMGR_SW_SHARE1_OUTPUT_MULTIREG_COUNT,
              "Number of output share 1 registers does not match.");

/**
 * Fails if the keymgr is not idle.
 *
 * @return OK if the key manager is idle, OTCRYPTO_RECOV_ERR otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t keymgr_is_idle(void) {
  uint32_t reg = abs_mmio_read32(kBaseAddr + KEYMGR_OP_STATUS_REG_OFFSET);
  uint32_t status = bitfield_field32_read(reg, KEYMGR_OP_STATUS_STATUS_FIELD);
  if (launder32(status) == KEYMGR_OP_STATUS_STATUS_VALUE_IDLE) {
    HARDENED_CHECK_EQ(status, KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
    return OTCRYPTO_OK;
  }
  return OTCRYPTO_RECOV_ERR;
}

/**
 * Set diversification input and start the key manager operation.
 *
 * Ensure the key manager is idle before calling this function.
 *
 * @param diversification Diversification input for the key derivation.
 */
static void keymgr_start(keymgr_diversification_t diversification) {
  // Set the version.
  abs_mmio_write32(kBaseAddr + KEYMGR_KEY_VERSION_REG_OFFSET,
                   diversification.version);
  // Set the salt.
  for (size_t i = 0; i < kKeymgrSaltNumWords; i++) {
    abs_mmio_write32(
        kBaseAddr + KEYMGR_SALT_0_REG_OFFSET + (i * sizeof(uint32_t)),
        diversification.salt[i]);
  }

  // Issue the start command.
  abs_mmio_write32(kBaseAddr + KEYMGR_START_REG_OFFSET,
                   1 << KEYMGR_START_EN_BIT);
}

/**
 * Wait for the key manager to finish an operation.
 *
 * Polls the key manager until it is no longer busy. If the operation completed
 * successfully or the key manager was already idle, returns OTCRYPTO_OK. If
 * there was an error during the operation, reads and clears the error code
 * and returns OTCRYPTO_RECOV_ERR; the operation can be retried afterwards.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t keymgr_wait_until_done(void) {
  // Poll the OP_STATUS register until it is something other than "WIP".
  uint32_t reg;
  uint32_t status;
  do {
    reg = abs_mmio_read32(kBaseAddr + KEYMGR_OP_STATUS_REG_OFFSET);
    status = bitfield_field32_read(reg, KEYMGR_OP_STATUS_STATUS_FIELD);
  } while (status == KEYMGR_OP_STATUS_STATUS_VALUE_WIP);

  // Clear OP_STATUS by writing back the value we read.
  abs_mmio_write32(kBaseAddr + KEYMGR_OP_STATUS_REG_OFFSET, reg);

  // Check if the key manager reported errors. If it is already idle or
  // completed an operation successfully, return an OK status. No other
  // statuses (e.g. WIP) should be possible.
  switch (status) {
    case KEYMGR_OP_STATUS_STATUS_VALUE_IDLE:
      return OTCRYPTO_OK;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS:
      return OTCRYPTO_OK;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR: {
      // Clear the ERR_CODE register before returning.
      uint32_t err_code =
          abs_mmio_read32(kBaseAddr + KEYMGR_ERR_CODE_REG_OFFSET);
      abs_mmio_write32(kBaseAddr + KEYMGR_ERR_CODE_REG_OFFSET, err_code);
      return OTCRYPTO_RECOV_ERR;
    }
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Set the control register of the key manager.
 *
 * The CDI select bit is always set to false for this driver (i.e. Sealing
 * CDI). The driver does not support attestation CDI.
 *
 * @param dest (NONE, AES, OTBN, or KMAC)
 * @param operation (GENERATE_SW or GENERATE_HW)
 */
#define WRITE_CTRL(dest, operation)                                            \
  do {                                                                         \
    uint32_t ctrl =                                                            \
        bitfield_field32_write(0, KEYMGR_CONTROL_SHADOWED_DEST_SEL_FIELD,      \
                               KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_##dest); \
    ctrl = bitfield_bit32_write(ctrl, KEYMGR_CONTROL_SHADOWED_CDI_SEL_BIT,     \
                                false);                                        \
    ctrl = bitfield_field32_write(                                             \
        ctrl, KEYMGR_CONTROL_SHADOWED_OPERATION_FIELD,                         \
        KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_##operation##_OUTPUT);         \
    abs_mmio_write32_shadowed(kBaseAddr + KEYMGR_CONTROL_SHADOWED_REG_OFFSET,  \
                              ctrl);                                           \
  } while (false);

status_t keymgr_generate_key_sw(keymgr_diversification_t diversification,
                                keymgr_output_t *key) {
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate a software-visible key.
  WRITE_CTRL(NONE, GENERATE_SW);

  // Start the operation and wait for it to complete.
  keymgr_start(diversification);
  HARDENED_TRY(keymgr_wait_until_done());

  // Collect output.
  // TODO: for SCA hardening, randomize the order of these reads.
  for (size_t i = 0; i < kKeymgrOutputShareNumWords; i++) {
    key->share0[i] =
        abs_mmio_read32(kBaseAddr + KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET +
                        (i * sizeof(uint32_t)));
  }
  for (size_t i = 0; i < kKeymgrOutputShareNumWords; i++) {
    key->share1[i] =
        abs_mmio_read32(kBaseAddr + KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET +
                        (i * sizeof(uint32_t)));
  }

  return OTCRYPTO_OK;
}

status_t keymgr_generate_key_aes(keymgr_diversification_t diversification) {
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate an AES key.
  WRITE_CTRL(AES, GENERATE_HW);

  // Start the operation and wait for it to complete.
  keymgr_start(diversification);
  return keymgr_wait_until_done();
}

status_t keymgr_generate_key_kmac(keymgr_diversification_t diversification) {
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate a KMAC key.
  WRITE_CTRL(KMAC, GENERATE_HW);

  // Start the operation and wait for it to complete.
  keymgr_start(diversification);
  return keymgr_wait_until_done();
}

status_t keymgr_generate_key_otbn(keymgr_diversification_t diversification) {
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate an OTBN key.
  WRITE_CTRL(OTBN, GENERATE_HW);

  // Start the operation and wait for it to complete.
  keymgr_start(diversification);
  return keymgr_wait_until_done();
}

/**
 * Clear the requested sideload slot.
 *
 * The `slot` parameter should be one of:
 *   - KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_AES
 *   - KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_KMAC
 *   - KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN
 *
 * @param slot Value to write to the SIDELOAD_CLEAR register.
 */
static status_t keymgr_sideload_clear(uint32_t slot) {
  HARDENED_TRY(keymgr_is_idle());

  // Ensure that the entropy complex has been initialized.
  HARDENED_TRY(entropy_complex_check());

  // Set SIDELOAD_CLEAR to begin continuously clearing the requested slot.
  abs_mmio_write32(
      kBaseAddr + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
      bitfield_field32_write(0, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD, slot));

  // Read back the value (hardening measure).
  uint32_t sideload_clear =
      abs_mmio_read32(kBaseAddr + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET);
  if (bitfield_field32_read(sideload_clear, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD) !=
      slot) {
    return OTCRYPTO_FATAL_ERR;
  }

  // Spin for 100 microseconds.
  // TODO: this value seems to work for tests, but it would be good to run a
  // more principled analysis.
  busy_spin_micros(100);

  // Stop continuous clearing.
  abs_mmio_write32(
      kBaseAddr + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
      bitfield_field32_write(0, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD,
                             KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_NONE));

  return OTCRYPTO_OK;
}

status_t keymgr_sideload_clear_aes(void) {
  return keymgr_sideload_clear(KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_AES);
}

status_t keymgr_sideload_clear_kmac(void) {
  return keymgr_sideload_clear(KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_KMAC);
}

status_t keymgr_sideload_clear_otbn(void) {
  return keymgr_sideload_clear(KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN);
}
