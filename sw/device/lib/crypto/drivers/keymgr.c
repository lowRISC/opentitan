// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/keymgr.h"

#include "hw/top/dt/keymgr.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/hart.h"

#include "hw/top/keymgr_regs.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('d', 'k', 'r')

static const dt_keymgr_t kKeymgrDt = kDtKeymgr;

static inline uint32_t keymgr_base(void) {
  return dt_keymgr_primary_reg_block(kKeymgrDt);
}

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
  uint32_t reg = abs_mmio_read32(keymgr_base() + KEYMGR_OP_STATUS_REG_OFFSET);
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
static status_t keymgr_start(keymgr_diversification_t diversification) {
  const uint32_t kBase = keymgr_base();
  // Set the version.
  abs_mmio_write32(kBase + KEYMGR_KEY_VERSION_REG_OFFSET,
                   diversification.version);
  // Set the salt.
  for (size_t i = 0; i < kKeymgrSaltNumWords; i++) {
    abs_mmio_write32(kBase + KEYMGR_SALT_0_REG_OFFSET + (i * sizeof(uint32_t)),
                     diversification.salt[i]);
  }

  // Issue the start command.
  abs_mmio_write32(kBase + KEYMGR_START_REG_OFFSET, 1 << KEYMGR_START_EN_BIT);

  return OTCRYPTO_OK;
}

/**
 * Wait for the key manager to finish an operation.
 *
 * Polls the key manager until it is no longer busy. If the operation completed
 * successfully, returns OTCRYPTO_OK. If there was an error during the
 * operation, reads and clears the error code and returns OTCRYPTO_RECOV_ERR;
 * the operation can be retried afterwards.
 *
 * This function assumes an operation has already been started by the caller.
 * The function traps if the keymgr is already idle.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t keymgr_wait_until_done(void) {
  // Poll the OP_STATUS register until it is something other than "WIP".
  uint32_t reg;
  uint32_t status;
  do {
    reg = abs_mmio_read32(keymgr_base() + KEYMGR_OP_STATUS_REG_OFFSET);
    status = bitfield_field32_read(reg, KEYMGR_OP_STATUS_STATUS_FIELD);
  } while (status == KEYMGR_OP_STATUS_STATUS_VALUE_WIP);

  // Clear OP_STATUS by writing back the value we read.
  abs_mmio_write32(keymgr_base() + KEYMGR_OP_STATUS_REG_OFFSET, reg);

  // Check if the key manager reported errors. If it completed an operation
  // successfully, return an OK status. No other statuses (e.g. WIP) should
  // be possible.
  // The `IDLE` status is left unhandled because the keymgr should never be
  // idle after an operation has been started by the caller.
  switch (status) {
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS:
      HARDENED_CHECK_EQ(launder32(status),
                        KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
      return OTCRYPTO_OK;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR: {
      // Clear the ERR_CODE register before returning.
      uint32_t err_code =
          abs_mmio_read32(keymgr_base() + KEYMGR_ERR_CODE_REG_OFFSET);
      abs_mmio_write32(keymgr_base() + KEYMGR_ERR_CODE_REG_OFFSET, err_code);
      HARDENED_CHECK_EQ(launder32(status),
                        KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR);
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
    abs_mmio_write32_shadowed(                                                 \
        keymgr_base() + KEYMGR_CONTROL_SHADOWED_REG_OFFSET, ctrl);             \
  } while (false);

/**
 * Verify the control register of the key manager.
 *
 * @param dest (NONE, AES, OTBN, or KMAC)
 * @param operation (GENERATE_SW or GENERATE_HW)
 */
#define VERIFY_CTRL(dest, operation)                                           \
  do {                                                                         \
    uint32_t ctrl =                                                            \
        bitfield_field32_write(0, KEYMGR_CONTROL_SHADOWED_DEST_SEL_FIELD,      \
                               KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_##dest); \
    ctrl = bitfield_bit32_write(ctrl, KEYMGR_CONTROL_SHADOWED_CDI_SEL_BIT,     \
                                false);                                        \
    ctrl = bitfield_field32_write(                                             \
        ctrl, KEYMGR_CONTROL_SHADOWED_OPERATION_FIELD,                         \
        KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_##operation##_OUTPUT);         \
    HARDENED_CHECK_EQ(                                                         \
        abs_mmio_read32(keymgr_base() + KEYMGR_CONTROL_SHADOWED_REG_OFFSET),   \
        ctrl);                                                                 \
  } while (false);

status_t keymgr_generate_key_sw(keymgr_diversification_t diversification,
                                keymgr_output_t *key) {
  // Ensure that the entropy complex has been initialized and keymgr is idle.
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate a software-visible key.
  WRITE_CTRL(NONE, GENERATE_SW);

  // Start the operation and wait for it to complete.
  HARDENED_TRY(keymgr_start(diversification));
  HARDENED_TRY(keymgr_wait_until_done());

  // Check the control register.
  VERIFY_CTRL(NONE, GENERATE_SW);

  // Collect the output. To avoid side-channel lekage, first randomize the
  // destination buffers using memshred. Then copy the key using a hardened
  // memcpy.
  uint32_t share0 = keymgr_base() + KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET;
  uint32_t share1 = keymgr_base() + KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET;
  HARDENED_TRY(hardened_memshred(key->share0, kKeymgrOutputShareNumWords));
  HARDENED_TRY(hardened_memcpy(key->share0, (uint32_t *)share0,
                               kKeymgrOutputShareNumWords));
  HARDENED_TRY(hardened_memshred(key->share1, kKeymgrOutputShareNumWords));
  HARDENED_TRY(hardened_memcpy(key->share1, (uint32_t *)share1,
                               kKeymgrOutputShareNumWords));

  return OTCRYPTO_OK;
}

status_t keymgr_generate_key_aes(keymgr_diversification_t diversification) {
  // Ensure that the entropy complex has been initialized and keymgr is idle.
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate an AES key.
  WRITE_CTRL(AES, GENERATE_HW);

  // Start the operation and wait for it to complete.
  HARDENED_TRY(keymgr_start(diversification));
  HARDENED_TRY(keymgr_wait_until_done());
  // Check the control register.
  VERIFY_CTRL(AES, GENERATE_HW);

  return OTCRYPTO_OK;
}

status_t keymgr_generate_key_kmac(keymgr_diversification_t diversification) {
  // Ensure that the entropy complex has been initialized and keymgr is idle.
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate a KMAC key.
  WRITE_CTRL(KMAC, GENERATE_HW);

  // Start the operation and wait for it to complete.
  HARDENED_TRY(keymgr_start(diversification));
  HARDENED_TRY(keymgr_wait_until_done());
  // Check the control register.
  VERIFY_CTRL(KMAC, GENERATE_HW);
  return OTCRYPTO_OK;
}

status_t keymgr_generate_key_otbn(keymgr_diversification_t diversification) {
  // Ensure that the entropy complex has been initialized and keymgr is idle.
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(keymgr_is_idle());

  // Set the control register to generate an OTBN key.
  WRITE_CTRL(OTBN, GENERATE_HW);

  // Start the operation and wait for it to complete.
  HARDENED_TRY(keymgr_start(diversification));
  HARDENED_TRY(keymgr_wait_until_done());
  // Check the control register.
  VERIFY_CTRL(OTBN, GENERATE_HW);
  return OTCRYPTO_OK;
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
  // Ensure that the entropy complex has been initialized and keymgr is idle.
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(keymgr_is_idle());

  // Set SIDELOAD_CLEAR to begin continuously clearing the requested slot.
  abs_mmio_write32(
      keymgr_base() + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
      bitfield_field32_write(0, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD, slot));

  // Read back the value (hardening measure).
  uint32_t sideload_clear =
      abs_mmio_read32(keymgr_base() + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET);
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
      keymgr_base() + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
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
