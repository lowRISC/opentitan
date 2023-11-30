// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr.h"

#include <assert.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.

#define KEYMGR_ASSERT(a, b) static_assert(a == b, "Bad value for " #a)
KEYMGR_ASSERT(kKeymgrStateReset, KEYMGR_WORKING_STATE_STATE_VALUE_RESET);
KEYMGR_ASSERT(kKeymgrStateInit, KEYMGR_WORKING_STATE_STATE_VALUE_INIT);
KEYMGR_ASSERT(kKeymgrStateCreatorRootKey,
              KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY);
KEYMGR_ASSERT(kKeymgrStateOwnerIntermediateKey,
              KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY);
KEYMGR_ASSERT(kKeymgrStateOwnerKey, KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_KEY);
KEYMGR_ASSERT(kKeymgrStateDisabled, KEYMGR_WORKING_STATE_STATE_VALUE_DISABLED);
KEYMGR_ASSERT(kKeymgrStateInvalid, KEYMGR_WORKING_STATE_STATE_VALUE_INVALID);

enum {
  kBase = TOP_EARLGREY_KEYMGR_BASE_ADDR,
};

/**
 * Checks the key manager `expected_state`.
 *
 * This function reads and clears the status and error code registers.
 *
 * @return `kErrorOk` if the key manager is at the `expected_state` and the
 * status is idle or success.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t expected_state_check(uint32_t expected_state) {
  // Read and clear the status register by writing back the read value,
  // polling until the status is non-WIP.
  uint32_t op_status;
  uint32_t op_status_field;
  do {
    op_status = abs_mmio_read32(kBase + KEYMGR_OP_STATUS_REG_OFFSET);
    abs_mmio_write32(kBase + KEYMGR_OP_STATUS_REG_OFFSET, op_status);
    op_status_field =
        bitfield_field32_read(op_status, KEYMGR_OP_STATUS_STATUS_FIELD);
  } while (op_status_field == KEYMGR_OP_STATUS_STATUS_VALUE_WIP ||
           op_status_field == KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  // Read and clear the error register by writing back the read value.
  uint32_t error_code = abs_mmio_read32(kBase + KEYMGR_ERR_CODE_REG_OFFSET);
  abs_mmio_write32(kBase + KEYMGR_ERR_CODE_REG_OFFSET, error_code);

  // Read the working state with sec_mmio so that we can check the expected
  // value periodically.
  uint32_t got_state = sec_mmio_read32(kBase + KEYMGR_WORKING_STATE_REG_OFFSET);
  if (op_status_field == KEYMGR_OP_STATUS_STATUS_VALUE_IDLE &&
      error_code == 0u && got_state == expected_state) {
    return kErrorOk;
  }
  return kErrorKeymgrInternal;
}

void keymgr_entropy_reseed_interval_set(uint16_t entropy_reseed_interval) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kKeymgrSecMmioEntropyReseedIntervalSet, 1);
  uint32_t reg = bitfield_field32_write(
      0, KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_FIELD, entropy_reseed_interval);
  sec_mmio_write32_shadowed(kBase + KEYMGR_RESEED_INTERVAL_SHADOWED_REG_OFFSET,
                            reg);
}

void keymgr_sw_binding_set(
    const keymgr_binding_value_t *binding_value_sealing,
    const keymgr_binding_value_t *binding_value_attestation) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kKeymgrSecMmioSwBindingSet, 17);

  // Write and lock (rw0c) the software binding value. This register is unlocked
  // by hardware upon a successful state transition.
  for (size_t i = 0; i < ARRAYSIZE(binding_value_sealing->data); ++i) {
    sec_mmio_write32(
        kBase + KEYMGR_SEALING_SW_BINDING_0_REG_OFFSET + i * sizeof(uint32_t),
        binding_value_sealing->data[i]);
  }
  for (size_t i = 0; i < ARRAYSIZE(binding_value_attestation->data); ++i) {
    sec_mmio_write32(
        kBase + KEYMGR_ATTEST_SW_BINDING_0_REG_OFFSET + i * sizeof(uint32_t),
        binding_value_attestation->data[i]);
  }
  sec_mmio_write32(kBase + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);
}

void keymgr_sw_binding_unlock_wait(void) {
  while (!abs_mmio_read32(kBase + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET)) {
  }
  // Ignore the return value since this read is performed to check and update
  // the expected value.
  OT_DISCARD(sec_mmio_read32(kBase + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET));
}

void keymgr_creator_max_ver_set(uint32_t max_key_ver) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kKeymgrSecMmioCreatorMaxVerSet, 2);
  // Write and lock (rw0c) the max key version.
  sec_mmio_write32_shadowed(
      kBase + KEYMGR_MAX_CREATOR_KEY_VER_SHADOWED_REG_OFFSET, max_key_ver);
  sec_mmio_write32(kBase + KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET, 0);
}

void keymgr_owner_int_max_ver_set(uint32_t max_key_ver) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kKeymgrSecMmioOwnerIntMaxVerSet, 2);
  // Write and lock (rw0c) the max key version.
  sec_mmio_write32_shadowed(
      kBase + KEYMGR_MAX_OWNER_INT_KEY_VER_SHADOWED_REG_OFFSET, max_key_ver);
  sec_mmio_write32(kBase + KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_REG_OFFSET, 0);
}

void keymgr_owner_max_ver_set(uint32_t max_key_ver) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kKeymgrSecMmioOwnerMaxVerSet, 2);
  // Write and lock (rw0c) the max key version.
  sec_mmio_write32_shadowed(
      kBase + KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_OFFSET, max_key_ver);
  sec_mmio_write32(kBase + KEYMGR_MAX_OWNER_KEY_VER_REGWEN_REG_OFFSET, 0);
}

void keymgr_advance_state(void) {
  uint32_t reg =
      bitfield_field32_write(0, KEYMGR_CONTROL_SHADOWED_DEST_SEL_FIELD,
                             KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE);
  reg = bitfield_field32_write(reg, KEYMGR_CONTROL_SHADOWED_OPERATION_FIELD,
                               KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE);
  abs_mmio_write32_shadowed(kBase + KEYMGR_CONTROL_SHADOWED_REG_OFFSET, reg);

  abs_mmio_write32(kBase + KEYMGR_START_REG_OFFSET, 1);
}

rom_error_t keymgr_state_check(keymgr_state_t expected_state) {
  return expected_state_check(expected_state);
}

/**
 * Fails if the keymgr is not idle.
 *
 * @return OK if the key manager is idle, kErrorKeymgrInternal otherwise.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t keymgr_is_idle(void) {
  uint32_t reg = abs_mmio_read32(kBase + KEYMGR_OP_STATUS_REG_OFFSET);
  uint32_t status = bitfield_field32_read(reg, KEYMGR_OP_STATUS_STATUS_FIELD);
  if (launder32(status) == KEYMGR_OP_STATUS_STATUS_VALUE_IDLE) {
    HARDENED_CHECK_EQ(status, KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
    return kErrorOk;
  }
  return kErrorKeymgrInternal;
}

/**
 * Wait for the key manager to finish an operation.
 *
 * Polls the key manager until it is no longer busy. If the operation completed
 * successfully or the key manager was already idle, returns kErrorOk. If
 * there was an error during the operation, reads and clears the error code
 * and returns kErrorKeymgrInternal.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t keymgr_wait_until_done(void) {
  // Poll the OP_STATUS register until it is something other than "WIP".
  uint32_t reg;
  uint32_t status;
  do {
    // Read OP_STATUS and then clear by writing back the value we read.
    reg = abs_mmio_read32(kBase + KEYMGR_OP_STATUS_REG_OFFSET);
    abs_mmio_write32(kBase + KEYMGR_OP_STATUS_REG_OFFSET, reg);
    status = bitfield_field32_read(reg, KEYMGR_OP_STATUS_STATUS_FIELD);
  } while (status == KEYMGR_OP_STATUS_STATUS_VALUE_WIP);

  // Check if the key manager reported errors. If it is already idle or
  // completed an operation successfully, return an OK status. A `WIP` status
  // should not be possible because of the check above.
  switch (launder32(status)) {
    case KEYMGR_OP_STATUS_STATUS_VALUE_IDLE:
      HARDENED_CHECK_EQ(status, KEYMGR_OP_STATUS_STATUS_VALUE_IDLE);
      return kErrorOk;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS:
      HARDENED_CHECK_EQ(status, KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
      return kErrorOk;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR: {
      // Clear the ERR_CODE register before returning.
      uint32_t err_code = abs_mmio_read32(kBase + KEYMGR_ERR_CODE_REG_OFFSET);
      abs_mmio_write32(kBase + KEYMGR_ERR_CODE_REG_OFFSET, err_code);
      return kErrorKeymgrInternal;
    }
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return kErrorKeymgrInternal;
}

rom_error_t keymgr_generate_attestation_key_otbn(
    keymgr_diversification_t diversification) {
  HARDENED_RETURN_IF_ERROR(keymgr_is_idle());

  // Select OTBN as the destination.
  uint32_t ctrl =
      bitfield_field32_write(0, KEYMGR_CONTROL_SHADOWED_DEST_SEL_FIELD,
                             KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN);

  // Select the attestation CDI.
  ctrl = bitfield_bit32_write(ctrl, KEYMGR_CONTROL_SHADOWED_CDI_SEL_BIT, true);

  // Select the "generate" operation.
  ctrl = bitfield_field32_write(
      ctrl, KEYMGR_CONTROL_SHADOWED_OPERATION_FIELD,
      KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT);

  // Write the control register.
  abs_mmio_write32_shadowed(kBase + KEYMGR_CONTROL_SHADOWED_REG_OFFSET, ctrl);

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

  // Block until keymgr is done.
  return keymgr_wait_until_done();
}

rom_error_t keymgr_sideload_clear_otbn(void) {
  HARDENED_RETURN_IF_ERROR(keymgr_is_idle());

  // Set SIDELOAD_CLEAR to begin continuously clearing the requested slot.
  abs_mmio_write32(
      kBase + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
      bitfield_field32_write(0, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD,
                             KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN));

  // Read back the value (hardening measure).
  uint32_t sideload_clear =
      abs_mmio_read32(kBase + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET);
  if (bitfield_field32_read(sideload_clear, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD) !=
      KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN) {
    return kErrorKeymgrInternal;
  }

  // Spin for 100 microseconds.
  // TODO(#20024): this value seems to work for tests, but it would be good to
  // run a more principled analysis.
  busy_spin_micros(100);

  // Stop continuous clearing.
  abs_mmio_write32(
      kBase + KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
      bitfield_field32_write(0, KEYMGR_SIDELOAD_CLEAR_VAL_FIELD,
                             KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_NONE));

  return kErrorOk;
}
