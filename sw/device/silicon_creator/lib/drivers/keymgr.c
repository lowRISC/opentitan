// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr.h"

#include "sw/device/lib/base/freestanding/assert.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"

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
static rom_error_t check_expected_state(uint32_t expected_state) {
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

  uint32_t got_state = abs_mmio_read32(kBase + KEYMGR_WORKING_STATE_REG_OFFSET);
  if (op_status_field == KEYMGR_OP_STATUS_STATUS_VALUE_IDLE &&
      error_code == 0u && got_state == expected_state) {
    return kErrorOk;
  }
  return kErrorKeymgrInternal;
}

rom_error_t keymgr_init(uint16_t entropy_reseed_interval) {
  RETURN_IF_ERROR(check_expected_state(kKeymgrStateReset));
  uint32_t reg = bitfield_field32_write(
      0, KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_FIELD, entropy_reseed_interval);
  abs_mmio_write32_shadowed(kBase + KEYMGR_RESEED_INTERVAL_SHADOWED_REG_OFFSET,
                            reg);
  return kErrorOk;
}

void keymgr_set_next_stage_inputs(
    const keymgr_binding_value_t *binding_value_sealing,
    const keymgr_binding_value_t *binding_value_attestation,
    uint32_t max_key_ver) {
  // Write and lock (rw0c) the software binding value. This register is unlocked
  // by hardware upon a successful state transition.
  // FIXME: Consider using sec_mmio module for the following register writes.
  for (size_t i = 0; i < ARRAYSIZE(binding_value_sealing->data); ++i) {
    abs_mmio_write32(
        kBase + KEYMGR_SEALING_SW_BINDING_0_REG_OFFSET + i * sizeof(uint32_t),
        binding_value_sealing->data[i]);
  }
  for (size_t i = 0; i < ARRAYSIZE(binding_value_attestation->data); ++i) {
    abs_mmio_write32(
        kBase + KEYMGR_ATTEST_SW_BINDING_0_REG_OFFSET + i * sizeof(uint32_t),
        binding_value_attestation->data[i]);
  }
  abs_mmio_write32(kBase + KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);

  // Write and lock (rw0c) the max key version.
  abs_mmio_write32_shadowed(
      kBase + KEYMGR_MAX_CREATOR_KEY_VER_SHADOWED_REG_OFFSET, max_key_ver);
  abs_mmio_write32(kBase + KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET, 0);
}

void keymgr_advance_state(void) {
  uint32_t reg = bitfield_bit32_write(0, KEYMGR_CONTROL_START_BIT, true);
  reg = bitfield_field32_write(reg, KEYMGR_CONTROL_DEST_SEL_FIELD,
                               KEYMGR_CONTROL_DEST_SEL_VALUE_NONE);
  reg = bitfield_field32_write(reg, KEYMGR_CONTROL_OPERATION_FIELD,
                               KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE);
  abs_mmio_write32(kBase + KEYMGR_CONTROL_REG_OFFSET, reg);
}

rom_error_t keymgr_check_state(keymgr_state_t expected_state) {
  return check_expected_state(expected_state);
}
