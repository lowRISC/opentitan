// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/keymgr_dpe.h"

#include <assert.h>

#include "hw/top/dt/keymgr_dpe.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#include "hw/top/keymgr_dpe_regs.h"  // Generated.

#define KEYMGR_DPE_ASSERT(a, b) static_assert(a == b, "Bad value for " #a)
KEYMGR_DPE_ASSERT(kScKeymgrDPEStateReset,
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_RESET);
KEYMGR_DPE_ASSERT(kScKeymgrDPEStateAvailable,
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE);
KEYMGR_DPE_ASSERT(kScKeymgrDPEStateDisabled,
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_DISABLED);
KEYMGR_DPE_ASSERT(kScKeymgrDPEStateInvalid,
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_INVALID);

/**
 * Internal keymgr dpe operation definition
 */
typedef enum sc_keymgr_dpe_operation {
  kScKeymgrDPEOpsAdvance = 0,
  kScKeymgrDPEOpsEraseSlot = 1,
  kScKeymgrDPEOpsGenSwKey = 2,
  kScKeymgrDPEOpsGenHwKey = 3,
  kScKeymgrDPEOpsDisable = 4,
  kScKeymgrDPEOpsLoadRootKey = 5,
} sc_keymgr_dpe_operation_t;

/**
 * Base address of the keymgr dpe registers.
 */
static inline uint32_t sc_keymgr_dpe_base(void) {
  return dt_keymgr_dpe_reg_block(kDtKeymgrDpe, kDtKeymgrDpeRegBlockCore);
}

/**
 * Sets the context of the control register for the next command.
 *
 * @param exl_sw_binding Should additional hw bindings be used during the
 * next advance call. Only impact DPE context generation if either the
 * creator root key / owner int key / owner key is being generated.
 * @param ops The type of operation to execute next.
 * @param sel_src_slot Source slot when either advancing a DPE context inside
 * the slot or if an HW / SW key is being generated.
 * @param sel_dst_slot Destination slot in which the next advance call will
 * load the newly generated DPE context.
 * @param key_dest Determine the sideload port when deriving a HW key.
 */
void sc_keymgr_dpe_control_reg_set(
    const sc_keymgr_dpe_sw_binding_t exl_sw_binding, const uint32_t ops,
    const sc_keymgr_dpe_dest_t key_dest, uint32_t sel_src_slot,
    uint32_t sel_dst_slot) {
  // Build the control register
  uint32_t ctrl = 0;
  ctrl = bitfield_field32_write(
      ctrl, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_FIELD, ops);
  ctrl = bitfield_field32_write(
      ctrl, KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_FIELD, key_dest);
  ctrl = bitfield_field32_write(
      ctrl, KEYMGR_DPE_CONTROL_SHADOWED_SLOT_SRC_SEL_FIELD, sel_src_slot);
  ctrl = bitfield_field32_write(
      ctrl, KEYMGR_DPE_CONTROL_SHADOWED_SLOT_DST_SEL_FIELD, sel_dst_slot);
  ctrl = bitfield_bit32_write(
      ctrl, KEYMGR_DPE_CONTROL_SHADOWED_SW_BINDING_ONLY_BIT, exl_sw_binding);

  // Write the control register.
  abs_mmio_write32_shadowed(
      sc_keymgr_dpe_base() + KEYMGR_DPE_CONTROL_SHADOWED_REG_OFFSET, ctrl);
}

/**
 * Start the command.
 */
void sc_keymgr_dpe_start_operation(void) {
  // Issue the start command.
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_START_REG_OFFSET,
                   1 << KEYMGR_DPE_START_EN_BIT);
}

/**
 * Wait for the key manager dpe to finish an operation.
 *
 * Polls the key manager dpe until it is no longer busy. If the operation
 * completed successfully, returns kErrorOk. If there was an error during the
 * operation, reads and clears the error code and returns kErrorKeymgrInternal.
 *
 * @return `kErrorOk` if the status is either "idle" or the operation
 * finished with "done_successfully", `kErrorKeymgrInternal`otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_wait_until_done(void) {
  // Poll the OP_STATUS register until it is something other than "WIP".
  uint32_t reg;
  uint32_t status;
  do {
    // Read OP_STATUS and then clear by writing back the value we read.
    reg =
        abs_mmio_read32(sc_keymgr_dpe_base() + KEYMGR_DPE_OP_STATUS_REG_OFFSET);
    abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                     reg);
    status = bitfield_field32_read(reg, KEYMGR_DPE_OP_STATUS_STATUS_FIELD);
  } while (status == KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);

  // Check if the keymgr_dpe reported errors. If it completed an operation
  // successfully, return an OK status. A `WIP` status should not be possible
  // because of the check above.
  // The `IDLE` status is left unhandled because the keymgr_dpe should never
  // be idle after an operation has been started by the caller.
  switch (launder32(status)) {
    case KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS:
      HARDENED_CHECK_EQ(status, KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
      return kErrorOk;
    case KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR: {
      // Clear the ERR_CODE register before returning.
      uint32_t err_code = abs_mmio_read32(sc_keymgr_dpe_base() +
                                          KEYMGR_DPE_ERR_CODE_REG_OFFSET);
      abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                       err_code);
      return kErrorKeymgrInternal;
    }
    default:
      // Should be unreachable.
      HARDENED_TRAP();
      return kErrorKeymgrInternal;
  }
}

/**
 * Checks the key manager dpe `expected_state`.
 *
 * This function reads and clears the status and error code registers.
 *
 * @return `kErrorOk` if the key manager dpe is at the `expected_state` and the
 * status is idle or success.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t expected_state_check(uint32_t expected_state) {
  // Read and clear the status register by writing back the read value,
  // polling until the status is non-WIP.
  uint32_t op_status;
  uint32_t op_status_field;
  do {
    op_status =
        abs_mmio_read32(sc_keymgr_dpe_base() + KEYMGR_DPE_OP_STATUS_REG_OFFSET);
    abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_OP_STATUS_REG_OFFSET,
                     op_status);
    op_status_field =
        bitfield_field32_read(op_status, KEYMGR_DPE_OP_STATUS_STATUS_FIELD);
  } while (op_status_field == KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP ||
           op_status_field == KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  // Read and clear the error register by writing back the read value.
  uint32_t error_code =
      abs_mmio_read32(sc_keymgr_dpe_base() + KEYMGR_DPE_ERR_CODE_REG_OFFSET);
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                   error_code);

  // Read the working state with sec_mmio so that we can check the expected
  // value periodically.
  // TODO(#30665): changed this towards abs_mmio_read32(...) instead of
  // sec_mmio_read32(...) as otherwise several test fail.
  // The test currently investigating is: 0.rom_e2e_asm_init_test_unlocked0!
  // When fixing this issue the keymgr_dpe_unittest.cc must reflect the
  // changes too!
  uint32_t got_state = abs_mmio_read32(sc_keymgr_dpe_base() +
                                       KEYMGR_DPE_WORKING_STATE_REG_OFFSET);
  if (op_status_field == KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE &&
      error_code == 0u && got_state == expected_state) {
    return kErrorOk;
  }
  return kErrorKeymgrInternal;
}

/**
 * Fails if the keymgr_dpe is not idle.
 *
 * @return OK if the key manager is idle, kErrorKeymgrInternal otherwise.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t keymgr_dpe_is_idle(void) {
  uint32_t reg =
      abs_mmio_read32(sc_keymgr_dpe_base() + KEYMGR_DPE_OP_STATUS_REG_OFFSET);
  uint32_t status =
      bitfield_field32_read(reg, KEYMGR_DPE_OP_STATUS_STATUS_FIELD);
  if (launder32(status) == KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE) {
    HARDENED_CHECK_EQ(status, KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE);
    return kErrorOk;
  }
  return kErrorKeymgrInternal;
}

/**
 * Wrapper for any advance call.
 *
 * All advance call will use this wrapper except for the first one as there
 * the initial state is different.
 *
 * @param exl_sw_binding should the software binding be used exclusively
 * @param adv_data all required data for a successful advance call
 *
 * @return `kErrorOk` if the advance call was successfully started
 */
OT_WARN_UNUSED_RESULT
static rom_error_t sc_keymgr_dpe_advance_wrapper(
    const sc_keymgr_dpe_sw_binding_t exl_sw_binding,
    sc_keymgr_dpe_advance_data_t adv_data) {
  // Set the current key version
  sc_keymgr_dpe_max_ver_set(adv_data.version);

  // Set the sw binding
  sc_keymgr_dpe_sw_binding_set(adv_data.binding_value);

  // Set the policy for the DPE context
  sc_keymgr_dpe_policy_set(adv_data.policy);

  // Set the control register entries
  sc_keymgr_dpe_control_reg_set(
      exl_sw_binding, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, adv_data.sel_src_slot,
      adv_data.sel_dst_slot);

  // Start the advance operation
  sc_keymgr_dpe_start_operation();
  return kErrorOk;
}

/**
 * Sets the entropy reseed interval of the key manager dpe.
 */
void sc_keymgr_dpe_entropy_reseed_interval_set(uint16_t reseed_interval) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kScKeymgrDPESecMmioReseedIntervalSet, 1);
  uint32_t reg = bitfield_field32_write(
      0, KEYMGR_DPE_RESEED_INTERVAL_SHADOWED_VAL_FIELD, reseed_interval);
  sec_mmio_write32_shadowed(
      sc_keymgr_dpe_base() + KEYMGR_DPE_RESEED_INTERVAL_SHADOWED_REG_OFFSET,
      reg);
}

/**
 * Sets the key manager dpe software binding input.
 */
void sc_keymgr_dpe_sw_binding_set(keymgr_dpe_binding_value_t *binding_value) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kScKeymgrDPESecMmioSwBindingSet, 8);
  // Write and lock (rw0c) the software binding value. This register is
  // unlocked by hardware upon a successful state transition.
  for (size_t i = 0; i < ARRAYSIZE(binding_value->data); ++i) {
    sec_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_SW_BINDING_0_REG_OFFSET +
                         i * sizeof(uint32_t),
                     binding_value->data[i]);
  }
  // Lock (clear) the sw binding register here
  // TODO(#30665): sec_mmio_writes currently does not work properly with
  // auto reset register. The reason is if we start an advance operation
  // then the HW will set this register afterwards. However, the
  // sec_mmio_check_value() function still expects the written value of 0!
  // When fixing this issue the keymgr_dpe_unittest.cc must reflect the changes
  // too!
  abs_mmio_write32(
      sc_keymgr_dpe_base() + KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET, 0);
}

/**
 * Blocks until the software binding registers are unlocked.
 */
void sc_keymgr_dpe_sw_binding_unlock_wait(void) {
  // wait until the sw binding register is unlocked
  while (!abs_mmio_read32(sc_keymgr_dpe_base() +
                          KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET)) {
  }
  // Ignore the return value since this read is performed to check and update
  // the expected value.
  OT_DISCARD(sec_mmio_read32(sc_keymgr_dpe_base() +
                             KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET));
}

/**
 * Sets the current max key version used to advance a DPE context
 */
void sc_keymgr_dpe_max_ver_set(uint32_t max_key_ver) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kScKeymgrDPESecMmioMaxVerSet, 1);
  // Write and lock (rw0c) the max key version.
  sec_mmio_write32_shadowed(
      sc_keymgr_dpe_base() + KEYMGR_DPE_MAX_KEY_VER_SHADOWED_REG_OFFSET,
      max_key_ver);
  // TODO(#30665): sec_mmio_writes currently does not work > The reason is if
  // we start an advance operation then the HW will set this register
  // afterwards. However the sec_mmio_check_value() function still expects the
  // written 0 value! When fixing this issue the keymgr_dpe_unittest.cc must
  // reflect the changes too!
  abs_mmio_write32(
      sc_keymgr_dpe_base() + KEYMGR_DPE_MAX_KEY_VER_REGWEN_REG_OFFSET, 0);
}

/**
 * Sets the key version used to generate a key
 */
void sc_keymgr_dpe_key_ver_set(uint32_t key_ver) {
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_KEY_VERSION_REG_OFFSET,
                   key_ver);
}

/**
 * Sets all the slot policies for the next advance call.
 */
void sc_keymgr_dpe_policy_set(sc_keymgr_dpe_policies_t policy) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kScKeymgrDPESecMmioSlotPolicy, 1);
  // Build, write and lock (rw0c) the policy field.
  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, KEYMGR_DPE_SLOT_POLICY_ALLOW_CHILD_BIT,
                             policy.child);
  reg = bitfield_bit32_write(reg, KEYMGR_DPE_SLOT_POLICY_EXPORTABLE_BIT,
                             policy.expo);
  reg = bitfield_bit32_write(reg, KEYMGR_DPE_SLOT_POLICY_RETAIN_PARENT_BIT,
                             policy.parent);
  sec_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_SLOT_POLICY_REG_OFFSET,
                   reg);
  // TODO(#30665): sec_mmio_writes currently does not work > The reason is if
  // we start an advance operation then the HW will set this register
  // afterwards. However the sec_mmio_check_value() function still expects the
  // written 0 value! When fixing this issue the keymgr_dpe_unittest.cc must
  // reflect the changes too!
  abs_mmio_write32(
      sc_keymgr_dpe_base() + KEYMGR_DPE_SLOT_POLICY_REGWEN_REG_OFFSET, 0);
}

/**
 * Checks the state of the key manager and compares against the provided
 * value.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_state_check(sc_keymgr_dpe_state_t expected_state) {
  return expected_state_check(expected_state);
}

/**
 * Generate a key manager dpe key and sideload to the requested block.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_generate_key(
    const sc_keymgr_dpe_dest_t destination,
    sc_keymgr_dpe_diversification_t diversification) {
  // Wait until the keymgr dpe has finished any previous operation
  // Keys can only be generated in the Available state
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));

  // Determine if destination enforce either the HW or SW key
  const uint32_t ops =
      (destination == kScKeymgrDPEDestNone)
          ? KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_SW_OUTPUT
          : KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT;

  // Set the current key version
  sc_keymgr_dpe_key_ver_set(diversification.version);

  // Set the salt value for the key generation
  for (size_t i = 0; i < kScKeymgrDPESaltNumWords; i++) {
    abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_SALT_0_REG_OFFSET +
                         i * sizeof(uint32_t),
                     diversification.salt[i]);
  }

  // Set the control register entries
  sc_keymgr_dpe_control_reg_set(kScKeymgrDPEUseAdditionalHwBinding, ops,
                                destination, diversification.sel_src_slot, 0);

  // Start the advance operation
  sc_keymgr_dpe_start_operation();

  // Blocks until the key is generated
  return sc_keymgr_dpe_wait_until_done();
}

/**
 * Read the generated sw key.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_read_key(uint32_t *share0, uint32_t *share1) {
  // Return a error if the keymgr_dpe is not idle
  HARDENED_RETURN_IF_ERROR(keymgr_dpe_is_idle());
  // To avoid side-channel leakage, first randomize the destination buffers
  // using memshred and then read the key.
  hardened_memshred(share0, kScKeymgrDPEKeyNumWords);
  hardened_memcpy(share0,
                  (uint32_t *)(sc_keymgr_dpe_base() +
                               KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET),
                  kScKeymgrDPEKeyNumWords);
  hardened_memshred(share1, kScKeymgrDPEKeyNumWords);
  hardened_memcpy(share1,
                  (uint32_t *)(sc_keymgr_dpe_base() +
                               KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET),
                  kScKeymgrDPEKeyNumWords);
  return kErrorOk;
}

/**
 * Clear the requested sideloaded key slot.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_clear_key(sc_keymgr_dpe_dest_t destination) {
  uint32_t reg = 0;
  // Wait until the keymgr dpe has finished any previous operation
  HARDENED_RETURN_IF_ERROR(keymgr_dpe_is_idle());

  // Set SIDELOAD_CLEAR to begin continuously clearing the requested slot.
  reg = bitfield_field32_write(reg, KEYMGR_DPE_SIDELOAD_CLEAR_VAL_FIELD,
                               destination);
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                   reg);

  // Read back the value (hardening measure).
  uint32_t sideload_clear = abs_mmio_read32(
      sc_keymgr_dpe_base() + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET);
  if (bitfield_field32_read(
          sideload_clear, KEYMGR_DPE_SIDELOAD_CLEAR_VAL_FIELD) != destination) {
    return kErrorKeymgrInternal;
  }

  // Stop continuous clearing.
  reg = 0;
  reg = bitfield_field32_write(reg, KEYMGR_DPE_SIDELOAD_CLEAR_VAL_FIELD,
                               KEYMGR_DPE_SIDELOAD_CLEAR_VAL_VALUE_NONE);
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                   reg);

  return kErrorOk;
}

/**
 * Enforces that only sw bindings are used for the advancement
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_dpe_context(
    sc_keymgr_dpe_advance_data_t adv_data) {
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));
  return sc_keymgr_dpe_advance_wrapper(kScKeymgrDPEUseExclusiveSwBinding,
                                       adv_data);
}

/**
 * Write into the lock register for the UDS
 */
rom_error_t sc_keymgr_dpe_lock_uds(void) {
  // Issue the start command.
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_LOAD_KEY_LOCK_REG_OFFSET,
                   1 << KEYMGR_DPE_LOAD_KEY_LOCK_LOCK_BIT);
  return kErrorOk;
}

/**
 * Load the UDS into the provided destination slot
 */
// TODO(#30667): Verify if the max key version needs to be written here too!
//              When loading the UDS the RTL fetches the max key version from
//              the SW register. Verify that the lock is released when the
//              version register is locked.
rom_error_t sc_keymgr_dpe_load_uds(uint32_t sel_dst_slot) {
  // Set the control register entries
  sc_keymgr_dpe_control_reg_set(
      kScKeymgrDPEUseAdditionalHwBinding,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_LOAD_ROOT_KEY,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, 0, sel_dst_slot);

  // Start the load operation
  sc_keymgr_dpe_start_operation();
  return sc_keymgr_dpe_wait_until_done();
}

/**
 * Executes the first advance call to load the UDS in the selected slot and
 * sets the keymgr_dpe FSM to available.
 */
// TODO(#30667): Verify if the max key version needs to be written here too!
//              When loading the UDS the RTL fetches the max key version from
//              the SW register. Verify that the lock is released when the
//              version register is locked.
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_initial(const uint32_t sel_dst_slot_uds) {
  // Verify the reset state
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateReset));

  // Set the control register entries
  sc_keymgr_dpe_control_reg_set(
      kScKeymgrDPEUseAdditionalHwBinding,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, 0, sel_dst_slot_uds);

  // Start the advance operation
  sc_keymgr_dpe_start_operation();

  // Wait until UDS is loaded
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  // Verify the available state
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));
  return kErrorOk;
}

/**
 * Sets the binding registers / key version registers and advances the
 * UDS into the creator keys (sealing and attestation).
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_creator(
    sc_keymgr_dpe_advance_data_t adv_data_sealing,
    sc_keymgr_dpe_advance_data_t adv_data_attestation) {
  // Sanity checks
  if ((adv_data_sealing.policy.parent != kScKeymgrDPESlotPolEraseParent) ||
      (adv_data_attestation.policy.parent != kScKeymgrDPESlotPolEraseParent)) {
    return kErrorKeymgrInternal;
  }

  // Verify the keymgr_dpe is in the correct FSM state
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));

  // Advance the sealing key chain
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_advance_wrapper(
      kScKeymgrDPEUseAdditionalHwBinding, adv_data_sealing));
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  // Load the UDS into the attestation source slot
  HARDENED_RETURN_IF_ERROR(
      sc_keymgr_dpe_load_uds(adv_data_attestation.sel_src_slot));

  // Advance the attestation key chain
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_advance_wrapper(
      kScKeymgrDPEUseAdditionalHwBinding, adv_data_attestation));
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  return kErrorOk;
}

/**
 * Sets the binding registers / key version registers and advances the
 * creator keys into the owner int keys (sealing and attestation).
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_owner_int(
    sc_keymgr_dpe_advance_data_t adv_data_sealing,
    sc_keymgr_dpe_advance_data_t adv_data_attestation) {
  // Sanity checks
  if ((adv_data_sealing.sel_src_slot != adv_data_sealing.sel_dst_slot) ||
      (adv_data_attestation.sel_src_slot !=
       adv_data_attestation.sel_dst_slot) ||
      (adv_data_sealing.policy.parent != kScKeymgrDPESlotPolEraseParent) ||
      (adv_data_attestation.policy.parent != kScKeymgrDPESlotPolEraseParent)) {
    return kErrorKeymgrInternal;
  }
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));

  // Advance the sealing key
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_advance_wrapper(
      kScKeymgrDPEUseAdditionalHwBinding, adv_data_sealing));
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  // Advance the attestation key
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_advance_wrapper(
      kScKeymgrDPEUseAdditionalHwBinding, adv_data_attestation));
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  return kErrorOk;
}

/**
 * Sets the binding registers / key version registers and advances the
 * owner int keys into the owner keys (sealing and attestation).
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_owner(
    sc_keymgr_dpe_advance_data_t adv_data_sealing,
    sc_keymgr_dpe_advance_data_t adv_data_attestation) {
  // Sanity checks
  if ((adv_data_sealing.sel_src_slot != adv_data_sealing.sel_dst_slot) ||
      (adv_data_attestation.sel_src_slot !=
       adv_data_attestation.sel_dst_slot)) {
    return kErrorKeymgrInternal;
  }
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));

  // Advance the sealing key
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_advance_wrapper(
      kScKeymgrDPEUseAdditionalHwBinding, adv_data_sealing));
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  // Advance the attestation key
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_advance_wrapper(
      kScKeymgrDPEUseAdditionalHwBinding, adv_data_attestation));
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());

  return kErrorOk;
}

/**
 * Erase the DPE context of any slot
 */
rom_error_t sc_keymgr_dpe_erase_slot(uint32_t sel_dst_slot) {
  // Set the control register entries
  sc_keymgr_dpe_control_reg_set(
      kScKeymgrDPEUseAdditionalHwBinding,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ERASE_SLOT,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, 0, sel_dst_slot);

  // Start the advance operation
  sc_keymgr_dpe_start_operation();

  // Wait until the erase operation has finished
  HARDENED_RETURN_IF_ERROR(sc_keymgr_dpe_wait_until_done());
  return kErrorOk;
}

/**
 * Advances the keymgr dpe into the disable state. All keys store in the
 * sideloaded interface are continuously scrambled.
 */
rom_error_t sc_keymgr_dpe_disable(void) {
  // Check if we are in the available state (Stalls until all ops are done)
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateAvailable));

  // Set the control register entries
  sc_keymgr_dpe_control_reg_set(
      kScKeymgrDPEUseExclusiveSwBinding,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_DISABLE,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, 0, 0);

  // Start the advance operation
  sc_keymgr_dpe_start_operation();
  // Wait until keymgr_dpe is finished and verify if state if disabled
  HARDENED_RETURN_IF_ERROR(expected_state_check(kScKeymgrDPEStateDisabled));
  // According to the documentation for the SIDELOAD_CLEAR register, an invalid
  // destination will enable continuous clearing of all destinations.
  abs_mmio_write32(sc_keymgr_dpe_base() + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                   UINT32_MAX);
  return kErrorOk;
}

/**
 * Generate a key manager key and sideload to the OTBN block.
 */
rom_error_t sc_keymgr_dpe_generate_key_otbn(
    sc_keymgr_dpe_diversification_t diversification) {
  return sc_keymgr_dpe_generate_key(kScKeymgrDPEDestOtbn, diversification);
}

/**
 * Clear OTBN's sideloaded key slot.
 */
rom_error_t sc_keymgr_dpe_clear_sideload_key_otbn(void) {
  return sc_keymgr_dpe_clear_key(kScKeymgrDPEDestOtbn);
}
