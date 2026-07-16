// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_DPE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_DPE_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_dpe_binding_value.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Key Manager states.
 */
typedef enum sc_keymgr_dpe_state {
  /**
   * Key manager dpe control is still in reset. Please wait for initialization
   * complete before issuing operations
   */
  kScKeymgrDPEStateReset,
  /**
   * Key manager control has finished latching OTP root key and will
   * now accept software commands.
   */
  kScKeymgrDPEStateAvailable,
  /**
   * Key manager dpe currently disabled. Please reset the key manager. Sideload
   * keys are still valid.
   */
  kScKeymgrDPEStateDisabled,
  /**
   * Key manager dpe currently invalid. Please reset the key manager. Sideload
   * keys are no longer valid.
   */
  kScKeymgrDPEStateInvalid,
  /**
   * This is not a state - it is the total number of states.
   */
  kScKeymgrDPEStateNumStates,
} sc_keymgr_dpe_state_t;

/**
 * Option to exclude the hw bindings values when deriving a DPE context
 * (only applicable when deriving either a first, second or third generation
 * DPE context in respect to the UDS).
 */
typedef enum sc_keymgr_dpe_sw_binding {
  kScKeymgrDPEUseAdditionalHwBinding = 0,
  kScKeymgrDPEUseExclusiveSwBinding = 1,
} sc_keymgr_dpe_sw_binding_t;

/**
 * Set whether further advance operations should overwrite the source slot.
 */
typedef enum sc_keymgr_dpe_policy_parent {
  kScKeymgrDPESlotPolRetainParent = 1,
  kScKeymgrDPESlotPolEraseParent = 0,
} sc_keymgr_dpe_policy_parent_t;

/**
 * Set whether the key for the target slot is exportable.
 * Currently the export function is not implemented in RTL (Issue #30612)!
 */
typedef enum sc_keymgr_dpe_policy_export {
  kScKeymgrDPESlotPolAllowExport = 1,
  kScKeymgrDPESlotPolNoExport = 0,
} sc_keymgr_dpe_policy_export_t;

/**
 * Set whether this DPE context allows to derive further DPE context.
 */
typedef enum sc_keymgr_dpe_policy_children {
  kScKeymgrDPESlotPolAllowChild = 1,
  kScKeymgrDPESlotPolNoChild = 0,
} sc_keymgr_dpe_policy_children_t;

/**
 * Merges the three policies into a single struct.
 */
typedef struct sc_keymgr_dpe_policies {
  sc_keymgr_dpe_policy_parent_t parent;
  sc_keymgr_dpe_policy_children_t child;
  sc_keymgr_dpe_policy_export_t expo;
} sc_keymgr_dpe_policies_t;

enum {
  /**
   * Number of 32-bit words for the salt.
   */
  kScKeymgrDPESaltNumWords = 8,
  /**
   * Number of 32-bit words for the key
   */
  kScKeymgrDPEKeyNumWords = 8,
};

/**
 * Data used to differentiate a generated keymgr key.
 */
typedef struct sc_keymgr_dpe_diversification {
  /**
   * Salt value to use for key generation.
   */
  uint32_t salt[kScKeymgrDPESaltNumWords];
  /**
   * The source slot to be used as parent DPE context.
   */
  uint32_t sel_src_slot;
  /**
   * Version for key generation (anti-rollback protection).
   */
  uint32_t version;
} sc_keymgr_dpe_diversification_t;

/**
 * Data used to advance the state of one DPE context
 */
typedef struct sc_keymgr_dpe_advance_data {
  /**
   * Binding values for the advance call.
   */
  keymgr_dpe_binding_value_t *binding_value;
  /**
   * Policy for the newly created DPE context.
   */
  sc_keymgr_dpe_policies_t policy;
  /**
   * The source slot to be used as parent DPE context.
   */
  uint32_t sel_src_slot;
  /**
   * The destination slot for the derived DPE context.
   */
  uint32_t sel_dst_slot;
  /**
   * Max version for key generation (anti-rollback protection).
   */
  uint32_t version;
} sc_keymgr_dpe_advance_data_t;

/**
 * Destination for key generation.
 */
typedef enum sc_keymgr_dpe_dest {
  kScKeymgrDPEDestNone = 0,
  kScKeymgrDPEDestAes = 1,
  kScKeymgrDPEDestKmac = 2,
  kScKeymgrDPEDestOtbn = 3,
} sc_keymgr_dpe_dest_t;

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  sc_keymgr_sw_binding_set();
 *  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet);
 * ```
 */
enum {
  kScKeymgrDPESecMmioReseedIntervalSet = 1,
  kScKeymgrDPESecMmioSwBindingSet = 8,
  kScKeymgrDPESecMmioMaxVerSet = 1,
  kScKeymgrDPESecMmioSlotPolicy = 1,
};

/**
 * Keymgr DPE ECC key generation descriptor.
 *
 * The attestation or sealing key chain is directly mapped towards one of the
 * keymgr_dpe slots thus removing the need to differentiate between the two
 * of them.
 *
 * Attestation keys are derived from the system state, which changes when the
 * ROM_EXT or the owner firmware is updated. Sealing keys remain stable as
 * long as the device remains under the same ownership and hardware lifecycle
 * state.
 */
typedef struct sc_keymgr_dpe_ecc_key {
  /**
   * Index into the kFlashCtrlInfoPageAttestationKeySeeds flash info page that
   * holds a seed for generating the ECC key pair.
   */
  uint32_t keygen_seed_idx;
  /**
   * Pointer to the keymgr dpe diversifier that is used when actuating the
   * keymgr's "output-generate" function to generate another ECC keygen seed
   * that will be sideloaded to OTBN.
   */
  const sc_keymgr_dpe_diversification_t *keymgr_dpe_diversifier;
  /**
   * Currently there is no way to control if the correct key was already
   * generated inside of keymgr_dpe slot. The program execution flow has to
   * guarantee the correct DPE context!
   */
  sc_keymgr_dpe_state_t required_keymgr_dpe_state;
} sc_keymgr_dpe_ecc_key_t;

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
rom_error_t sc_keymgr_dpe_wait_until_done(void);

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
    uint32_t sel_dst_slot);

/**
 * Start the pre-programmed operation.
 */
void sc_keymgr_dpe_start_operation(void);

/**
 * Sets the entropy reseed interval of the key manager dpe.
 *
 * @param reseed_interval Number of key manager dpe cycles before the
 * entropy is reseeded.
 */
void sc_keymgr_dpe_entropy_reseed_interval_set(uint16_t reseed_interval);

/**
 * Sets the key manager dpe software binding input.
 *
 * This function also clears and caches the value of the `SW_BINDING_REGWEN`
 * register in the `sec_mmio` expectations table. This register is unlocked
 * after a successful transaction. It is recommended to call
 * `sc_keymgr_dpe_sw_binding_unlock_wait()` after initiating a transition
 * to update its value in the `sec_mmio` expectations table.
 *
 * @param binding_value Software binding value
 */
void sc_keymgr_dpe_sw_binding_set(keymgr_dpe_binding_value_t *binding_value);

/**
 * Blocks until the software binding registers are unlocked.
 *
 * This function can be called after `sc_keymgr_dpe_advance_state()` to wait
 * for the software binding registers to become available for writing and to
 * update the cached value of `SW_BINDING_REGWEN` register in the `sec_mmio`
 * expectations table.
 */
void sc_keymgr_dpe_sw_binding_unlock_wait(void);

/**
 * Sets the current max key version used to advance a DPE context
 *
 * This function sets the current max key version. The subfield
 * max_key_version of each hardware slot is populated with this value
 * during an advance call which target the corresponding slot.
 *
 * @param max_key_ver Maximum key version
 */
void sc_keymgr_dpe_max_ver_set(uint32_t max_key_ver);

/**
 * Sets the key version used to generate a key
 *
 * This version is compared against the max version stores in the subfield of
 * the source slot. Only if this version is smaller or equal to the max version
 * the key is generated.
 *
 * @param key_ver key version
 */
void sc_keymgr_dpe_key_ver_set(uint32_t key_ver);

/**
 * Sets all the slot policies for the next advance call.
 *
 * @param policy combined policy vector for the next advance call
 */
void sc_keymgr_dpe_policy_set(sc_keymgr_dpe_policies_t policy);

/**
 * Checks the state of the key manager and compares against the provided
 * value.
 *
 * @param expected_state Expected key manager dpe state.
 * @return `kErrorOk` if the key manager dpe is in `expected_state` and the
 * status is idle or success; otherwise returns `kErrorKeymgrInternal`.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_state_check(sc_keymgr_dpe_state_t expected_state);

/**
 * Generate a key manager dpe key and sideload to the requested block.
 *
 * Calls the key manager dpe to sideload a key into the requested hardware block
 * and waits until the operation is complete before returning.
 *
 * @param destination: Hardware destination for key material.
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_generate_key(
    const sc_keymgr_dpe_dest_t destination,
    sc_keymgr_dpe_diversification_t diversification);

/**
 * Read the generated sw key.
 *
 * The caller ensure the pointer have sufficient space for the full
 * key in each share and that a key was successfully generated first.
 *
 * @param share0 Pointer to store the first share of the generated key with
 * the required size defined in kScKeymgrDPEKeyNumWords.
 * @param share1 Pointer to store the second share of the generated key with
 * the required size defined in kScKeymgrDPEKeyNumWords.
 * @return OK or kErrorKeymgrInternal if keymgr_dpe is not idle
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_read_key(uint32_t *share0, uint32_t *share1);

/**
 * Clear the requested sideloaded key slot.
 *
 * The entropy complex needs to be initialized before calling this function, so
 * that keymgr dpe can use it to clear the slot.
 *
 * @param destination: Hardware block to clear key material
 * @return OK or kErrorKeymgrInternal if keymgr_dpe is not idle
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_clear_key(sc_keymgr_dpe_dest_t destination);

/**
 * Advances the DPE context of one slot inside the keymgr_dpe
 *
 * This function can only be called if the targeted key_slot has already
 * advanced three times. If the function is called sooner it will generate
 * not valid keys and the boot process is corrupted. The function stalls at
 * the start if the keymgr dpe is not idle.
 *
 * The caller must ensure that this function finish successfully by calling
 * `sc_keymgr_dpe_wait_until_done()`.
 *
 * @param adv_data All required data to advance the key of one DPE Context.
 * @return The result of the advance call.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_dpe_context(
    sc_keymgr_dpe_advance_data_t adv_data);

/**
 * Locks the load uds operation until the next reset
 *
 * When this function is called then the function "sc_keymgr_dpe_load_uds" will
 * generate an error as the uds is locked. This lock can only be released by
 * resetting the device.
 *
 * @return kErrorOk if the operation finished with "done_successfully",
 * kErrorKeymgrInternal otherwise.
 *
 */
rom_error_t sc_keymgr_dpe_lock_uds(void);

/**
 * Load the UDS into an empty hw slot
 *
 * Load the UDS into the selected hw slot. If the selected hw slot is not
 * empty then the keymgr_dpe will through an error.
 *
 * @param sel_dst_slot empty destination slot for the UDS
 * @return kErrorOk
 */
rom_error_t sc_keymgr_dpe_load_uds(uint32_t sel_dst_slot);

/**
 * Executes the first advance call to load the UDS in the selected slot and
 * sets the keymgr_dpe FSM to available.
 *
 * Precondition: keymgr_dpe has to be in the state kScKeymgrDPEStateReset
 *
 * @param sel_dst_slot DPE context slot for the UDS
 * @return The result of the advance call.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_initial(const uint32_t sel_dst_slot_uds);

/**
 * Sets the binding registers / key version registers and advances the
 * UDS into the creator keys (sealing and attestation).
 *
 * First the sealing key is generated from the preloaded UDS while the UDS
 * is manually loaded a second time to generated the attestation key.
 * Additionally the retain parent policy bit must be cleared to avoid leaving
 * the creator keys existing beyond its designated boot stage. This
 * function is blocking until the advance operation was successfully.
 *
 * Precondition: keymgr_dpe has to be in the state kScKeymgrDPEStateAvailable
 *
 * @param adv_data_sealing All required data to advance the UDS into the
 * sealing owner key.
 * @param adv_data_attestation All required data to advance the UDS into the
 * attestation owner key.
 * @return The result of the advance call.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_creator(
    sc_keymgr_dpe_advance_data_t adv_data_sealing,
    sc_keymgr_dpe_advance_data_t adv_data_attestation);

/**
 * Sets the binding registers / key version registers and advances the
 * creator keys into the owner int keys (sealing and attestation).
 *
 * The retain parent policy bit must be cleared to avoid leaving the owner int
 * keys existing beyond its designated boot stage. Due to the retain parent
 * policy on the creator keys the source and destination slot have to be equal.
 * This function is blocking until the advance operation was successfully.
 *
 * Precondition: keymgr_dpe has to be in the state kScKeymgrDPEStateAvailable
 *
 * @param adv_data_sealing All required data for the sealing key
 * @param adv_data_attestation All required data for the attestation key
 * @return The result of the advance call.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_owner_int(
    sc_keymgr_dpe_advance_data_t adv_data_sealing,
    sc_keymgr_dpe_advance_data_t adv_data_attestation);

/**
 * Sets the binding registers / key version registers and advances the
 * owner int keys into the owner keys (sealing and attestation).
 *
 * Due to the retain parent policy on the owner int the source and
 * destination slot have to be equal. This function is blocking until the
 * advance operation was successfully.
 *
 * Precondition: keymgr_dpe has to be in the state kScKeymgrDPEStateAvailable
 *
 * @param adv_data_sealing All required data for the sealing key
 * @param adv_data_attestation All required data for the attestation key
 * @return The result of the advance call.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_dpe_advance_owner(
    sc_keymgr_dpe_advance_data_t adv_data_sealing,
    sc_keymgr_dpe_advance_data_t adv_data_attestation);

/**
 * Erase the DPE context of any slot
 *
 * This function is blocking until the advance operation was successfully.
 *
 * @param sel_dst_slot selected DPE context to erase
 * @return The result of the erase call.
 */
rom_error_t sc_keymgr_dpe_erase_slot(uint32_t sel_dst_slot);

/**
 * Advances the keymgr dpe into the disable state.
 *
 * All keys store in the sideloaded interface are continuously scrambled.
 *
 * @return OK or error.
 */
rom_error_t sc_keymgr_dpe_disable(void);

/**
 * Generate a key manager key and sideload to the OTBN block.
 *
 * Calls the key manager to sideload a key into the OTBN hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
rom_error_t sc_keymgr_dpe_generate_key_otbn(
    sc_keymgr_dpe_diversification_t diversification);

/**
 * Clear OTBN's sideloaded key slot.
 *
 * The entropy complex needs to be initialized before calling this function, so
 * that keymgr dpe can use it to clear the slot.
 *
 * @return OK or error.
 */
rom_error_t sc_keymgr_dpe_clear_sideload_key_otbn(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_DPE_H_
