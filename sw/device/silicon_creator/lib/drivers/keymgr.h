// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Key Manager states.
 */
typedef enum sc_keymgr_state {
  /**
   * Key manager control is still in reset. Please wait for initialization
   * complete before issuing operations
   */
  kScKeymgrStateReset,
  /**
   * Key manager control has finished initialization and will now accept
   * software commands.
   */
  kScKeymgrStateInit,
  /**
   * Key manager control currently contains the creator root key.
   */
  kScKeymgrStateCreatorRootKey,
  /**
   * Key manager control currently contains the owner intermediate key.
   */
  kScKeymgrStateOwnerIntermediateKey,
  /**
   * Key manager control currently contains the owner key.
   */
  kScKeymgrStateOwnerKey,
  /**
   * Key manager currently disabled. Please reset the key manager. Sideload keys
   * are still valid.
   */
  kScKeymgrStateDisabled,
  /**
   * Key manager currently invalid. Please reset the key manager. Sideload keys
   * are no longer valid.
   */
  kScKeymgrStateInvalid,
  /**
   * This is not a state - it is the total number of states.
   */
  kScKeymgrStateNumStates,
} sc_keymgr_state_t;

enum {
  /**
   * Number of 32-bit words for the salt.
   */
  kScKeymgrSaltNumWords = 8,
};

/**
 * Data used to differentiate a generated keymgr key.
 */
typedef struct sc_keymgr_diversification {
  /**
   * Salt value to use for key generation.
   */
  uint32_t salt[kScKeymgrSaltNumWords];
  /**
   * Version for key generation (anti-rollback protection).
   */
  uint32_t version;
} sc_keymgr_diversification_t;

/**
 * Destination for key generation.
 */
typedef enum sc_keymgr_dest {
  kScKeymgrDestNone = 0,
  kScKeymgrDestAes = 1,
  kScKeymgrDestKmac = 2,
  kScKeymgrDestOtbn = 3,
} sc_keymgr_dest_t;

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  sc_keymgr_sw_binding_set();
 *  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet);
 * ```
 */
enum {
  kScKeymgrSecMmioEntropyReseedIntervalSet = 1,
  kScKeymgrSecMmioSwBindingSet = 17,
  kScKeymgrSecMmioCreatorMaxVerSet = 2,
  kScKeymgrSecMmioOwnerIntMaxVerSet = 2,
  kScKeymgrSecMmioOwnerMaxVerSet = 2,
};

/**
 * Sets the key manager software binding inputs.
 *
 * This function also clears and caches the value of the `SW_BINDING_REGWEN`
 * register in the `sec_mmio` expectations table. This register is unlocked
 * after a successful transaction. It is recommended to call
 * `sc_keymgr_sw_binding_unlock_wait()` after initiating a transition to update
 * its value in the `sec_mmio` expectations table.
 *
 * @param binding_value_sealing Software binding for sealing value.
 * @param binding_value_attestation Software binding for attestation value.
 */
void sc_keymgr_sw_binding_set(
    const keymgr_binding_value_t *binding_value_sealing,
    const keymgr_binding_value_t *binding_value_attestation);

/**
 * Blocks until the software binding registers are unlocked.
 *
 * This function can be called after `sc_keymgr_advance_state()` to wait for the
 * software binding registers to become available for writing and to update the
 * cached value of `SW_BINDING_REGWEN` register in the `sec_mmio` expectations
 * table.
 */
void sc_keymgr_sw_binding_unlock_wait(void);

/**
 * Sets the Silicon Creator max key version.
 *
 * @param max_key_ver Maximum key version associated with the Silicon Creator
 * key manager stage.
 */
void sc_keymgr_creator_max_ver_set(uint32_t max_key_ver);

/**
 * Sets the Silicon Owner Intermediate max key version.
 *
 * @param max_key_ver Maximum key version associated with the Silicon Owner
 * Intermediate key manager stage.
 */
void sc_keymgr_owner_int_max_ver_set(uint32_t max_key_ver);

/**
 * Sets the Silicon Owner max key version.
 *
 * @param max_key_ver Maximum key version associated with the Silicon Owner
 * key manager stage.
 */
void sc_keymgr_owner_max_ver_set(uint32_t max_key_ver);

/**
 * Sets the entropy reseed interval of the key manager.
 *
 * @param entropy_reseed_interval Number of key manager cycles before the
 * entropy is reseeded.
 * @return The result of the operation.
 */
void sc_keymgr_entropy_reseed_interval_set(uint16_t entropy_reseed_interval);

/**
 * Advances the state of the key manager.
 *
 * The `sc_keymgr_state_check()` function must be called before this function to
 * ensure the key manager is in the expected state and ready to receive op
 * commands.
 *
 * The caller is responsible for calling the `sc_keymgr_state_check()` at a
 * later time to ensure the advance transition completed without errors.
 *
 * Note: It is recommended to call `sc_keymgr_sw_binding_unlock_wait()` before
 * the secure mmio `sec_mmio_check_values()` function to make sure the value of
 * the `SW_BINDING_REGWEN` register is updated in the secure mmio expectations
 * table.
 */
void sc_keymgr_advance_state(void);

/**
 * Checks the state of the key manager.
 *
 * @param expected_state Expected key manager state.
 * @return `kErrorOk` if the key manager is in `expected_state` and the status
 * is idle or success; otherwise returns `kErrorKeymgrInternal`.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_state_check(sc_keymgr_state_t expected_state);

/**
 * Keymgr output-generate key types (attestation or sealing).
 */
typedef enum sc_keymgr_key_type {
  kScKeymgrKeyTypeAttestation = 0,
  kScKeymgrKeyTypeSealing = 1,
} sc_keymgr_key_type_t;

/**
 * Keymgr ECC key generation descriptor.
 */
typedef struct sc_keymgr_ecc_key {
  /**
   * Keymgr key type, either: attestation or sealing.
   *
   * Attestation keys are derived from keymgr state that changes when ROM_EXT or
   * Owner firmware is updated, while Sealing keys remain stable as long as a
   * device remains under the same ownership and hardware lifecycle state.
   */
  sc_keymgr_key_type_t type;
  /**
   * Index into the kFlashCtrlInfoPageAttestationKeySeeds flash info page that
   * holds a seed for generating the ECC key pair.
   */
  uint32_t keygen_seed_idx;
  /**
   * Pointer to the keymgr diversifier that is used when actuating the keymgr's
   * "output-generate" function to generate another ECC keygen seed that will be
   * sideloaded to OTBN.
   */
  const sc_keymgr_diversification_t *keymgr_diversifier;
  /**
   * Pointer to the keymgr diversifier that is used when actuating the keymgr's
   */
  sc_keymgr_state_t required_keymgr_state;
} sc_keymgr_ecc_key_t;

/**
 * Generate a key manager key and sideload to the requested block.
 *
 * Calls the key manager to sideload a key into the requested hardware block and
 * waits until the operation is complete before returning. Can sideload an
 * attestation or sealing key based on user input.
 *
 * @param destination: Hardware destination for key material.
 * @param key_type Key type: attestation or sealing.
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */

OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_generate_key(sc_keymgr_dest_t destination,
                                   sc_keymgr_key_type_t key_type,
                                   sc_keymgr_diversification_t diversification);

/**
 * Clear the requested sideloaded key slot.
 *
 * The entropy complex needs to be initialized before calling this function, so
 * that keymgr can use it to clear the slot.
 *
 * @param destination: Hardware block to clear key material.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_sideload_clear(sc_keymgr_dest_t destination);

/**
 * Generate a key manager key and sideload to the OTBN block.
 *
 * Calls the key manager to sideload a key into the OTBN hardware block and
 * waits until the operation is complete before returning. Can sideload an
 * attestation or sealing key based on user input.
 *
 * @param key_type Key type: attestation or sealing.
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
inline rom_error_t sc_keymgr_generate_key_otbn(
    sc_keymgr_key_type_t key_type,
    sc_keymgr_diversification_t diversification) {
  return sc_keymgr_generate_key(kScKeymgrDestOtbn, key_type, diversification);
}

/**
 * Clear OTBN's sideloaded key slot.
 *
 * The entropy complex needs to be initialized before calling this function, so
 * that keymgr can use it to clear the slot.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
inline rom_error_t sc_keymgr_sideload_clear_otbn(void) {
  return sc_keymgr_sideload_clear(kScKeymgrDestOtbn);
}

/**
 * Sets the binding registers and advances the keymgr to the
 * `OwnerIntermediateKey` (CDI_0) key stage.
 *
 * Preconditions: keymgr has been initialized and cranked to the
 * `CreatorRootKey` stage.
 *
 * @param attest_binding The attestation binding value to use.
 * @param sealing_binding The sealing binding value to use.
 * @param max_key_version Maximum key version associated with the Silicon Owner
 *                        Intermediate key manager stage.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_owner_int_advance(keymgr_binding_value_t *attest_binding,
                                        keymgr_binding_value_t *sealing_binding,
                                        uint32_t max_key_version);

/**
 * Sets the binding registers and advances the keymgr to the `OwnerKey` (CDI_1)
 * key stage.
 *
 * Preconditions: keymgr has been initialized and cranked to the
 * `OwnerIntermediateKey` stage.
 *
 * @param attest_binding The attestation binding value to use.
 * @param sealing_binding The sealing binding value to use.
 * @param max_key_version Maximum key version associated with the Silicon Owner
 *                        key manager stage.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sc_keymgr_owner_advance(keymgr_binding_value_t *attest_binding,
                                    keymgr_binding_value_t *sealing_binding,
                                    uint32_t max_key_version);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_KEYMGR_H_
