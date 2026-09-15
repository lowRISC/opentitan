// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KEYMGR_DPE_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KEYMGR_DPE_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Number of 32-bit words for the salt.
   */
  kKeymgrDPESaltNumWords = 8,
  /**
   * Number of 32-bit words for each output key share.
   */
  kKeymgrDPEOutputShareNumWords = 8,
};

/**
 * Data used to differentiate a generated keymgr dpe key.
 */
typedef struct keymgr_dpe_diversification {
  /**
   * Salt value to use for key generation.
   */
  uint32_t salt[kKeymgrDPESaltNumWords];
  /**
   * The source slot to be used as parent DPE context.
   */
  uint32_t slot_src_sel;
  /**
   * Version for key generation (anti-rollback protection).
   */
  uint32_t version;
} keymgr_dpe_diversification_t;

/**
 * Generated key from keymgr dpe.
 *
 * The output key material is 256 bits, generated in two shares.
 */
typedef struct keymgr_dpe_output {
  uint32_t share0[kKeymgrDPEOutputShareNumWords];
  uint32_t share1[kKeymgrDPEOutputShareNumWords];
} keymgr_dpe_output_t;

/**
 * Policy bits associated with the DPE context held in one HW slot.
 */
typedef struct keymgr_dpe_policy {
  /**
   * Set if this DPE context allows deriving further DPE contexts.
   */
  bool allow_child;
  /**
   * Set if the key for this slot is exportable.
   */
  bool exportable;
  /**
   * Set if further advance operations retain (do not erase) this slot.
   */
  bool retain_parent;
} keymgr_dpe_policy_t;

/**
 * Boot stage associated with a DPE context.
 * Mirrors `keymgr_dpe_boot_stage_e` in keymgr_dpe_pkg.sv.
 */
typedef enum keymgr_dpe_boot_stage {
  kKeymgrDPEBootStageCreator = 0,
  kKeymgrDPEBootStageOwnerInt = 1,
  kKeymgrDPEBootStageOwner = 2,
  kKeymgrDPEBootStageRuntime = 3,
} keymgr_dpe_boot_stage_t;

/**
 * Output metadata from one HW slot.
 */
typedef struct keymgr_dpe_metadata {
  /**
   * Maximum allowed version for keys to be generated from this DPE context.
   */
  uint32_t max_key_version;
  /**
   * The current boot_stage of this DPE context.
   */
  keymgr_dpe_boot_stage_t boot_stage;
  /**
   * The current slot policy bits for this DPE context.
   */
  keymgr_dpe_policy_t slot_policy;
  /**
   * Validity of this DPE context.
   */
  bool valid;
} keymgr_dpe_metadata_t;

/**
 * Derive a key manager dpe key that is visible to software.
 *
 * @param diversification Diversification input for the key derivation.
 * @param[out] key Destination key struct.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_generate_key_sw(
    const keymgr_dpe_diversification_t diversification,
    keymgr_dpe_output_t *key);

/**
 * Derive a key manager dpe key for the AES block.
 *
 * Calls the key manager dpe to sideload a key into the AES hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_generate_key_aes(
    keymgr_dpe_diversification_t diversification);

/**
 * Derive a key manager dpe key for the KMAC block.
 *
 * Calls the key manager dpe to sideload a key into the KMAC hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_generate_key_kmac(
    keymgr_dpe_diversification_t diversification);

/**
 * Derive a key manager dpe key for the OTBN block.
 *
 * Calls the key manager dpe to sideload a key into the OTBN hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_generate_key_otbn(
    keymgr_dpe_diversification_t diversification);

/**
 * Clear the sideloaded AES key.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_sideload_clear_aes(void);

/**
 * Clear the sideloaded KMAC key.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_sideload_clear_kmac(void);

/**
 * Clear the sideloaded OTBN key.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_sideload_clear_otbn(void);

/**
 * Reads back the metadata of a keymgr_dpe HW slot.
 *
 * @param slot Index of the HW slot to read metadata from.
 * @param[out] metadata Out-param for the slot's metadata.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_dpe_get_metadata(uint32_t slot,
                                 keymgr_dpe_metadata_t *metadata);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KEYMGR_DPE_H_
