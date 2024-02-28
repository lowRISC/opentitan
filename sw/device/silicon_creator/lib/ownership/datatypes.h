// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_DATATYPES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_DATATYPES_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * An owner_key can be either a ECDSA P256 or SPX+ key.  The type of the key
 * material will be determined by a separate field on the owner block
 */
typedef struct owner_key {
  uint32_t key[16];
} owner_key_t;

/**
 * An owner_signature is an ECDSA P256 signature.
 */
typedef struct owner_signature {
  uint32_t signature[16];
} owner_signature_t;

typedef enum ownership_state {
  /* Locked Owner: `OWND`. */
  kOwnershipStateLockedOwner = 0x444e574f,
  /* Locked Update: `LUPD`. */
  kOwnershipStateLockedUpdate = 0x4450554c,
  /* Unlocked Any: `UANY`. */
  kOwnershipStateUnlockedAny = 0x594e4155,
  /* Unlocked Endorsed: `UEND`. */
  kOwnershipStateUnlockedEndorsed = 0x444e4555,
  /* Locked None: any bit pattern not listed above. */
  kOwnershipStateLockedNone = 0,
} ownership_state_t;

typedef struct tlv_header {
  uint32_t tag;
  uint32_t length;
} tlv_header_t;

typedef enum owner_sram_exec_mode {
  /** SRAM Exec disabled and locked: `LNEX`. */
  kOwnerSramExecModeDisabledLocked = 0x58454e4c,
  /** SRAM Exec disabled: `NOEX`. */
  kOwnerSramExecModeDisabled = 0x58454f4e,
  /** SRAM Exec enabled: `EXEC` */
  kOwnerSramExecModeEnabled = 0x43455845,
} owner_sram_exec_mode_t;

/**
 * The owner configuration block describes an owner identity and configuration.
 */
typedef struct owner_block {
  /**
   * Header identifying this struct.
   * tag: `OWNR`.
   * length: 2048.
   */
  tlv_header_t header;
  /** Version of the owner struct.  Currently `0`. */
  uint32_t version;
  /** SRAM execution configuration (DisabledLocked, Disabled, Enabled). */
  uint32_t sram_exec_mode;
  /** Ownership key algorithm (currently, only ECDSA is supported). */
  uint32_t ownership_key_alg;
  /** Reserved space for future use. */
  uint32_t reserved[3];
  /** Owner public key. */
  owner_key_t owner_key;
  /** Owner's Activate public key. */
  owner_key_t activate_key;
  /** Owner's Unlock public key. */
  owner_key_t unlock_key;
  /** Data region to hold the other configuration structs. */
  uint8_t data[1728];
  /** Signature over the owner block with the Owner private key. */
  owner_signature_t signature;
  /** A sealing value to seal the owner block to a specific chip. */
  uint32_t seal[8];
} owner_block_t;

OT_ASSERT_MEMBER_OFFSET(owner_block_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, version, 8);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, sram_exec_mode, 12);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, ownership_key_alg, 16);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, reserved, 20);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, owner_key, 32);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, activate_key, 96);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, unlock_key, 160);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, data, 224);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, signature, 1952);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, seal, 2016);
OT_ASSERT_SIZE(owner_block_t, 2048);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_DATATYPES_H_
