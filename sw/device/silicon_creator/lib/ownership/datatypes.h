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
  /* Unlocked None: `NONE`. */
  kOwnershipStateUnlockedNone = 0x454e4f4e,
  /* Locked None: any bit pattern not listed above. */
  kOwnershipStateLockedNone = 0,
} ownership_state_t;

typedef struct tlv_header {
  uint32_t tag;
  uint32_t length;
} tlv_header_t;

typedef enum owner_sram_exec_mode {
  kOwnerSramExecModeDisabledLocked = 0,
  kOwnerSramExecModeDisabled = 1,
  kOwnerSramExecModeEnabled = 2,
} owner_sram_exec_mode_t;

typedef struct owner_block {
  tlv_header_t header;
  uint32_t version;
  uint32_t sram_exec_mode;
  uint32_t reserved[4];
  owner_key_t owner_key;
  owner_key_t activate_key;
  owner_key_t unlock_key;
  uint8_t data[1728];
  owner_signature_t signature;
  uint32_t seal[8];
} owner_block_t;

OT_ASSERT_MEMBER_OFFSET(owner_block_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, version, 8);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, sram_exec_mode, 12);
OT_ASSERT_MEMBER_OFFSET(owner_block_t, reserved, 16);
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
