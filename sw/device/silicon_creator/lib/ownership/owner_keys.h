// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_KEYS_H_

#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

/**
 * The OwnershipNoOwnerRecoveryKey is a silicon_creator key that allows
 * recovery of a device should it get into the LockedNone state (ie:
 * a state where there is no valid owner).
 */
extern const owner_key_t *const kOwnershipNoOwnerRecoveryKey;

/**
 * The Fake Owner/Activate/Unlock keys are used for pre-initializing the
 * owner pages for testing (FPGA) rom_exts.  This pre-initialization allows
 * us to avoid a chicken-and-egg problem when running on an FPGA plaftform
 * without an owner already provisioned.
 */
extern const owner_key_t *const kOwnershipFakeOwnerKey;
extern const owner_key_t *const kOwnershipFakeActivateKey;
extern const owner_key_t *const kOwnershipFakeUnlockKey;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_OWNER_KEYS_H_
