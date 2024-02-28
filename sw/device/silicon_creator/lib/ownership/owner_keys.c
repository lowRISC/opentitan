// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/owner_keys.h"

#include "sw/device/lib/base/macros.h"

OT_WEAK const owner_key_t *const kOwnershipNoOwnerRecoveryKey;

OT_WEAK const owner_key_t *const kOwnershipFakeOwnerKey;
OT_WEAK const owner_key_t *const kOwnershipFakeActivateKey;
OT_WEAK const owner_key_t *const kOwnershipFakeUnlockKey;
