// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/silicon_creator/lib/ownership/keys/fake/ownership_no_owner_recovery_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/owner_keys.h"

const owner_key_t *const kOwnershipNoOwnerRecoveryKey = &(const owner_key_t){
    .key = OWNERSHIP_NO_OWNER_RECOVERY_ECDSA_P256,
};

// TODO(cfrantz): Add these fake keys for testing
// const owner_key_t *kOwnershipFakeOwnerKey;
// const owner_key_t *kOwnershipFakeActivateKey;
// const owner_key_t *kOwnershipFakeUnlockKey;
