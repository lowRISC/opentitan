// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/silicon_creator/lib/ownership/keys/fake/no_owner_recovery_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"

const owner_key_t *const kNoOwnerRecoveryKey = &(const owner_key_t){
    .ecdsa = {NO_OWNER_RECOVERY_ECDSA_P256},
};
