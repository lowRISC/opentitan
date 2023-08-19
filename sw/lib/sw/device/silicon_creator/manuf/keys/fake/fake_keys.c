// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/silicon_creator/manuf/keys/fake/rma_unlock_token_export_key.pk_hsm.h"

const ecc_public_key_t kRmaUnlockTokenExportKeyPkHsm =
    RMA_UNLOCK_TOKEN_EXPORT_KEY_PK_HSM;
