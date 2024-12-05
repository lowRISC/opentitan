// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_KEYS_H_

#include "sw/device/silicon_creator/lib/drivers/keymgr.h"

extern const sc_keymgr_ecc_key_t kDiceKeyUds;
extern const sc_keymgr_ecc_key_t kDiceKeyCdi0;
extern const sc_keymgr_ecc_key_t kDiceKeyCdi1;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_KEYS_H_
