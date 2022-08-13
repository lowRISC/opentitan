// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/sigverify_keys_ptrs.h"

extern const sigverify_rom_key_t *sigverify_rsa_keys_ptr_get(void);
extern size_t sigverify_num_rsa_keys_get(void);
extern size_t sigverify_rsa_keys_step_get(void);
