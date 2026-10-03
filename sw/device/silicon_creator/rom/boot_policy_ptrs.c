// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/boot_policy_ptrs.h"

extern const manifest_t *boot_policy_manifest_a_load(void);
extern const manifest_t *boot_policy_manifest_b_load(void);
extern void boot_policy_manifest_a_unload(void);
extern void boot_policy_manifest_b_unload(void);
