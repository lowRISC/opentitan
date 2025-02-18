// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_IMM_ROM_EXT_HASH_ENFORCEMENT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_IMM_ROM_EXT_HASH_ENFORCEMENT_H_

/**
 * Flag when calling an immutable section without enforcing its hash.
 *
 * When the immutable section feature is disabled in OTP, ROM will not invoke
 * the immutable section before jumping to mutable ROM_EXT. During the
 * startup of ROM_EXT, ROM_EXT should invoke its immutable section first, and
 * pass the following constant to the immutable section to indicate that the
 * device is running in unenforced mode.
 *
 * The value below was chosen at random.
 * All other values are considered as ENFORCED.
 */
#define IMMUTABLE_HASH_UNENFORCED 0x9526ecc2

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_IMM_ROM_EXT_HASH_ENFORCEMENT_H_
