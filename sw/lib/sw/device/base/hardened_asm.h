// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_ASM_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_ASM_H_

/**
 * Values for a hardened boolean type.
 *
 * The intention is that this is used instead of `<stdbool.h>`'s #bool, where a
 * higher hamming distance is required between the truthy and the falsey value.
 *
 * The values below were chosen at random, with some specific restrictions. They
 * have a Hamming Distance of 8, and they are 11-bit values so they can be
 * materialized with a single instruction on RISC-V. They are also specifically
 * not the complement of each other.
 */
#define HARDENED_BOOL_TRUE 0x739
#define HARDENED_BOOL_FALSE 0x1d4

/**
 * Values for a byte-sized hardened boolean.
 *
 * This type is intended for cases where a byte-sized hardened boolean is
 * required, e.g. for the entries of the `CREATOR_SW_CFG_SIGVERIFY_RSA_KEY_EN`
 * OTP item.
 *
 * The values below were chosen to ensure that the hamming difference between
 * them is greater than 5 and they are not bitwise complements of each other.
 */
#define HARDENED_BYTE_BOOL_TRUE 0xa5
#define HARDENED_BYTE_BOOL_FALSE 0x4b

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_HARDENED_ASM_H_
