// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_THIRD_PARTY_XOSHIRO_XOSHIRO128PP_H_
#define OPENTITAN_THIRD_PARTY_XOSHIRO_XOSHIRO128PP_H_

#include <stdint.h>

/**
 * Advances the state by one stage and returns a random value.
 *
 * @param s The four-word state.
 * @return a random value.
 */
uint32_t xoshiro128pp_next(uint32_t s[4]);

/**
 * Advances the state by 2^64 stages.
 * 
 * @param s The four-word state.
 */
void xoshiro128pp_jump(uint32_t s[4]);

/**
 * Advances the state by 2^96 stages.
 * 
 * @param s The four-word state.
 */
void xoshiro128pp_long_jump(uint32_t s[4]);

#endif  // OPENTITAN_THIRD_PARTY_XOSHIRO_XOSHIRO128PP_H_
