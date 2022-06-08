// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_THIRD_PARTY_XOSHIRO_SPLITMIX64_H_
#define OPENTITAN_THIRD_PARTY_XOSHIRO_SPLITMIX64_H_

#include <stdint.h>

/**
 * Advances the state by one stage and returns a random value.
 * 
 * @param x the input state.
 * @return a random value.
 */
uint64_t splitmix64_next(uint64_t *x);

#endif  // OPENTITAN_THIRD_PARTY_XOSHIRO_SPLITMIX64_H_
