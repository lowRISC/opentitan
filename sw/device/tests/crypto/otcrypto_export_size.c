// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/otcrypto_interface.h"

// Only here for coverage reporting.
// Satisfy bare_metal_start.S so the linker doesn't crash.
// These don't need to actually initialize RAM.
void crt_section_copy(void) {}
void crt_section_clear(void) {}

// Simple main function so the linker doesn't discard the inerface struct.
void bare_metal_main(void) { (void)otcrypto; }
