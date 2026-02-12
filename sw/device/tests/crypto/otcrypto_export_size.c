// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/otcrypto_interface.h"

// Simple main function so the linker doesn't discard the inerface struct.
void bare_metal_main(void) { (void)otcrypto; }
