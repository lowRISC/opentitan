// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// NOTE: This is the only header from OpenTitan that can be imported here. Any
// OpenTitan-specific work should be done in support.c, instead.
// Doing this avoids having to create patches for this file any time
// requirements for the wrapper change.
#include "sw/device/riscv_compliance_support/support.h"

int main(int argc, char **argv) {
  return opentitan_compliance_main(argc, argv);
}
