// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"

TOPLEVEL_NAME &VerilatedToplevel::dut() {
  // The static_cast below is generally unsafe, but we know the types involved.
  // It's safe for these.
  TOPLEVEL_NAME &dut = static_cast<TOPLEVEL_NAME &>(*this);
  return dut;
}
