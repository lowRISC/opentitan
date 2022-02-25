// Copyright lowRISC contributors.
// Copyright IAIK.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>

#include "Vcircuit.h"
#include "testbench.h"

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Testbench<Vcircuit> tb;
  tb.opentrace("tmp.vcd");

  tb.reset();

  // Data signals - we don't really care about the data fed to the module.
  // The whole tracing is really just about control signals.
  tb.m_core.rand_i = 0x123456;
  tb.m_core.s_i = 0x789ABCDE;

  // Control signals
  tb.m_core.rnd_i = 0;  // Round, just defines which round constant is added
                        // at the very end.
  tb.m_core.rand_valid_i = 1;  // Randomness always valid. TODO experiment with
                               // stalls to test muxing.

  // Phase 1 - Theta, Rho, Pi - Takes 1 cycle.
  tb.m_core.sel_i = 0x5;
  tb.tick();
  // Phase 2 - Chi, Iota - Takes 2 cycles.
  tb.m_core.sel_i = 0xA;
  tb.tick();
  tb.tick();

  tb.closetrace();
}
