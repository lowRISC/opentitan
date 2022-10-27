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
  tb.m_core.rand_i = 0x0123456789ABCDEF;
  tb.m_core.rand_aux_i = 0x0;
  tb.m_core.s_i[0] = 0x01234567;
  tb.m_core.s_i[1] = 0x89ABCDEF;
  tb.m_core.s_i[2] = 0x01234567;
  tb.m_core.s_i[3] = 0x89ABCDEF;

  // Control signals
  tb.m_core.rnd_i = 0;  // Round, just defines which round constant is added
                        // at the very end.

  // Phase 1 - Theta, Rho, Pi - Takes 1 cycle.
  tb.m_core.phase_sel_i = 0x5;
  tb.m_core.cycle_i = 0x0;
  tb.tick();
  // Phase 2 - Chi, Iota - Takes 3 cycles.
  tb.m_core.phase_sel_i = 0xA;
  tb.m_core.cycle_i = 0x1;
  tb.tick();
  tb.m_core.phase_sel_i = 0xA;
  tb.m_core.cycle_i = 0x2;
  tb.tick();
  tb.m_core.phase_sel_i = 0xA;
  tb.m_core.cycle_i = 0x3;
  tb.tick();
  // Phase 1 again - Theta, Rho, Pi - Takes 1 cycle.
  tb.m_core.phase_sel_i = 0x5;
  tb.m_core.cycle_i = 0x0;
  tb.tick();
  // Phase 2 - Chi, Iota - Takes 3 cycles.
  tb.m_core.phase_sel_i = 0xA;
  tb.m_core.cycle_i = 0x1;
  tb.tick();
  tb.m_core.phase_sel_i = 0xA;
  tb.m_core.cycle_i = 0x2;
  tb.tick();
  tb.m_core.phase_sel_i = 0xA;
  tb.m_core.cycle_i = 0x3;
  tb.tick();

  tb.closetrace();
}
